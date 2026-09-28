#include <algorithms/base.hh>
#include <query/expressions.hh>
#include <query/query.hh>
#include <query/trace.hh>
#include <set>
namespace query {
    namespace {
        struct Constraint {
            compiler::Unit unit;
            unsigned time;
            Json::Value metadata;
        };
        void require(bool value, const std::string& message)
        {
            if (!value) throw std::invalid_argument(message);
        }
        Json::Value metadata(const std::string& id, const std::string& kind, unsigned time, const compiler::Unit& unit)
        {
            Json::Value v;
            v["id"] = id;
            v["kind"] = kind;
            v["step"] = time;
            v["expression"] = source::print(unit.expr());
            v["source_ids"] = Json::arrayValue;
            for (const auto& source_id : unit.source_ids)
                v["source_ids"].append(source_id);
            return v;
        }
        void append(std::vector<Constraint>& constraints, const compiler::Units& units, const std::string& kind, unsigned time)
        {
            for (const auto& unit : units) {
                const auto id = unit.source_ids.at(0) + ":t" + std::to_string(time);
                constraints.push_back({ unit, time, metadata(id, kind, time, unit) });
            }
        }
        expr::Expr_ptr domain(expr::Expr_ptr key, type::Type_ptr type)
        {
            auto& em = expr::ExprMgr::INSTANCE();
            auto result = em.make_true();
            if (type->is_enum()) {
                result = em.make_false();
                for (auto literal : type->as_enum()->literals())
                    result = em.make_or(result, em.make_eq(key, literal));
            } else if (type->is_array()) {
                for (unsigned i = 0; i < type->as_array()->nelems(); ++i)
                    result = em.make_and(result, domain(em.make_subscript(key, em.make_const(i)), type->as_array()->of()));
            }
            return result;
        }
        // Domains, widths, input substitution and frozen-variable identity stay fixed.
        void background(algorithms::Algorithm& a, sat::Engine& engine, unsigned depth)
        {
            auto& em = expr::ExprMgr::INSTANCE();
            symb::SymbIter it(a.model());
            while (it.has_next()) {
                auto [scope, symbol] = it.next();
                if (!symbol->is_variable() || symbol->as_variable().type()->is_instance()) continue;
                auto& variable = symbol->as_variable();
                auto expression = domain(symbol->name(), variable.type());
                if (expression == em.make_true()) continue;
                auto unit = a.compiler().process(scope, expression);
                for (unsigned k = 0; k <= depth; ++k)
                    engine.push(unit, k);
            }
        }
        void activate(sat::Engine& engine, const std::set<int>& enabled)
        {
            auto& groups = engine.groups();
            for (size_t i = 1; i < groups.size(); ++i) {
                const auto id = std::abs(groups[i]);
                groups[i] = enabled.count(id) ? id : -id;
            }
        }
        Json::Value solve_case(const QuerySpec& spec, algorithms::Algorithm& a, const std::vector<Constraint>& constraints,
                               unsigned depth, QueryContext& context, bool& feasible)
        {
            sat::Engine engine("explanation");
            background(a, engine, depth);
            std::map<int, Json::Value> entries;
            std::set<int> enabled;
            std::set<std::string> selected;
            const bool filtered = spec.explanation.isMember("active_ids");
            if (filtered)
                for (const auto& id : spec.explanation["active_ids"])
                    selected.insert(id.asString());
            for (const auto& constraint : constraints) {
                checkpoint(Phase::encoding);
                const auto group = engine.new_group();
                // Every unit emits its entire definition under its own selector.
                // Shared compiler temporaries remain defined by every enabled use.
                engine.push(constraint.unit, constraint.time, group);
                entries[group] = constraint.metadata;
                if (!filtered || selected.erase(constraint.metadata["id"].asString())) enabled.insert(group);
            }
            require(selected.empty(), "Unknown constraint ID in subset recheck");
            activate(engine, enabled);
            auto status = engine.solve();
            if (status == sat::STATUS_UNKNOWN) throw Cancelled();
            feasible = status == sat::STATUS_SAT;
            if (feasible) return Json::Value();
            std::set<int> core;
            for (auto group : engine.failed_groups())
                if (enabled.count(group)) core.insert(group);
            // Verify the adapter's failed assumptions before publishing any core.
            activate(engine, core);
            status = engine.solve();
            if (status == sat::STATUS_UNKNOWN) throw Cancelled();
            if (status != sat::STATUS_UNSAT) throw std::runtime_error("Failed-assumption core did not reproduce UNSAT");
            bool minimal = false;
            unsigned checks = 0;
            std::string stop = "not_requested";
            if (spec.explanation.get("minimize", false).asBool()) {
                const unsigned limit = spec.explanation.get("checks", 100).asUInt();
                QueryLimits limits;
                limits.wall_ms = spec.explanation.get("wall_ms", 1000).asInt64();
                if (context.limits.conflicts >= 0) limits.conflicts = std::max<int64_t>(0, context.limits.conflicts - context.conflicts_used);
                if (context.limits.propagations >= 0) limits.propagations = std::max<int64_t>(0, context.limits.propagations - context.propagations_used);
                // Shrinking has a separate wall/check budget; the outer job can still cancel it.
                QueryContext shrinking(limits);
                {
                    ContextScope scope(shrinking);
                    shrinking.attach(&engine);
                    stop = "complete";
                    try {
                        const auto candidates = core;
                        for (auto group : candidates) {
                            if (checks >= limit) {
                                stop = "check_limit";
                                break;
                            }
                            shrinking.check(Phase::solving);
                            auto trial = core;
                            trial.erase(group);
                            activate(engine, trial);
                            ++checks;
                            const auto verdict = engine.solve();
                            if (verdict == sat::STATUS_UNKNOWN) throw Cancelled();
                            if (verdict == sat::STATUS_UNSAT) core = std::move(trial);
                            if (context.stop != StopReason::none) throw Cancelled();
                        }
                        minimal = stop == "complete";
                    } catch (const Cancelled&) {
                        stop = name(shrinking.stop == StopReason::none ? context.stop.load() : shrinking.stop.load());
                    }
                    shrinking.detach(&engine);
                }
                context.conflicts_used += shrinking.conflicts_used;
                context.propagations_used += shrinking.propagations_used;
                context.solve_ms += shrinking.solve_ms;
            }
            Json::Value result;
            result["depth"] = depth;
            result["verified_unsat"] = true;
            result["subset_minimal"] = minimal;
            result["minimization"]["checks"] = checks;
            result["minimization"]["stop_reason"] = stop;
            result["constraints"] = Json::arrayValue;
            for (auto group : core)
                result["constraints"].append(entries.at(group));
            result["candidate_count"] = Json::UInt64(enabled.size());
            return result;
        }
    } // namespace
    void explain(const QuerySpec& spec, QueryResult& result, QueryContext& context)
    {
        require(spec.watches.empty(), "Explanation queries do not evaluate watches");
        require(!spec.until, "Explanation queries do not accept until conditions");
        for (auto expression : spec.assumptions)
            require(state_expression(expression) && model::ModelMgr::INSTANCE().type(expression)->is_boolean(), "Explanation assumptions must be Boolean state expressions");
        const bool reach = spec.operation == Operation::explain_reach;
        const bool step = spec.operation == Operation::explain_step;
        require(!spec.target || model::ModelMgr::INSTANCE().type(spec.target)->is_boolean(), "Explanation goal must be Boolean");
        require(reach ? spec.target && spec.limits.depth >= 0 : !spec.target, "Bounded reach explanations require target and depth");
        require(!spec.explanation.get("exact_depth", false).asBool() || reach, "exact_depth applies only to explain-reach");
        require(!spec.explanation.isMember("active_ids") || !reach || spec.explanation.get("exact_depth", false).asBool(), "Reach subset rechecks require exact_depth");
        require(reach || spec.limits.depth < 0 || (step && spec.limits.depth == 1), "Initial explanations have no depth; continuation explanations add exactly one transition");
        witness::Witness_ptr parent = nullptr;
        unsigned prefix = 0;
        if (step) {
            require(!spec.trace.isNull(), "Continuation explanation requires a parent trace");
            auto replay = trace::validate(spec.trace, spec.parent_trace, context);
            if (replay.status == ExecutionStatus::unknown) {
                context.cancel(replay.reason == StopReason::none ? StopReason::solver_unknown : replay.reason);
                throw Cancelled();
            }
            require(replay.outcome == Outcome::valid, "Explanation parent failed replay");
            parent = replay.witness;
            require(spec.prefix_length <= int64_t(parent->size()), "Prefix exceeds parent trace");
            prefix = spec.prefix_length < 0 ? parent->size() : spec.prefix_length;
        } else
            require(spec.trace.isNull() && spec.trace_id.empty(), "Only continuation explanations accept a trace");
        algorithms::Algorithm a(model::ModelMgr::INSTANCE().model());
        auto empty = expr::ExprMgr::INSTANCE().make_empty();
        const unsigned last = reach ? spec.limits.depth : prefix;
        const unsigned first = step || spec.explanation.get("exact_depth", false).asBool() ? last : 0;
        result.scope = reach ? (first == 0 && !spec.explanation.get("exact_depth", false).asBool() ? "through_depth" : "exact_depth") : step ? "single_step_continuation"
                                                                                                                                             : "initial_state";
        result.explanation["version"] = 1;
        result.explanation["scope"] = result.scope;
        result.explanation["bound"] = last;
        result.explanation["prefix_length"] = prefix;
        result.explanation["query"] = spec_json(spec);
        result.explanation["background"] = "Fixed model declarations, finite type domains, bit widths, compile-time inputs, frozen-variable identity, and expression encoding semantics. All INIT, INVAR, TRANS/frame constraints, pinned values, user assumptions and goals are selectable.";
        result.explanation["cases"] = Json::arrayValue;
        for (unsigned depth = first; depth <= last; ++depth) {
            std::vector<Constraint> constraints;
            append(constraints, a.init_units(), "init", 0);
            for (unsigned k = 0; k <= depth; ++k) {
                append(constraints, a.invar_units(), "invar", k);
                if (k) append(constraints, a.trans_units(), "trans", k - 1);
                if (!step || k == prefix - 1) {
                    for (size_t i = 0; i < spec.assumptions.size(); ++i) {
                        auto unit = a.compiler().process(empty, spec.assumptions[i]);
                        auto id = "assumption:" + std::to_string(i) + ":t" + std::to_string(k);
                        constraints.push_back({ unit, k, metadata(id, "assumption", k, unit) });
                    }
                }
                if (parent && k < prefix) {
                    for (auto assignment : (*parent)[k].assignments()) {
                        auto& em = expr::ExprMgr::INSTANCE();
                        auto full = assignment->lhs();
                        auto unit = a.compiler().process(full->lhs(), em.make_eq(full->rhs(), assignment->rhs()));
                        auto id = "pin:" + source::print(full) + ":t" + std::to_string(k);
                        constraints.push_back({ unit, k, metadata(id, "pin", k, unit) });
                    }
                }
            }
            if (reach) {
                auto unit = a.compiler().process(empty, spec.target);
                constraints.push_back({ unit, depth, metadata("goal:t" + std::to_string(depth), "goal", depth, unit) });
            }
            bool feasible = false;
            const auto core = solve_case(spec, a, constraints, depth, context, feasible);
            result.checked_depths.push_back(depth);
            if (feasible) {
                result.explanation = Json::Value();
                result.status = ExecutionStatus::completed;
                result.outcome = Outcome::satisfiable;
                result.complete = true;
                return;
            }
            result.explanation["cases"].append(core);
        }
        result.status = ExecutionStatus::completed;
        result.outcome = Outcome::unsatisfiable;
        result.complete = true;
        result.proof_method = "selector-unsat-core";
    }
} // namespace query

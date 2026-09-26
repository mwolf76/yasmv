#include <algorithms/fsm/fsm.hh>
#include <algorithms/reach/reach.hh>
#include <algorithms/reach/witness.hh>
#include <algorithms/sim/simulation.hh>
#include <cmath>
#include <env/environment.hh>
#include <expr/time/analyzer/analyzer.hh>
#include <filesystem>
#include <fstream>
#include <opts/opts_mgr.hh>
#include <parse.hh>
#include <query/expressions.hh>
#include <query/query.hh>
#include <query/trace.hh>
#include <witness/witness_mgr.hh>
namespace query {
    static const char* name(ExecutionStatus s)
    {
        return s == ExecutionStatus::completed ? "completed" : s == ExecutionStatus::unknown ? "unknown"
                                                                                             : "error";
    }
    static const char* name(Outcome o)
    {
        switch (o) {
#define CASE(x)      \
    case Outcome::x: \
        return #x
            CASE(holds_bounded);
            CASE(violated);
            CASE(proven);
            CASE(none);
            CASE(satisfiable);
            CASE(unsatisfiable);
            CASE(reachable);
            CASE(unreachable);
            CASE(simulated);
            CASE(deadlocked);
            CASE(diameter);
            CASE(valid);
            CASE(invalid);
#undef CASE
        }
        return "none";
    }
    int QueryResult::exit_code() const
    {
        return status == ExecutionStatus::completed ? 0 : status == ExecutionStatus::unknown ? 3
                                                      : reason == StopReason::internal_error ? 4
                                                                                             : 2;
    }
    Json::Value QueryResult::json() const
    {
        Json::Value v;
        v["version"] = 1;
        v["request_id"] = request_id;
        v["status"] = name(status);
        v["outcome"] = outcome == Outcome::none ? Json::Value() : Json::Value(name(outcome));
        v["stop_reason"] = name(reason);
        v["scope"] = scope;
        if (scope == "through_depth" && (outcome == Outcome::holds_bounded || outcome == Outcome::unreachable || proof_method == "selector-unsat-core")) v["unbounded_outcome"] = "unknown";
        v["complete"] = complete;
        v["value"] = std::to_string(value);
        v["identity"] = identity;
        v["strategy"] = strategy;
        v["proof_method"] = proof_method;
        v["statistics"] = statistics;
        if (!symbols.isNull()) v["symbols"] = symbols;
        v["watches"] = watches;
        v["explanation"] = explanation;
        v["optimality"] = optimality;
        v["proof"] = proof;
        v["trace"] = trace;
        v["checked_depths"] = Json::arrayValue;
        for (auto d : checked_depths)
            v["checked_depths"].append(d);
        v["diagnostics"] = Json::arrayValue;
        for (const auto& d : diagnostics)
            v["diagnostics"].append(d.json());
        return v;
    }
    Json::Value identity()
    {
        Json::Value v;
        v["source_revision"] = source::revision();
        auto& mm = model::ModelMgr::INSTANCE();
        auto& om = opts::OptsMgr::INSTANCE();
        v["root"] = source::print(mm.model().main_module().name());
        v["engine"] = "yasmv-0.0.10/minisat";
        v["inputs"] = Json::objectValue;
        auto& env = env::Environment::INSTANCE();
        for (auto id : env.identifiers())
            v["inputs"][source::print(id)] = source::print(env.get(id));
        v["options"]["word_width"] = om.word_width();
        v["options"]["cnf_tautology_removal"] = om.cnf_tautology_removal();
        v["options"]["cnf_duplicate_removal"] = om.cnf_duplicate_removal();
        v["options"]["cnf_subsumption"] = om.cnf_subsumption();
        v["options"]["cnf_self_subsumption"] = om.cnf_self_subsumption();
        v["options"]["sat_random_var_freq"] = om.sat_random_var_freq();
        v["options"]["sat_random_init_act"] = om.sat_random_init_act();
        v["options"]["sat_ccmin_mode"] = om.sat_ccmin_mode();
        v["options"]["sat_phase_saving"] = om.sat_phase_saving();
        v["options"]["sat_garbage_frac"] = om.sat_garbage_frac();
        v["options"]["sat_var_decay"] = om.sat_var_decay();
        v["options"]["sat_clause_decay"] = om.sat_clause_decay();
        v["options"]["sat_random_seed"] = om.sat_random_seed();
        v["options"]["sat_luby_restart"] = om.sat_luby_restart();
        v["options"]["sat_restart_first"] = om.sat_restart_first();
        v["options"]["sat_restart_inc"] = om.sat_restart_inc();
        v["options"]["sat_elim"] = om.sat_elim();
        v["options"]["sat_rcheck"] = om.sat_rcheck();
        v["options"]["sat_asymm"] = om.sat_asymm();
        v["options"]["sat_grow"] = om.sat_grow();
        v["options"]["sat_clause_lim"] = om.sat_clause_lim();
        v["options"]["sat_subsumption_lim"] = om.sat_subsumption_lim();
        v["options"]["sat_simp_garbage_frac"] = om.sat_simp_garbage_frac();
        // JSON clients may rewrite 2.0 as 2. Normalize integral options before
        // fingerprinting so saving a trace in JavaScript preserves its identity.
        for (auto& option : v["options"]) {
            if (option.type() == Json::realValue) {
                const double n = option.asDouble();
                if (std::isfinite(n) && std::trunc(n) == n && n >= -9223372036854775808.0 && n < 9223372036854775808.0)
                    option = Json::Int64(n);
            }
        }
        v["environment_constraints"] = Json::arrayValue;
        for (const auto* list : { &env.extra_init(), &env.extra_invar(), &env.extra_trans() }) {
            Json::Value a(Json::arrayValue);
            for (auto e : *list)
                a.append(source::print(e));
            v["environment_constraints"].append(a);
        }
        static std::string fragments;
        if (fragments.empty()) {
            const char* home = std::getenv("YASMV_HOME");
            std::filesystem::path path = home ? home : ".";
            path = std::string(home ? home : ".") + om.cnf_microcode_directory();
            std::vector<std::filesystem::path> files;
            for (const auto& f : std::filesystem::directory_iterator(path))
                if (f.path().extension() == ".json") files.push_back(f.path());
            std::sort(files.begin(), files.end());
            std::ostringstream data;
            for (const auto& f : files) {
                std::ifstream in(f, std::ios::binary);
                checkpoint(Phase::loading);
                data << f.filename().string() << '\0' << in.rdbuf() << '\0';
            }
            fragments = source::digest(data.str());
        }
        v["microcode_revision"] = fragments;
        Json::StreamWriterBuilder builder;
        builder["indentation"] = "";
        v["model_revision"] = source::digest(Json::writeString(builder, v));
        return v;
    }
    static void valid_limits(const QueryLimits& l)
    {
        if (l.depth < -1 || l.depth >= UINT_MAX || l.states < -1 || l.states == 0 || l.wall_ms < -1 || l.conflicts < -1 || l.propagations < -1) throw std::invalid_argument("Invalid query limits");
    }
    void bounded_reach(const QuerySpec& spec, QueryResult& r)
    {
        if (!state_expression(spec.target)) throw std::invalid_argument("Bounded reachability requires a state target");
        for (auto e : spec.assumptions)
            if (!state_expression(e)) throw std::invalid_argument("Bounded reachability requires untimed state assumptions");
        auto& mm = model::ModelMgr::INSTANCE();
        algorithms::Algorithm a(mm.model());
        auto empty = expr::ExprMgr::INSTANCE().make_empty();
        auto goal = a.compiler().process(empty, spec.target);
        compiler::Units assumptions;
        for (auto e : spec.assumptions)
            assumptions.push_back(a.compiler().process(empty, e));
        sat::Engine engine("bounded-forward");
        a.assert_fsm_init(engine, 0);
        r.scope = "through_depth";
        r.strategy = "bounded-forward";
        for (unsigned k = 0; k <= static_cast<unsigned>(spec.limits.depth); ++k) {
            checkpoint(Phase::encoding);
            a.assert_fsm_invar(engine, k);
            for (auto& u : assumptions)
                a.assert_formula(engine, k, u);
            trace::allocate_state(engine, k);
            a.assert_formula(engine, k, goal, engine.new_group());
            auto status = engine.solve();
            if (status == sat::STATUS_UNKNOWN) return;
            r.checked_depths.push_back(k);
            if (status == sat::STATUS_SAT) {
                r.witness = trace::decode(engine, k);
                r.status = ExecutionStatus::completed;
                r.outcome = Outcome::reachable;
                r.complete = true;
                r.optimality["criterion"] = "transitions";
                r.optimality["certified"] = true;
                r.optimality["depth"] = k;
                r.optimality["unsat_depths"] = Json::arrayValue;
                for (unsigned smaller = 0; smaller < k; ++smaller) r.optimality["unsat_depths"].append(smaller);
                r.optimality["method"] = "increasing-depth-exhaustion";
                return;
            }
            engine.invert_last_group();
            if (k < static_cast<unsigned>(spec.limits.depth)) a.assert_fsm_trans(engine, k);
        }
        r.status = ExecutionStatus::completed;
        r.outcome = Outcome::unreachable;
        r.reason = StopReason::depth_limit;
        r.complete = true;
    }
    static void continuation(const QuerySpec& spec, QueryResult& r, QueryContext& context)
    {
        auto& wm = witness::WitnessMgr::INSTANCE();
        Json::Value parent = spec.trace;
        if (parent.isNull()) {
            auto& w = spec.trace_id.empty() ? wm.current() : wm.witness(spec.trace_id);
            parent = w.artifact;
            if (parent.isNull()) throw std::invalid_argument("Continuation requires a trace with generating-query metadata");
        }
        auto checked = trace::validate(parent, spec.parent_trace, context);
        if (checked.outcome != Outcome::valid) {
            if (checked.status == ExecutionStatus::unknown) throw Cancelled();
            throw std::invalid_argument("Continuation parent failed replay");
        }
        for (auto e : spec.assumptions)
            if (!state_expression(e)) throw std::invalid_argument("Continuation requires state assumptions");
        if (spec.until && !state_expression(spec.until)) throw std::invalid_argument("Continuation requires a state until condition");
        if (spec.prefix_length > int64_t(checked.witness->size())) throw std::invalid_argument("Prefix exceeds parent trace");
        const unsigned prefix = spec.prefix_length < 0 ? checked.witness->size() : spec.prefix_length;
        const unsigned count = spec.limits.depth < 0 ? 1 : spec.limits.depth;
        if (count == 0 || uint64_t(prefix) + count >= UINT_MAX) throw std::invalid_argument("Invalid continuation depth");
        algorithms::Algorithm a(model::ModelMgr::INSTANCE().model());
        sat::Engine engine("continuation");
        auto empty = expr::ExprMgr::INSTANCE().make_empty();
        a.assert_fsm_init(engine, 0);
        for (unsigned k = 0; k < prefix; ++k) {
            a.assert_fsm_invar(engine, k);
            a.assert_time_frame(engine, k, (*checked.witness)[k]);
            if (k) a.assert_fsm_trans(engine, k - 1);
        }
        compiler::Units assumptions;
        for (auto e : spec.assumptions)
            assumptions.push_back(a.compiler().process(empty, e));
        unsigned last = prefix - 1;
        r.scope = "continuation";
        r.strategy = "forward";
        r.outcome = Outcome::simulated;
        Json::Value evidence = parent;
        evidence["steps"].resize(prefix);
        evidence["origin"]["direction"] = "forward";
        evidence["origin"]["initial_time"] = 0;
        for (unsigned i = 0; i < count; ++i) {
            const unsigned group = engine.new_group();
            for (auto& u : assumptions)
                a.assert_formula(engine, last, u, group);
            a.assert_fsm_trans(engine, last, group);
            a.assert_fsm_invar(engine, last + 1, group);
            auto status = engine.solve();
            if (status == sat::STATUS_UNKNOWN) throw Cancelled();
            r.checked_depths.push_back(last + 1);
            if (status == sat::STATUS_UNSAT) {
                r.outcome = Outcome::deadlocked;
                break;
            }
            ++last;
            bool done = false;
            if (spec.until) {
                auto goal = a.compiler().process(empty, spec.until);
                a.assert_formula(engine, last, goal, engine.new_group());
                auto goal_status = engine.solve();
                if (goal_status == sat::STATUS_UNKNOWN) throw Cancelled();
                done = goal_status == sat::STATUS_SAT;
                if (!done) {
                    engine.invert_last_group();
                    if (engine.solve() != sat::STATUS_SAT) throw Cancelled();
                }
            }
            // Preserve a complete valuation before attempting a potentially deadlocked step.
            auto w = trace::decode(engine, last);
            evidence = trace::export_trace(*w, spec, r.identity);
            if (done) break;
        }
        auto w = trace::import_trace(evidence);
        w->set_id("continuation_" + std::to_string(wm.autoincrement()));
        auto effective = spec;
        effective.parent_trace = parent;
        r.trace = trace::export_trace(*w, effective, r.identity);
        r.trace["branch"]["parent_id"] = parent["id"];
        r.trace["branch"]["prefix_length"] = prefix;
        Json::StreamWriterBuilder builder;
        builder["indentation"] = "";
        r.trace["branch"]["parent_digest"] = source::digest(Json::writeString(builder, parent));
        w->artifact = r.trace;
        r.witness = w;
        r.status = ExecutionStatus::completed;
        r.complete = true;
    }
    QueryResult execute(const QuerySpec& spec, QueryContext& context)
    {
        ContextScope scope(context);
        QueryResult r;
        r.request_id = spec.request_id;
        const auto started = std::chrono::steady_clock::now();
        try {
            auto& mm = model::ModelMgr::INSTANCE();
            mm.require_valid();
            valid_limits(spec.limits);
            const auto& l = context.limits;
            if (l.depth != spec.limits.depth || l.states != spec.limits.states || l.wall_ms != spec.limits.wall_ms || l.conflicts != spec.limits.conflicts || l.propagations != spec.limits.propagations)
                throw std::invalid_argument("QueryContext limits must match QuerySpec limits");
            const bool reaching = spec.operation == Operation::reach || spec.operation == Operation::shortest_reach;
            const bool property = spec.operation == Operation::check_property || spec.operation == Operation::prove_property;
            if (property != !spec.property.isNull()) throw std::invalid_argument("Named property requires check-property or prove-property");
            if ((property || spec.operation == Operation::shortest_reach) && spec.limits.depth < 0) throw std::invalid_argument("An explicit depth is required");
            const bool explaining = spec.operation == Operation::explain_init || spec.operation == Operation::explain_step || spec.operation == Operation::explain_reach;
            if (!explaining && !spec.explanation.isNull()) throw std::invalid_argument("Explanation options require an explanation operation");
            if (spec.prefix_length != -1 && ((spec.operation != Operation::simulate && spec.operation != Operation::explain_step) || spec.prefix_length <= 0)) throw std::invalid_argument("Prefix length applies only to continuation");
            for (const auto& [name, e] : spec.watches)
                if (name.empty() || !state_expression(e) || !mm.type(e)->is_boolean()) throw std::invalid_argument("Watches require named Boolean state expressions");
            if (!reaching && spec.strategy != "auto") throw std::invalid_argument("Strategy selection applies only to reachability");
            if (spec.target && ((!reaching && spec.operation != Operation::explain_reach) || !state_expression(spec.target))) throw std::invalid_argument("Reachability target must be a state expression");
            if (spec.until && spec.operation != Operation::simulate) throw std::invalid_argument("Until condition applies only to simulation");
            if (spec.operation != Operation::pick_state && (spec.enumerate || spec.count)) throw std::invalid_argument("Enumeration/counting applies only to pick-state");
            if (spec.operation == Operation::check_init || spec.operation == Operation::pick_state || spec.operation == Operation::check_trans)
                for (auto e : spec.assumptions)
                    if (!state_expression(e)) throw std::invalid_argument("This operation requires state assumptions");
            if (spec.limits.states >= 0 && spec.operation != Operation::pick_state) throw std::invalid_argument("State limit applies only to pick-state");
            if (spec.limits.depth >= 0 && (spec.operation == Operation::check_init || spec.operation == Operation::pick_state || spec.operation == Operation::validate_trace || spec.operation == Operation::validate_model)) throw std::invalid_argument("Depth limit is unsupported for this operation");
            if (reaching)
                for (auto e : spec.assumptions)
                    if (!state_expression(e, spec.limits.depth < 0)) throw std::invalid_argument("Incompatible timed assumption");
            context.requested_strategy = spec.strategy;
            context.check(Phase::compilation);
            r.identity = identity();
            if (spec.strategy != "auto" && spec.strategy != "forward" && spec.strategy != "backward") throw std::invalid_argument("Unknown or empty strategy configuration");
            if (reaching && !spec.target) throw std::invalid_argument("Reachability requires a target");
            if (property) {
                analyze_property(spec, r, context);
            } else if (explaining) {
                explain(spec, r, context);
            } else if (spec.operation == Operation::validate_model) {
                if (!spec.assumptions.empty()) throw std::invalid_argument("Model validation does not accept assumptions");
                r.status = ExecutionStatus::completed;
                r.outcome = Outcome::valid;
                r.scope = "model";
                r.symbols = trace::symbol_catalog();
                r.complete = true;
            } else if (spec.operation == Operation::check_init) {
                fsm::CheckInitConsistency a(mm.model());
                a.process(spec.assumptions);
                if (a.status() != fsm::FSM_CONSISTENCY_UNDECIDED) {
                    r.status = ExecutionStatus::completed;
                    r.complete = true;
                    r.outcome = a.status() == fsm::FSM_CONSISTENCY_OK ? Outcome::satisfiable : Outcome::unsatisfiable;
                    r.checked_depths = { 0 };
                }
            } else if (spec.operation == Operation::check_trans) {
                if (spec.limits.depth <= 0) throw std::invalid_argument("Transition check requires a positive depth");
                fsm::CheckTransConsistency a(mm.model());
                a.set_limit(spec.limits.depth);
                a.process(spec.assumptions, [&r](sat::Engine& e) {auto s=e.solve();if(s!=sat::STATUS_UNKNOWN)r.checked_depths.push_back(r.checked_depths.size()+1);return s; });
                if (a.status() != fsm::FSM_CONSISTENCY_UNDECIDED) {
                    r.status = ExecutionStatus::completed;
                    r.complete = true;
                    r.outcome = a.status() == fsm::FSM_CONSISTENCY_OK ? Outcome::satisfiable : Outcome::unsatisfiable;
                }
                r.scope = "through_depth";
            } else if (spec.operation == Operation::pick_state) {
                if (spec.enumerate && spec.count) throw std::invalid_argument("Counting and enumeration are mutually exclusive");
                const auto previous = witness::WitnessMgr::INSTANCE().witnesses().size();
                sim::Simulation a(mm.model());
                const auto result = a.pick_state(spec.assumptions, spec.enumerate, spec.count, spec.limits.states);
                r.value = result.count;
                r.complete = result.complete();
                if (result.stop == sim::EnumerationStop::limit)
                    r.reason = StopReason::state_limit;
                else if (result.stop != sim::EnumerationStop::unknown) {
                    r.status = ExecutionStatus::completed;
                    r.outcome = result.count ? Outcome::satisfiable : Outcome::unsatisfiable;
                }
                if (a.has_witness()) r.witness = &a.witness();
                size_t index = 0;
                for (auto w : witness::WitnessMgr::INSTANCE().witnesses())
                    if (index++ >= previous) w->artifact = trace::export_trace(*w, spec, r.identity);
            } else if (reaching) {
                if (spec.limits.depth >= 0) {
                    if (spec.strategy == "backward") throw std::invalid_argument("Bounded queries currently support the forward strategy");
                    bounded_reach(spec, r);
                } else {
                    reach::Reachability a(mm.model());
                    a.process(spec.target, spec.assumptions);
                    r.scope = "unbounded";
                    r.strategy = context.selected_strategy;
                    r.checked_depths = context.checked_depths;
                    if (a.status() == reach::REACHABILITY_ERROR) throw std::invalid_argument("No compatible reachability strategy is enabled");
                    if (a.status() != reach::REACHABILITY_UNKNOWN) {
                        r.status = ExecutionStatus::completed;
                        r.complete = true;
                        r.outcome = a.status() == reach::REACHABILITY_REACHABLE ? Outcome::reachable : Outcome::unreachable;
                        if (r.outcome == Outcome::unreachable) r.proof_method = "simple-path-exhaustion";
                    }
                    if (a.has_witness()) r.witness = &a.witness();
                }
            } else if (spec.operation == Operation::simulate) {
                continuation(spec, r, context);
            } else if (spec.operation == Operation::diameter) {
                fsm::ComputeDiameter a(mm.model());
                a.process();
                r.value = a.diameter();
                r.checked_depths = context.checked_depths;
                if (r.value != UINT_MAX) {
                    r.status = ExecutionStatus::completed;
                    r.outcome = Outcome::diameter;
                    r.complete = true;
                    r.scope = "unbounded";
                    r.proof_method = "simple-path-exhaustion";
                }
            } else if (spec.operation == Operation::validate_trace) {
                r = trace::validate(spec.trace, spec.parent_trace, context, spec.request_id);
            }
            if (r.witness && r.status == ExecutionStatus::completed && r.trace.isNull()) {
                auto evidence_spec = spec;
                if (r.strategy == "backward") evidence_spec.strategy = "backward";
                r.trace = trace::export_trace(*r.witness, evidence_spec, r.identity);
                r.witness->artifact = r.trace;
            }
            if (r.witness && r.status == ExecutionStatus::completed && !spec.watches.empty())
                r.watches = trace::evaluate_watches(*r.witness, spec.watches);
            if (context.stop != StopReason::none) throw Cancelled();
            if (r.witness && r.status == ExecutionStatus::completed &&
                (spec.operation == Operation::simulate || (reaching && spec.limits.depth >= 0))) {
                auto& wm = witness::WitnessMgr::INSTANCE();
                wm.record(*r.witness);
                wm.set_current(*r.witness);
            }
            if (r.status == ExecutionStatus::unknown && r.reason == StopReason::none) r.reason = StopReason::solver_unknown;
        } catch (const Cancelled&) {
            if (!context.checked_depths.empty()) r.checked_depths = context.checked_depths;
            r.status = ExecutionStatus::unknown;
            r.outcome = Outcome::none;
            r.complete = false;
            r.reason = context.stop;
            r.trace = Json::Value();
            r.explanation = Json::Value();
            r.optimality = Json::Value();
            r.proof = Json::Value();
            r.witness = nullptr;
        } catch (const Exception& e) {
            r.status = ExecutionStatus::error;
            r.reason = StopReason::validation_error;
            source::Diagnostic d;
            d.code = "invalid-query";
            d.message = e.what();
            r.diagnostics.push_back(d);
        } catch (const std::invalid_argument& e) {
            r.status = ExecutionStatus::error;
            r.reason = StopReason::validation_error;
            source::Diagnostic d;
            d.code = "invalid-query";
            d.message = e.what();
            r.diagnostics.push_back(d);
        } catch (const std::exception& e) {
            r.status = ExecutionStatus::error;
            r.reason = StopReason::internal_error;
            source::Diagnostic d;
            d.code = "internal-error";
            d.message = e.what();
            r.diagnostics.push_back(d);
        }
        if (r.status == ExecutionStatus::error) {
            r.outcome = Outcome::none;
            r.complete = false;
            r.trace = Json::Value();
            r.explanation = Json::Value();
            r.optimality = Json::Value();
            r.proof = Json::Value();
            r.witness = nullptr;
        }
        r.statistics["compile_ms"] = context.compile_ms;
        r.statistics["encode_ms"] = context.encode_ms;
        r.statistics["solve_ms"] = context.solve_ms;
        r.statistics["decode_ms"] = context.decode_ms;
        r.statistics["elapsed_ms"] = std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - started).count();
        r.statistics["variables"] = Json::UInt64(context.variables);
        r.statistics["clauses"] = Json::UInt64(context.clauses);
        r.statistics["conflicts"] = Json::UInt64(context.conflicts_used);
        r.statistics["propagations"] = Json::UInt64(context.propagations_used);
        return r;
    }
    QueryResult execute(const QuerySpec& spec)
    {
        QueryContext context(spec.limits);
        return execute(spec, context);
    }
    QueryResult checked(const QuerySpec& spec)
    {
        auto r = execute(spec);
        if (r.status == ExecutionStatus::error) {
            const auto message = r.diagnostics.empty() ? "Query failed" : r.diagnostics.front().message;
            if (r.reason == StopReason::internal_error) throw std::runtime_error(message);
            throw model::SemanticError(message);
        }
        return r;
    }
} // namespace query

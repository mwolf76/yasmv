#include <algorithms/base.hh>
#include <parse.hh>
#include <query/expressions.hh>
#include <query/trace.hh>
#include <algorithm>
#include <map>
#include <memory>
#include <set>

namespace query {
    namespace {
        void require(bool value, const std::string& message)
        {
            if (!value) throw std::invalid_argument(message);
        }
        void state_budget(size_t size)
        {
            if (size > static_cast<uint64_t>(current()->limits.states)) {
                current()->cancel(StopReason::state_limit);
                throw Cancelled();
            }
        }
        void fields(const Json::Value& v, std::initializer_list<const char*> names)
        {
            require(v.isObject(), "Expected progress artifact object");
            std::set<std::string> expected(names.begin(), names.end());
            require(v.size() == expected.size(), "Progress artifact fields mismatch");
            for (const auto& key : v.getMemberNames()) require(expected.count(key), "Unknown progress field: " + key);
        }
        std::string canonical(const Json::Value& v)
        {
            Json::StreamWriterBuilder w;
            w["indentation"] = "";
            return Json::writeString(w, v);
        }
        // Check the actual instantiated model, including definitions/parameters.
        bool local(expr::Expr_ptr e, expr::Expr_ptr scope, unsigned time, unsigned last, unsigned depth = 0, bool deterministic = false)
        {
            checkpoint(Phase::compilation);
            if (!e) return true;
            require(depth < 512, "Progress expression expansion is too deep");
            if (time > last || e->symb() == expr::AT) return false;
            auto& em = expr::ExprMgr::INSTANCE();
            if (deterministic && (em.is_set(e) || em.is_set_comma(e))) return false;
            auto recur = [&](expr::Expr_ptr x, unsigned t) { return local(x, scope, t, last, depth + 1, deterministic); };
            if (e->symb() == expr::NEXT) return recur(e->lhs(), time + 1);
            if (e->symb() == expr::ASSIGNMENT) return recur(e->lhs(), time + 1) && recur(e->rhs(), time);
            if (em.is_constant(e) || e->symb() == expr::QSTRING || e->symb() == expr::INSTANT || e->symb() == expr::TYPE) return true;
            if (em.is_dot(e)) return local(e->rhs(), em.make_dot(scope, e->lhs()), time, last, depth + 1, deterministic);
            if (em.is_identifier(e)) {
                symb::ResolverProxy resolver;
                auto full = em.make_dot(scope, e);
                auto symbol = resolver.symbol(full);
                if (symbol->is_define()) return recur(symbol->as_define().body(), time);
                if (symbol->is_parameter()) {
                    auto rewrite = model::ModelMgr::INSTANCE().rewrite_parameter(full);
                    return local(rewrite->rhs(), rewrite->lhs(), time, last, depth + 1, deterministic);
                }
                if (symbol->is_variable() && symbol->as_variable().is_input())
                    return recur(env::Environment::INSTANCE().get(e), time);
                return true;
            }
            return recur(e->lhs(), time) && recur(e->rhs(), time);
        }
        void check_fragment()
        {
            auto& mm = model::ModelMgr::INSTANCE();
            auto& em = expr::ExprMgr::INSTANCE();
            std::vector<std::pair<expr::Expr_ptr, model::Module*>> pending { { em.make_empty(), &mm.model().main_module() } };
            while (!pending.empty()) {
                auto [scope, module] = pending.back();
                pending.pop_back();
                for (auto e : module->init()) require(local(e, scope, 0, 0), "Progress requires state-local INIT");
                for (auto e : module->invar()) require(local(e, scope, 0, 0), "Progress requires state-local INVAR");
                for (auto e : module->trans()) require(local(e, scope, 0, 1), "Progress requires one-step TRANS without explicit time references");
                for (const auto& [id, var] : module->vars())
                    if (var->type()->is_instance()) pending.push_back({ em.make_dot(scope, id), &mm.model().module(var->type()->as_instance()->name()) });
            }
            auto& env = env::Environment::INSTANCE();
            for (auto e : env.extra_init()) require(local(e, em.make_empty(), 0, 0), "Nonlocal environment INIT");
            for (auto e : env.extra_invar()) require(local(e, em.make_empty(), 0, 0), "Nonlocal environment INVAR");
            for (auto e : env.extra_trans()) require(local(e, em.make_empty(), 0, 1), "Nonlocal environment TRANS");
        }
        expr::Expr_ptr finite_domain(expr::Expr_ptr key, type::Type_ptr type)
        {
            auto& em = expr::ExprMgr::INSTANCE();
            auto result = em.make_true();
            if (type->is_enum()) {
                result = em.make_false();
                for (auto literal : type->as_enum()->literals()) result = em.make_or(result, em.make_eq(key, literal));
            } else if (type->is_array()) {
                for (unsigned i = 0; i < type->as_array()->nelems(); ++i)
                    result = em.make_and(result, finite_domain(em.make_subscript(key, em.make_const(i)), type->as_array()->of()));
            }
            return result;
        }
        expr::Expr_ptr finite_domains()
        {
            auto& em = expr::ExprMgr::INSTANCE();
            auto result = em.make_true();
            symb::SymbIter it(model::ModelMgr::INSTANCE().model());
            while (it.has_next()) {
                auto [scope, symbol] = it.next();
                if (!symbol->is_variable() || symbol->as_variable().type()->is_instance()) continue;
                auto name = source::print(em.make_dot(scope, symbol->name()));
                result = em.make_and(result, finite_domain(parse::parseExpression(name.c_str()), symbol->as_variable().type()));
            }
            return result;
        }
        class GraphSolver {
        public:
            algorithms::Algorithm a;
            QuerySpec spec;
            compiler::Unit good, bad, domains;
            compiler::Units assumptions;
            GraphSolver(const QuerySpec& s)
                : a(model::ModelMgr::INSTANCE().model()), spec(s), good(compile(s.target)), bad(compile(a.em().make_not(s.target))), domains(compile(finite_domains()))
            {
                for (auto e : s.assumptions) assumptions.push_back(compile(e));
            }
            compiler::Unit compile(expr::Expr_ptr e) { return a.compiler().process(a.em().make_empty(), e); }
            void state(sat::Engine& e, unsigned t)
            {
                checkpoint(Phase::encoding);
                a.assert_fsm_invar(e, t);
                a.assert_formula(e, t, domains);
                for (auto& u : assumptions) a.assert_formula(e, t, u);
                trace::allocate_state(e, t);
            }
            void initial(sat::Engine& e) { state(e, 0); a.assert_fsm_init(e, 0); }
            void successors(sat::Engine& e, const Json::Value& v)
            {
                state(e, 0); state(e, 1);
                pin(e, v, 0);
                a.assert_fsm_trans(e, 0);
            }
            void pin(sat::Engine& e, const Json::Value& v, unsigned t, bool negate = false)
            {
                auto expression = trace::valuation(v);
                auto unit = compile(negate ? a.em().make_not(expression) : expression);
                a.assert_formula(e, t, unit);
            }
            bool solve(sat::Engine& e)
            {
                auto s = e.solve();
                if (s == sat::STATUS_UNKNOWN) {
                    if (current()->stop == StopReason::none) current()->cancel(StopReason::solver_unknown);
                    throw Cancelled();
                }
                return s == sat::STATUS_SAT;
            }
            bool initial_sat()
            {
                sat::Engine e("progress-initial"); initial(e); return solve(e);
            }
            bool goal_exit(const Json::Value& v)
            {
                sat::Engine e("progress-goal-exit"); successors(e, v); a.assert_formula(e, 1, good); return solve(e);
            }
        };
        struct Node {
            Json::Value values;
            std::vector<unsigned> edges;
            int parent;
            bool exit = false;
        };
        // Iterative DFS distinguishes cycles from merged paths and avoids stack overflow.
        std::vector<unsigned> cycle(const std::vector<Node>& nodes, std::vector<unsigned>& ranks)
        {
            std::vector<unsigned> color(nodes.size(), 0), position(nodes.size(), 0);
            ranks.assign(nodes.size(), 0);
            std::vector<unsigned> stack;
            std::vector<size_t> cursor;
            for (unsigned root = 0; root < nodes.size(); ++root) {
                if (color[root]) continue;
                stack.push_back(root); cursor.push_back(0); color[root] = 1; position[root] = 0;
                while (!stack.empty()) {
                    checkpoint(Phase::solving);
                    auto v = stack.back();
                    if (cursor.back() < nodes[v].edges.size()) {
                        auto u = nodes[v].edges[cursor.back()++];
                        if (color[u] == 1) return { stack.begin() + position[u], stack.end() };
                        if (!color[u]) {
                            position[u] = stack.size(); stack.push_back(u); cursor.push_back(0); color[u] = 1;
                        }
                    } else {
                        for (auto u : nodes[v].edges) ranks[v] = std::max(ranks[v], ranks[u] + 1);
                        color[v] = 2; stack.pop_back(); cursor.pop_back();
                    }
                }
            }
            return {};
        }
        QuerySpec progress_spec(const Json::Value& artifact)
        {
            require(artifact.isObject() && artifact["version"].isInt() && artifact["version"].asInt() == 1, "Unsupported progress artifact version");
            require(artifact["kind"].isString() && artifact["identity"].isObject(), "Malformed progress artifact header");
            require(canonical(artifact["identity"]) == canonical(identity()), "Progress model/configuration identity mismatch");
            auto spec = spec_from_json(artifact["query"]);
            require(spec.operation == Operation::check_progress && spec.target && spec.progress.isNull(), "Invalid generating progress query");
            return spec;
        }
        void check_spec(const QuerySpec& s)
        {
            auto& mm = model::ModelMgr::INSTANCE();
            auto empty = expr::ExprMgr::INSTANCE().make_empty();
            require(s.target && state_expression(s.target) && local(s.target, empty, 0, 0, 0, true) && mm.type(s.target)->is_boolean(), "Progress target must be a deterministic Boolean state expression");
            for (auto e : s.assumptions)
                require(state_expression(e) && local(e, empty, 0, 0, 0, true) && mm.type(e)->is_boolean(), "Progress assumptions must be deterministic Boolean state expressions");
            require(s.limits.depth == -1 && s.limits.states > 0 && s.limits.wall_ms >= 0, "Progress requires positive states and a wall budget; depth is unsupported");
            require(s.strategy == "auto" && !s.until && !s.enumerate && !s.count && s.prefix_length == -1 && s.trace.isNull() && s.parent_trace.isNull() && s.trace_id.empty() && s.explanation.isNull() && s.property.isNull() && s.progress.isNull(), "Unsupported progress query option");
            check_fragment();
        }
        bool verify(GraphSolver& g, const Json::Value& artifact)
        {
            const auto kind = artifact["kind"].asString();
            if (kind == "proof") {
                fields(artifact, { "version", "kind", "identity", "query", "initial_satisfiable", "vacuous", "nodes" });
                require(artifact["initial_satisfiable"].isBool() && artifact["vacuous"].isBool() && artifact["nodes"].isArray(), "Malformed progress proof");
                bool initial = g.initial_sat();
                if (initial != artifact["initial_satisfiable"].asBool() || !initial != artifact["vacuous"].asBool()) return false;
                const auto& nodes = artifact["nodes"];
                state_budget(nodes.size());
                std::set<std::string> unique;
                // Closure of the initial non-goal region.
                sat::Engine init("verify-progress-initial-coverage"); g.initial(init); g.a.assert_formula(init, 0, g.bad);
                for (const auto& n : nodes) {
                    fields(n, { "values", "edges", "goal_exit", "rank" });
                    require(n["edges"].isArray() && n["goal_exit"].isBool() && n["rank"].isUInt64(), "Malformed progress node");
                    require(unique.insert(canonical(n["values"])).second, "Duplicate proof state");
                    g.pin(init, n["values"], 0, true);
                }
                if (g.solve(init)) return false;
                for (unsigned i = 0; i < nodes.size(); ++i) {
                    checkpoint(Phase::solving);
                    const auto& n = nodes[i];
                    sat::Engine legal("verify-progress-state"); g.state(legal, 0); g.pin(legal, n["values"], 0); g.a.assert_formula(legal, 0, g.bad);
                    if (!g.solve(legal)) return false;
                    if (g.goal_exit(n["values"]) != n["goal_exit"].asBool()) return false;
                    if (n["edges"].empty() && !n["goal_exit"].asBool()) return false;
                    sat::Engine closure("verify-progress-successor-coverage"); g.successors(closure, n["values"]); g.a.assert_formula(closure, 1, g.bad);
                    std::set<unsigned> edges;
                    for (const auto& edge : n["edges"]) {
                        require(edge.isUInt() && edge.asUInt() < nodes.size() && edges.insert(edge.asUInt()).second, "Invalid or duplicate proof edge");
                        const auto& dest = nodes[edge.asUInt()];
                        require(dest["rank"].isUInt64(), "Invalid destination rank");
                        if (n["rank"].asUInt64() <= dest["rank"].asUInt64()) return false;
                        sat::Engine transition("verify-progress-edge"); g.successors(transition, n["values"]); g.pin(transition, dest["values"], 1);
                        if (!g.solve(transition)) return false;
                        g.pin(closure, dest["values"], 1, true);
                    }
                    if (g.solve(closure)) return false;
                }
                return true;
            }
            require(kind == "loop" || kind == "deadlock", "Unknown progress artifact kind");
            if (kind == "loop") fields(artifact, { "version", "kind", "identity", "query", "trace", "loop_start" });
            else fields(artifact, { "version", "kind", "identity", "query", "trace" });
            const auto& trace = artifact["trace"];
            auto path_spec = spec_from_json(trace["query"]);
            require(path_spec.operation == Operation::reach && path_spec.target &&
                    path_spec.target == g.a.em().make_not(g.spec.target) &&
                    spec_json(path_spec)["assumptions"] == spec_json(g.spec)["assumptions"] &&
                    trace["branch"].isNull() && path_spec.parent_trace.isNull() && path_spec.strategy == "auto",
                    "Finite path context differs from progress query");
            require(trace["steps"].isArray() && !trace["steps"].empty(), "Missing counterexample path");
            state_budget(trace["steps"].size());
            auto replay = query::trace::validate(trace, Json::Value(), *current());
            if (replay.status == ExecutionStatus::unknown) { current()->cancel(replay.reason); throw Cancelled(); }
            if (replay.status == ExecutionStatus::error) throw std::invalid_argument("Malformed counterexample trace");
            if (replay.outcome != Outcome::valid) return false;
            const auto& steps = trace["steps"];
            for (const auto& step : steps) {
                sat::Engine e("verify-progress-avoids-goal"); g.state(e, 0); g.pin(e, step["values"], 0); g.a.assert_formula(e, 0, g.good);
                if (g.solve(e)) return false;
            }
            sat::Engine closing("verify-progress-ending"); g.successors(closing, steps[steps.size() - 1]["values"]);
            if (kind == "deadlock") return !g.solve(closing);
            require(artifact["loop_start"].isUInt() && artifact["loop_start"].asUInt() < steps.size(), "Invalid loop start");
            g.pin(closing, steps[artifact["loop_start"].asUInt()]["values"], 1);
            return g.solve(closing);
        }
        Json::Value base_artifact(const QuerySpec& spec, const Json::Value& id, const std::string& kind)
        {
            Json::Value v; v["version"] = 1; v["identity"] = id; v["query"] = spec_json(spec); v["kind"] = kind; return v;
        }
        Json::Value failure_artifact(GraphSolver& g, const std::vector<Node>& nodes, unsigned end, const std::vector<unsigned>& loop, const Json::Value& id)
        {
            std::vector<unsigned> path;
            for (int n = end; n >= 0; n = nodes[n].parent) { checkpoint(Phase::decoding); path.push_back(n); }
            std::reverse(path.begin(), path.end());
            auto artifact = base_artifact(g.spec, id, loop.empty() ? "deadlock" : "loop");
            if (!loop.empty()) {
                size_t entry = 0;
                while (std::find(loop.begin(), loop.end(), path[entry]) == loop.end()) ++entry;
                auto offset = std::find(loop.begin(), loop.end(), path[entry]) - loop.begin();
                path.resize(entry + 1);
                artifact["loop_start"] = Json::UInt(entry);
                for (size_t i = 1; i < loop.size(); ++i) path.push_back(loop[(offset + i) % loop.size()]);
            }
            QuerySpec reach;
            reach.operation = Operation::reach; reach.target = g.a.em().make_not(g.spec.target); reach.assumptions = g.spec.assumptions;
            Json::Value t;
            t["version"] = 1; t["id"] = "progress-path"; t["identity"] = id; t["initial_time"] = 0;
            t["origin"]["initial_time"] = 0; t["origin"]["direction"] = "forward";
            t["symbols"] = trace::symbol_catalog(); t["query"] = spec_json(reach); t["branch"] = Json::Value(); t["steps"] = Json::arrayValue;
            for (auto n : path) {
                checkpoint(Phase::decoding);
                Json::Value step; step["step"] = t["steps"].size(); step["values"] = nodes[n].values; t["steps"].append(step);
            }
            artifact["trace"] = t;
            return artifact;
        }
    } // namespace
    void analyze_progress(const QuerySpec& request, QueryResult& result, QueryContext& context)
    {
        const bool validating = request.operation == Operation::validate_progress;
        require(request.limits.depth == -1 && request.limits.states > 0 && request.limits.wall_ms >= 0, "Progress requires positive states and a wall budget; depth is unsupported");
        if (validating) require(!request.target && request.assumptions.empty() && request.watches.empty() && request.trace.isNull() && request.parent_trace.isNull() && request.trace_id.empty(), "Validation uses artifact context, not new assumptions or traces");
        auto spec = validating ? progress_spec(request.progress) : request;
        check_spec(spec);
        GraphSolver g(spec);
        result.scope = validating ? "whole_progress_artifact" : "unbounded";
        result.strategy = "explicit-sat-graph";
        if (validating) {
            bool valid = verify(g, request.progress);
            result.status = ExecutionStatus::completed; result.complete = true;
            result.outcome = valid ? Outcome::valid : Outcome::invalid;
            if (valid) result.progress = request.progress;
            return;
        }
        bool initial = g.initial_sat();
        std::vector<Node> nodes;
        std::map<std::string, unsigned> index;
        size_t expanded = 0, edge_count = 0;
        auto stats = [&] {
            auto& s = result.statistics["graph"];
            s["states"] = Json::UInt64(nodes.size()); s["edges"] = Json::UInt64(edge_count);
            s["expanded"] = Json::UInt64(expanded); s["pending"] = Json::UInt64(nodes.size() - expanded);
        };
        auto admit = [&](const Json::Value& values, int parent) {
            const auto key = canonical(values);
            auto it = index.find(key);
            if (it != index.end()) return it->second;
            if (nodes.size() >= static_cast<uint64_t>(spec.limits.states)) { context.cancel(StopReason::state_limit); throw Cancelled(); }
            unsigned n = nodes.size(); index[key] = n; nodes.push_back({ values, {}, parent, false }); return n;
        };
        auto publish_failure = [&](unsigned end, const std::vector<unsigned>& loop) {
            auto evidence = failure_artifact(g, nodes, end, loop, result.identity);
            if (!verify(g, evidence)) throw std::runtime_error("Progress counterexample failed fresh replay");
            result.progress = evidence; result.trace = evidence["trace"];
            result.witness = trace::import_trace(result.trace);
            result.outcome = Outcome::violated; result.proof_method = "replayed-progress-counterexample";
        };
        try {
            sat::Engine init("progress-enumerate-initial"); g.initial(init); g.a.assert_formula(init, 0, g.bad);
            while (g.solve(init)) {
                auto values = trace::state_values(init, 0); admit(values, -1); g.pin(init, values, 0, true);
            }
            std::vector<unsigned> ranks;
            for (unsigned n = 0; n < nodes.size(); ++n) {
                auto values = nodes[n].values; // admitting successors may reallocate nodes
                nodes[n].exit = g.goal_exit(values);
                sat::Engine next("progress-enumerate-successors"); g.successors(next, values); g.a.assert_formula(next, 1, g.bad);
                while (g.solve(next)) {
                    auto successor = trace::state_values(next, 1);
                    auto dest = admit(successor, n); nodes[n].edges.push_back(dest); ++edge_count;
                    g.pin(next, successor, 1, true);
                    if (dest == n) { publish_failure(n, { n }); stats(); result.status = ExecutionStatus::completed; result.complete = true; return; }
                }
                ++expanded;
                if (nodes[n].edges.empty() && !nodes[n].exit) { publish_failure(n, {}); break; }
                if (expanded % 64 == 0 || expanded == nodes.size()) {
                    auto loop = cycle(nodes, ranks);
                    if (!loop.empty()) { publish_failure(loop.front(), loop); break; }
                }
            }
            if (result.outcome != Outcome::violated) {
                auto loop = cycle(nodes, ranks);
                if (!loop.empty()) publish_failure(loop.front(), loop);
                else {
                    auto proof = base_artifact(spec, result.identity, "proof");
                    proof["initial_satisfiable"] = initial; proof["vacuous"] = !initial; proof["nodes"] = Json::arrayValue;
                    for (unsigned i = 0; i < nodes.size(); ++i) {
                        checkpoint(Phase::decoding);
                        Json::Value n; n["values"] = nodes[i].values; n["rank"] = ranks[i]; n["goal_exit"] = nodes[i].exit; n["edges"] = Json::arrayValue;
                        for (auto e : nodes[i].edges) n["edges"].append(e);
                        proof["nodes"].append(n);
                    }
                    if (!verify(g, proof)) throw std::runtime_error("Progress proof failed fresh verification");
                    result.progress = proof; result.outcome = Outcome::proven; result.proof_method = "finite-graph-ranking";
                    result.proof["verified"] = true; result.proof["verification"] = "fresh-solvers";
                    result.proof["initial_satisfiable"] = initial; result.proof["vacuous"] = !initial;
                }
            }
            result.status = ExecutionStatus::completed; result.complete = true;
            stats();
        } catch (...) { stats(); throw; }
    }
} // namespace query

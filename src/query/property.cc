#include <algorithms/base.hh>
#include <parse.hh>
#include <query/expressions.hh>
#include <query/trace.hh>

namespace query {
    void analyze_property(const QuerySpec& spec, QueryResult& r, QueryContext& context)
    {
        auto& mm = model::ModelMgr::INSTANCE();
        auto& em = expr::ExprMgr::INSTANCE();
        auto property = parse::parseExpression(spec.property["expression"].asCString());
        if (!property || !state_expression(property) || !mm.type(property)->is_boolean())
            throw std::invalid_argument("Safety property must be a Boolean state expression");
        for (auto e : spec.assumptions)
            if (!state_expression(e) || !mm.type(e)->is_boolean()) throw std::invalid_argument("Safety assumptions must be Boolean state expressions");
        if (spec.operation == Operation::prove_property && spec.limits.depth < 1)
            throw std::invalid_argument("Induction requires a positive depth");
        auto search = spec;
        search.target = em.make_not(property);
        bounded_reach(search, r);
        r.proof["property"] = spec.property;
        r.proof["assumptions"] = spec_json(spec)["assumptions"];
        r.proof["base_unsat_depths"] = Json::arrayValue;
        for (auto d : r.checked_depths)
            if (!r.witness || d + 1 < r.witness->size()) r.proof["base_unsat_depths"].append(d);
        if (r.status != ExecutionStatus::completed) return;
        if (r.outcome == Outcome::reachable) {
            r.outcome = Outcome::violated;
            r.proof_method = "bounded-counterexample";
            return;
        }
        r.outcome = Outcome::holds_bounded;
        r.proof_method = "bounded-exhaustion";
        if (spec.operation == Operation::check_property) return;

        algorithms::Algorithm a(mm.model());
        const auto empty = em.make_empty();
        auto good = a.compiler().process(empty, property);
        auto bad = a.compiler().process(empty, search.target);
        compiler::Units assumptions;
        for (auto e : spec.assumptions)
            assumptions.push_back(a.compiler().process(empty, e));
        const unsigned depth = spec.limits.depth;
        auto obligation = [&](bool initial, unsigned n, const std::string& name, bool decode) {
            sat::Engine engine(name.c_str());
            if (initial) a.assert_fsm_init(engine, 0);
            for (unsigned t = 0; t <= n; ++t) {
                checkpoint(Phase::encoding);
                a.assert_fsm_invar(engine, t);
                for (auto& u : assumptions)
                    a.assert_formula(engine, t, u);
                if (!initial && t < n) a.assert_formula(engine, t, good);
                if (t < n) a.assert_fsm_trans(engine, t);
                if (decode) trace::allocate_state(engine, t);
            }
            a.assert_formula(engine, n, bad);
            auto status = engine.solve();
            if (status == sat::STATUS_UNKNOWN) {
                if (context.stop == StopReason::none) context.cancel(StopReason::solver_unknown);
                throw Cancelled();
            }
            if (decode && status == sat::STATUS_SAT) {
                auto w = trace::decode(engine, n);
                auto artifact = trace::export_trace(*w, spec, r.identity);
                // This is a step-obligation assignment, never a replay-valid INIT trace.
                r.proof["induction_counterexample"]["trace"] = artifact;
                r.proof["induction_counterexample"]["reachable"] = "not_established";
                r.proof["induction_counterexample"]["meaning"] = "Arbitrary states satisfying the property before a violating successor; INIT was not asserted";
            }
            return status;
        };
        r.proof["induction_depth"] = depth;
        r.proof_method = "k-induction";
        auto status = obligation(false, depth, "induction-step", true);
        r.proof["step_status"] = status == sat::STATUS_UNSAT ? "unsatisfiable" : "satisfiable";
        if (status == sat::STATUS_SAT) return;

        // Recheck all proof obligations in fresh solvers without incremental goal groups.
        r.proof["verified_base_depths"] = Json::arrayValue;
        for (unsigned n = 0; n <= depth; ++n) {
            if (obligation(true, n, "verify-induction-base", false) != sat::STATUS_UNSAT)
                throw std::runtime_error("Induction base failed independent recheck");
            r.proof["verified_base_depths"].append(n);
        }
        if (obligation(false, depth, "verify-induction-step", false) != sat::STATUS_UNSAT)
            throw std::runtime_error("Induction step failed independent recheck");
        r.proof["verified"] = true;
        r.proof["verification"] = "fresh-solvers";
        r.status = ExecutionStatus::completed;
        r.outcome = Outcome::proven;
        r.scope = "unbounded";
        r.reason = StopReason::none;
        r.complete = true;
    }
} // namespace query

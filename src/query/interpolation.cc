#include <algorithms/reach/interpolation.hh>
#include <query/trace.hh>
#include <symb/symb_iter.hh>
#include <symb/classes.hh>
#include <memory>

namespace query {
namespace {
namespace imc = reach::interpolation;
Json::Value invariant(const imc::StateFormula& formula, const QuerySpec& spec, const Json::Value& identity)
{
    Json::Value artifact;
    artifact["version"] = 1;
    artifact["format"] = "yasmv-state-invariant";
    artifact["identity"] = identity;
    artifact["symbols"] = trace::symbol_catalog();
    artifact["target"] = source::print(spec.target);
    artifact["assumptions"] = spec_json(spec)["assumptions"];
    artifact["bits"] = Json::arrayValue;
    for (size_t i = 0; i < formula.bits.size(); ++i) {
        checkpoint(Phase::encoding);
        const auto& bit = formula.bits[i];
        Json::Value entry;
        entry["atom"] = Json::UInt64(i + 1);
        entry["symbol"] = source::print(bit.expr());
        entry["bit"] = bit.bitno();
        entry["frozen"] = bit.time() == FROZEN;
        artifact["bits"].append(entry);
    }
    artifact["root"] = formula.root;
    artifact["nodes"] = Json::arrayValue;
    formula.circuit.visit(formula.root, [&](sat::Circuit::Ref id, sat::Circuit::Atom atom,
                                          sat::Circuit::Ref left, sat::Circuit::Ref right) {
        checkpoint(Phase::encoding);
        Json::Value node;
        node["id"] = id;
        if (atom) node["atom"] = Json::UInt64(atom);
        else { node["and"] = Json::arrayValue; node["and"].append(left); node["and"].append(right); }
        artifact["nodes"].append(node);
    });
    checkpoint(Phase::encoding);
    return artifact;
}
sat::status_t solve(sat::Engine& engine, QueryContext& context)
{
    const auto status = engine.solve();
    if (status == sat::STATUS_UNKNOWN) {
        if (context.stop == StopReason::none) context.cancel(StopReason::solver_unknown);
        throw Cancelled();
    }
    checkpoint(Phase::decoding);
    return status;
}
expr::Expr_ptr input_value(algorithms::Algorithm& algorithm, sat::Engine& engine, QueryContext& context,
                           type::Type_ptr type, expr::Expr_ptr expression, expr::Expr_ptr scope, unsigned frame)
{
    checkpoint(Phase::decoding);
    auto& em = expr::ExprMgr::INSTANCE();
    const auto test = [&](expr::Expr_ptr condition) {
        sat::StatePredicate predicate(algorithm.compiler(), condition, scope);
        predicate.emit(engine, frame, true, engine.new_group());
        const bool result = solve(engine, context) == sat::STATUS_SAT;
        engine.invert_last_group();
        return result;
    };
    if (type->is_boolean()) return test(expression) ? em.make_true() : em.make_false();
    if (type->is_enum()) {
        for (auto literal : type->as_enum()->literals())
            if (test(em.make_eq(expression, literal))) return literal;
        throw std::logic_error("Effective input has no legal enum value");
    }
    if (type->is_algebraic()) {
        const auto width = type->as_algebraic()->width();
        if (!width || width > 64) throw std::invalid_argument("Interpolation input width must be between 1 and 64");
        uint64_t value = 0;
        const auto zero = em.make_cast(type->repr(), em.make_const(0));
        for (unsigned i = 0; i < width; ++i) {
            const auto mask = em.make_cast(type->repr(), em.make_const(static_cast<value_t>(uint64_t(1) << i)));
            if (test(em.make_ne(em.make_bw_and(expression, mask), zero))) value |= uint64_t(1) << i;
        }
        if (type->is_signed_algebraic() && width < 64 && (value & (uint64_t(1) << (width - 1))))
            value |= ~((uint64_t(1) << width) - 1);
        return em.make_const(static_cast<value_t>(value));
    }
    if (type->is_array()) {
        expr::Expr_ptr elements = nullptr;
        for (unsigned i = type->as_array()->nelems(); i > 0; --i) {
            const auto value = input_value(algorithm, engine, context, type->as_array()->of(),
                                          em.make_subscript(expression, em.make_const(i - 1)), scope, frame);
            elements = elements ? em.make_array_comma(value, elements) : value;
        }
        return em.make_array(elements);
    }
    throw std::invalid_argument("Interpolation traces require finite effective inputs");
}
witness::Witness_ptr decode(const imc::System& system, const imc::Path& path, QueryContext& context)
{
    // Pin the verified semantic bits in a fresh native model before using the
    // standard decoder. This includes all state values and effective inputs.
    sat::Engine engine("interpolation-decode");
    system.initial(engine, 0);
    for (unsigned t = 0; t < path.size(); ++t) {
        checkpoint(Phase::decoding);
        if (t) system.transition(engine, t - 1);
        trace::allocate_state(engine, t);
        for (size_t i = 0; i < system.bits().size(); ++i) {
            checkpoint(Phase::decoding);
            const auto& bit = system.bits()[i];
            const auto var = engine.tcbi_to_var(enc::TCBI(enc::UCBI(bit.expr(), bit.time(), bit.bitno()), t));
            engine.add_clause({sat::mkLit(var, !path[t][i])});
        }
    }
    system.target(engine, path.size() - 1);
    if (solve(engine, context) != sat::STATUS_SAT) throw std::logic_error("Interpolation path failed native decoding recheck");
    std::unique_ptr<witness::Witness> witness(trace::decode(engine, path.size() - 1, false));
    algorithms::Algorithm algorithm(model::ModelMgr::INSTANCE().model());
    symb::SymbIter symbols(algorithm.model());
    while (symbols.has_next()) {
        checkpoint(Phase::decoding);
        const auto [scope, symbol] = symbols.next();
        if (!symbol->is_variable() || !symbol->as_variable().is_input()) continue;
        const auto key = algorithm.em().make_dot(scope, symbol->name());
        for (unsigned t = 0; t < path.size(); ++t)
            (*witness)[t].set_value(key, input_value(algorithm, engine, context, symbol->as_variable().type(), symbol->name(), scope, t));
    }
    return witness.release();
}
} // namespace

void interpolation_reach(const QuerySpec& spec, QueryResult& r, QueryContext& context)
{
    r.strategy = context.selected_strategy = "interpolation";
    r.scope = spec.operation == Operation::prove_property ? "through_depth" : "unbounded";
    imc::Limits limits;
    if (spec.operation == Operation::prove_property) {
        if (spec.limits.depth < 1) throw std::invalid_argument("Interpolation proof requires a positive depth");
        limits.horizon = spec.limits.depth - 1;
    }
    algorithms::Algorithm algorithm(model::ModelMgr::INSTANCE().model());
    imc::ModelSystem system(algorithm, spec.target, spec.assumptions);
    auto result = imc::search(system, limits);
    const auto& stats = result.statistics;
    r.checked_depths = context.checked_depths = stats.checked_depths;
    auto& data = r.statistics["interpolation"];
    data["horizon"] = stats.horizon;
    data["images"] = Json::UInt64(stats.images);
    data["enlargements"] = Json::UInt64(stats.enlargements);
    data["restarts"] = Json::UInt64(stats.restarts);
    data["concrete_sat"] = Json::UInt64(stats.concrete_sat);
    data["spurious_sat"] = Json::UInt64(stats.spurious_sat);
    data["proof_nodes"] = Json::UInt64(stats.proof_nodes);
    data["circuit_nodes"] = Json::UInt64(stats.circuit_nodes);
    if (result.outcome == imc::Outcome::unknown) {
        if (result.stop == imc::Stop::horizon_limit && spec.operation == Operation::prove_property &&
            r.checked_depths.size() == static_cast<uint64_t>(spec.limits.depth) + 1 &&
            r.checked_depths.back() == spec.limits.depth) {
            r.status = ExecutionStatus::completed;
            r.outcome = Outcome::unreachable;
            r.scope = "through_depth";
            r.reason = StopReason::depth_limit;
            r.complete = true;
            r.proof_method = "bounded-exhaustion";
            return;
        }
        r.reason = result.query_stop == StopReason::none ? StopReason::solver_unknown : result.query_stop;
        return;
    }
    if (!result.verified) throw std::logic_error("Interpolation returned an unverified conclusion");
    if (result.outcome == imc::Outcome::reachable) {
        r.witness = decode(system, result.path, context);
        const unsigned depth = result.path.size() - 1;
        r.optimality["criterion"] = "transitions";
        r.optimality["certified"] = true;
        r.optimality["depth"] = depth;
        r.optimality["unsat_depths"] = Json::arrayValue;
        for (unsigned d = 0; d < depth; ++d) { checkpoint(Phase::decoding); r.optimality["unsat_depths"].append(d); }
        r.optimality["method"] = "increasing-depth-exhaustion";
        r.proof_method = "bounded-counterexample";
        r.outcome = Outcome::reachable;
    } else {
        if (!result.invariant) throw std::logic_error("Interpolation proof lacks an invariant");
        auto artifact = invariant(*result.invariant, spec, r.identity);
        r.proof["invariant"] = std::move(artifact);
        r.proof["assumptions"] = spec_json(spec)["assumptions"];
        r.proof["vacuous"] = result.vacuous;
        r.proof["initial_satisfiable"] = !result.vacuous;
        r.proof["verification"] = "fresh-solvers";
        for (auto name : {"initial_containment", "transition_closure", "target_exclusion"})
            r.proof["obligations"][name] = "unsatisfiable";
        r.proof["verified"] = true;
        r.proof_method = "interpolation";
        r.scope = "unbounded";
        r.outcome = Outcome::unreachable;
    }
    checkpoint(Phase::encoding);
    r.status = ExecutionStatus::completed;
    r.reason = StopReason::none;
    r.complete = true;
}
} // namespace query

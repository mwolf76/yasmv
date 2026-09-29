#define BOOST_TEST_DYN_LINK
#include <boost/test/unit_test.hpp>
#include <algorithms/base.hh>
#include <opts/opts_mgr.hh>
#include <parse.hh>
#include <sat/interpolation.hh>

namespace {
using namespace sat;
void load()
{
    static bool ready = [] {
        const char* args[] = {"interpolation-tests"};
        opts::OptsMgr::INSTANCE().parse_command_line(1, args);
        auto& mm = model::ModelMgr::INSTANCE();
        mm.begin_load();
        if (!parse::parseFile("tests/models/interpolation.smv") || !mm.analyze())
            throw std::runtime_error("Interpolation fixture failed");
        return true;
    }();
    (void)ready;
}
expr::Expr_ptr expression(const char* source)
{
    auto result = parse::parseExpression(source);
    if (!result) throw std::runtime_error("Test expression failed to parse");
    return result;
}
auto scope() { return expr::ExprMgr::INSTANCE().make_empty(); }
auto bit(const char* name, unsigned frame)
{
    return enc::TCBI(enc::UCBI(expr::ExprMgr::INSTANCE().make_dot(scope(), expression(name)), 0, 0), frame);
}
StatePredicate predicate(algorithms::Algorithm& a, const char* text)
{
    return StatePredicate(a.compiler(), expression(text), scope());
}
} // namespace

BOOST_AUTO_TEST_CASE(proof_engine_lifecycle_and_result_contracts)
{
    load();
    Engine e("proof-lifecycle", Engine::Mode::proof);
    auto x = e.new_sat_var();
    BOOST_CHECK_THROW(e.add_clause({mkLit(x)}), std::logic_error);
    BOOST_CHECK_THROW(e.new_group(), std::logic_error);
    BOOST_CHECK_THROW(e.set_groups({0}), std::logic_error);
    BOOST_CHECK_THROW(e.invert_last_group(), std::logic_error);
    BOOST_CHECK_THROW(e.enable_cnf_optimization(), std::logic_error);
    e.add_proof_clause({mkLit(x), mkLit(x, true)}, proof::Partition::a); // ignored tautology
    e.add_proof_clause({mkLit(x), mkLit(x)}, proof::Partition::a);
    e.add_proof_clause({mkLit(x, true)}, proof::Partition::b);
    BOOST_REQUIRE(e.solve() == STATUS_UNSAT);
    BOOST_CHECK(e.resolution_proof().nodes().at(e.proof_root()).clause.empty());
    BOOST_CHECK_THROW(e.new_sat_var(), std::logic_error);
    BOOST_CHECK_THROW(e.solve(), std::logic_error);
    BOOST_CHECK_THROW(e.resolution_proof(), std::logic_error);

    Engine interrupted("proof-interrupted", Engine::Mode::proof);
    interrupted.interrupt();
    BOOST_CHECK(interrupted.solve() == STATUS_UNKNOWN);
    BOOST_CHECK_THROW(interrupted.proof_root(), std::logic_error);
    Engine limited("proof-budget", Engine::Mode::proof);
    limited.configure(0, -1);
    BOOST_CHECK(limited.solve() == STATUS_UNKNOWN);
    BOOST_CHECK_THROW(limited.proof_root(), std::logic_error);
    Engine poisoned("proof-node-limit", Engine::Mode::proof, 1);
    const auto p = poisoned.new_sat_var();
    BOOST_CHECK_THROW(poisoned.add_proof_clause({mkLit(p)}, proof::Partition::a), std::length_error);
    BOOST_CHECK_THROW(poisoned.resolution_proof(), std::logic_error);
}

BOOST_AUTO_TEST_CASE(exhaustive_partition_projection_oracle)
{
    load();
    size_t unsat = 0, sat = 0;
    // All 16 Boolean relations between shared x and one private variable,
    // independently on each side (256 pairs). Oracle projects private bits.
    for (unsigned mask_a = 0; mask_a < 16; ++mask_a) for (unsigned mask_b = 0; mask_b < 16; ++mask_b) {
        Engine a("oracle-a", Engine::Mode::record), b("oracle-b", Engine::Mode::record);
        auto relation = [&](Engine& engine, unsigned mask) {
            const auto x = engine.tcbi_to_var(bit("x", 1)), local = engine.new_sat_var();
            for (unsigned row = 0; row < 4; ++row)
                if (!(mask & (1u << row))) engine.add_clause({mkLit(x, row & 1), mkLit(local, row & 2)});
        };
        relation(a, mask_a); relation(b, mask_b);
        const auto project = [](unsigned mask, unsigned x) { return bool(mask & ((1u << x) | (1u << (x + 2)))); };
        bool expected_sat = false;
        for (unsigned x = 0; x < 2; ++x) expected_sat |= project(mask_a, x) && project(mask_b, x);
        PartitionedCnf cnf(a, b, 1);
        auto result = compute_interpolant(cnf);
        BOOST_REQUIRE(result.status == (expected_sat ? STATUS_SAT : STATUS_UNSAT));
        if (expected_sat) { ++sat; BOOST_CHECK(!result.verified); continue; }
        ++unsat;
        BOOST_REQUIRE(result.verified);
        for (unsigned x = 0; x < 2; ++x) {
            const bool value = result.circuit.evaluate(result.root, [&](Circuit::Atom atom) {
                BOOST_CHECK_EQUAL(result.state_bits.at(atom).absolute_time(), 0);
                return bool(x);
            });
            BOOST_CHECK(!project(mask_a, x) || value);
            BOOST_CHECK(!project(mask_b, x) || !value);
        }
    }
    BOOST_CHECK(sat > 0 && unsat > 0);
}

BOOST_AUTO_TEST_CASE(partition_isolation_arithmetic_mux_arrays_and_enums)
{
    load(); algorithms::Algorithm algorithm(model::ModelMgr::INSTANCE().model());
    const char* formulas[] = {"n + 1 = 3", "(x ? n : (n + 1)) = 3",
                             "bits[x ? 1 : 0]", "mode = GREEN"};
    for (auto formula : formulas) {
        auto p = predicate(algorithm, formula);
        Engine a("compiled-a", Engine::Mode::record), b("compiled-b", Engine::Mode::record);
        p.emit(a, 1); p.emit(b, 1, false);
        PartitionedCnf cnf(a, b, 1);
        auto result = compute_interpolant(cnf);
        BOOST_REQUIRE(result.status == STATUS_UNSAT && result.verified);
        for (const auto& [atom, semantic] : result.state_bits) {
            (void)atom;
            BOOST_CHECK_EQUAL(semantic.absolute_time(), 0);
        }
        Engine replay("reencode-interpolant");
        emit_interpolant(replay, result, 7);
        p.emit(replay, 7, false);
        BOOST_CHECK(replay.solve() == STATUS_UNSAT);
        Engine shifted("distinct-frames");
        emit_interpolant(shifted, result, 7);
        p.emit(shifted, 8, false);
        BOOST_CHECK(shifted.solve() == STATUS_SAT);

        // Reusing the very same compiled units in both partitions must not
        // share their DD/Tseitin or compiler temporary variables.
        Engine same_a("same-unit-a", Engine::Mode::record), same_b("same-unit-b", Engine::Mode::record);
        p.emit(same_a, 1); p.emit(same_b, 1);
        BOOST_CHECK(compute_interpolant(PartitionedCnf(same_a, same_b, 1)).status == STATUS_SAT);
    }
}

BOOST_AUTO_TEST_CASE(state_predicate_polarities_and_eligibility)
{
    load(); algorithms::Algorithm a(model::ModelMgr::INSTANCE().model());
    const auto arithmetic = predicate(a, "n + 1 = 3");
    for (unsigned value = 0; value < 8; ++value) for (bool positive : {false, true}) {
        Engine e("predicate-polarity");
        arithmetic.emit(e, 0, positive);
        predicate(a, ("n = " + std::to_string(value)).c_str()).emit(e, 0);
        BOOST_CHECK(e.solve() == ((positive == (value == 2)) ? STATUS_SAT : STATUS_UNSAT));
    }
    for (auto text : {"next(x)", "future", "choice", "@0{x}", "n"})
        BOOST_CHECK_THROW(predicate(a, text), std::invalid_argument);
}

BOOST_AUTO_TEST_CASE(emission_does_not_mutate_shared_dd_ownership)
{
    load(); algorithms::Algorithm algorithm(model::ModelMgr::INSTANCE().model());
    const auto unit = algorithm.compiler().process(scope(), expression("(x ? n : (n + 1)) = 3"));
    std::map<const DdNode*, unsigned> references;
    const auto remember = [&](const ADD& value) { references[value.getNode()] = value.getNode()->ref; };
    const auto vector = [&](const dd::DDVector& values) { for (const auto& value : values) remember(value); };
    vector(unit.dds());
    for (const auto& descriptor : unit.inlined_operator_descriptors()) {
        vector(descriptor.z()); vector(descriptor.x()); vector(descriptor.y());
    }
    for (const auto& [key, descriptors] : unit.binary_selection_descriptors_map()) {
        (void)key;
        for (const auto& descriptor : descriptors) {
            vector(descriptor.z()); vector(descriptor.x()); vector(descriptor.y());
            remember(descriptor.cnd()); remember(descriptor.aux());
        }
    }
    BOOST_REQUIRE(!references.empty());
    query::QueryContext context; query::ContextScope current(context);
    size_t observations = 0;
    context.checkpoint_hook = [&](query::Phase phase) {
        if (phase != query::Phase::encoding) return;
        ++observations;
        // Checking during emission catches temporary ADD copies, whose CUDD
        // reference updates would race between parallel readers of this unit.
        for (const auto& [node, count] : references) BOOST_REQUIRE_EQUAL(static_cast<unsigned>(node->ref), count);
    };
    for (auto mode : {Engine::Mode::normal, Engine::Mode::record}) {
        Engine engine("shared-unit-reader", mode);
        engine.push(unit, 0);
        engine.push(unit, 1);
    }
    BOOST_CHECK(observations > 0);
}

BOOST_AUTO_TEST_CASE(frozen_bits_and_interface_rejection)
{
    load(); algorithms::Algorithm a(model::ModelMgr::INSTANCE().model());
    const auto frozen = predicate(a, "fixed_bit");
    Engine left("frozen-a", Engine::Mode::record), right("frozen-b", Engine::Mode::record);
    frozen.emit(left, 2); frozen.emit(right, 17, false);
    auto result = compute_interpolant(PartitionedCnf(left, right, 1));
    BOOST_REQUIRE(result.verified);
    BOOST_REQUIRE_EQUAL(result.state_bits.size(), 1);
    BOOST_CHECK_EQUAL(result.state_bits.begin()->second.time(), FROZEN);
    Engine replay("frozen-renaming");
    emit_interpolant(replay, result, 12); frozen.emit(replay, 28, false);
    BOOST_CHECK(replay.solve() == STATUS_UNSAT);

    Engine wrong_a("wrong-cut-a", Engine::Mode::record), wrong_b("wrong-cut-b", Engine::Mode::record);
    predicate(a, "x").emit(wrong_a, 0); predicate(a, "!x").emit(wrong_b, 0);
    BOOST_CHECK_THROW(PartitionedCnf(wrong_a, wrong_b, 1), std::invalid_argument);
    BOOST_CHECK_THROW(PartitionedCnf(wrong_a, wrong_a, 0), std::invalid_argument);
}

BOOST_AUTO_TEST_CASE(group_assumptions_are_local_and_materialized)
{
    load(); algorithms::Algorithm algorithm(model::ModelMgr::INSTANCE().model());
    auto positive = algorithm.compiler().process(scope(), expression("x"));
    auto negative = algorithm.compiler().process(scope(), expression("!x"));
    Engine a("group-a", Engine::Mode::record), b("group-b", Engine::Mode::record);
    a.push(positive, 0, a.new_group());
    b.push(negative, 0, b.new_group());
    b.invert_last_group();
    BOOST_CHECK(compute_interpolant(PartitionedCnf(a, b, 0)).status == STATUS_SAT);
    b.invert_last_group();
    BOOST_CHECK(compute_interpolant(PartitionedCnf(a, b, 0)).verified);
    BOOST_CHECK_THROW(a.enable_cnf_optimization(), std::logic_error);
    Engine ordinary("ordinary-recording-rejected");
    BOOST_CHECK_THROW(ordinary.recorded_clauses(), std::logic_error);
}

BOOST_AUTO_TEST_CASE(craig_validation_rejects_mutated_predicates)
{
    load(); algorithms::Algorithm a(model::ModelMgr::INSTANCE().model());
    Engine left("mutated-a", Engine::Mode::record), right("mutated-b", Engine::Mode::record);
    predicate(a, "x").emit(left, 0); predicate(a, "!x").emit(right, 0);
    PartitionedCnf cnf(left, right, 0);
    Circuit circuit;
    BOOST_CHECK(cnf.verify(circuit, Circuit::True) == STATUS_SAT);
    BOOST_CHECK(cnf.verify(circuit, Circuit::False) == STATUS_SAT);
    BOOST_CHECK_THROW(cnf.verify(circuit, circuit.atom(999)), std::invalid_argument);
    auto result = compute_interpolant(cnf);
    BOOST_REQUIRE(result.verified);
    BOOST_CHECK(cnf.verify(result.circuit, result.circuit.negate(result.root)) == STATUS_SAT);
}

BOOST_AUTO_TEST_CASE(cancellation_and_limits_never_publish_an_interpolant)
{
    load(); algorithms::Algorithm a(model::ModelMgr::INSTANCE().model());
    Engine left("cancel-a", Engine::Mode::record), right("cancel-b", Engine::Mode::record);
    predicate(a, "x").emit(left, 0); predicate(a, "!x").emit(right, 0);
    PartitionedCnf cnf(left, right, 0);
    BOOST_CHECK_THROW(compute_interpolant(cnf, {1, 100}), std::length_error);
    BOOST_CHECK_THROW(compute_interpolant(cnf, {10000, 0}), std::length_error);
    for (unsigned stop_at : {1, 2, 3}) {
        query::QueryContext context;
        query::ContextScope current(context);
        unsigned solves = 0;
        context.checkpoint_hook = [&](query::Phase phase) {
            if (phase == query::Phase::solving && ++solves == stop_at) context.cancel();
        };
        BOOST_CHECK_THROW(compute_interpolant(cnf), query::Cancelled);
        BOOST_CHECK(context.stop == query::StopReason::cancelled);
    }
    {
        query::QueryLimits limits; limits.conflicts = 0;
        query::QueryContext context(limits); query::ContextScope current(context);
        const auto result = compute_interpolant(cnf);
        BOOST_CHECK(result.status == STATUS_UNKNOWN && !result.verified);
    }
    BOOST_CHECK(compute_interpolant(cnf).verified);
}

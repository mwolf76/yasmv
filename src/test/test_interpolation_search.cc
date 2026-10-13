#define BOOST_TEST_DYN_LINK
#include <boost/test/unit_test.hpp>
#include <algorithms/reach/interpolation.hh>
#include <opts/opts_mgr.hh>
#include <parse.hh>
#include <queue>
#include <env/environment.hh>
#include <query/query.hh>

namespace {
using namespace reach::interpolation;
using namespace sat;
void load()
{
    static bool ready = [] {
        const char* args[] = {"interpolation-search-tests", "--root", "main"};
        opts::OptsMgr::INSTANCE().parse_command_line(3, args);
        auto& mm = model::ModelMgr::INSTANCE();
        mm.begin_load();
        if (!parse::parseFile("tests/models/interpolation-search.smv") || !mm.analyze())
            throw std::runtime_error("Interpolation search fixture failed");
        return true;
    }();
    (void)ready;
}
expr::Expr_ptr expression(const char* text)
{
    auto result = parse::parseExpression(text);
    if (!result) throw std::runtime_error("Invalid test expression");
    return result;
}
auto scope() { return expr::ExprMgr::INSTANCE().make_empty(); }
enc::TCBI bit(const char* name)
{
    return enc::TCBI(enc::UCBI(expr::ExprMgr::INSTANCE().make_dot(scope(), expression(name)), 0, 0), 0);
}
State state(unsigned value, size_t width)
{
    State result;
    for (size_t i = 0; i < width; ++i) result.push_back(value & (1u << i));
    return result;
}
unsigned number(const State& value)
{
    unsigned result = 0;
    for (size_t i = 0; i < value.size(); ++i) if (value[i]) result |= 1u << i;
    return result;
}
// An independent truth-table CNF emitter; no model compiler or search helpers.
class Graph : public System {
public:
    Graph(unsigned count, unsigned edges, unsigned init, unsigned target)
        : count(count), edges(edges), init(init), bad(target), dictionary{bit("x")}
    { if (count > 2) dictionary.push_back(bit("y")); }
    const Bits& bits() const override { return dictionary; }
    bool edge(unsigned a, unsigned b) const { return edges & (1u << (a * count + b)); }
    void initial(Engine& e, step_t frame, bool positive = true, group_t guard = MAINGROUP) const override
    { states(e, frame, positive ? init : (~init & ((1u << (1u << dictionary.size())) - 1)), guard); }
    void target(Engine& e, step_t frame, group_t guard = MAINGROUP) const override
    { states(e, frame, bad, guard); }
    void transition(Engine& e, step_t frame, group_t guard = MAINGROUP) const override
    {
        unsigned size = 1u << dictionary.size();
        for (unsigned a = 0; a < size; ++a) for (unsigned b = 0; b < size; ++b) {
            if (a < count && b < count && edge(a, b)) continue;
            Lits clause{mkLit(guard, true)};
            row(e, frame, a, clause); row(e, frame + 1, b, clause);
            e.add_clause(clause);
        }
    }
    void pin(Engine& e, step_t frame, unsigned value) const
    {
        for (size_t i = 0; i < dictionary.size(); ++i)
            e.add_clause({mkLit(variable(e, frame, i), !(value & (1u << i)))});
    }
    int distance() const
    {
        std::queue<unsigned> todo;
        std::vector<int> distances(count, -1);
        for (unsigned i = 0; i < count; ++i) if (init & (1u << i)) { todo.push(i); distances[i] = 0; }
        while (!todo.empty()) {
            auto from = todo.front(); todo.pop();
            if (bad & (1u << from)) return distances[from];
            for (unsigned to = 0; to < count; ++to) if (edge(from, to) && distances[to] < 0) {
                distances[to] = distances[from] + 1; todo.push(to);
            }
        }
        return -1;
    }
    unsigned count, edges, init, bad;
private:
    Bits dictionary;
    Var variable(Engine& e, step_t frame, size_t index) const
    {
        const auto& b = dictionary[index];
        return e.tcbi_to_var(enc::TCBI(enc::UCBI(b.expr(), b.time(), b.bitno()), frame));
    }
    void row(Engine& e, step_t frame, unsigned value, Lits& clause) const
    {
        for (size_t i = 0; i < dictionary.size(); ++i)
            clause.push_back(mkLit(variable(e, frame, i), value & (1u << i)));
    }
    void states(Engine& e, step_t frame, unsigned mask, group_t guard) const
    {
        for (unsigned value = 0; value < (1u << dictionary.size()); ++value) if (!(mask & (1u << value))) {
            Lits clause{mkLit(guard, true)}; row(e, frame, value, clause); e.add_clause(clause);
        }
    }
};
void no_certificate(const Result& result)
{
    BOOST_CHECK(result.outcome == Outcome::unknown);
    BOOST_CHECK(!result.verified);
    BOOST_CHECK(result.path.empty());
    BOOST_CHECK(!result.invariant);
}
} // namespace

BOOST_AUTO_TEST_CASE(exhaustive_finite_graph_search_matches_bfs)
{
    load();
    unsigned restarts = 0, growth = 0, concrete = 0, systems = 0;
    Limits limits; limits.horizon = 3; limits.images = 64;
    for (unsigned count : {2u, 3u})
        for (unsigned edges = 0; edges < (1u << (count * count)); ++edges)
            for (unsigned init = 0; init < (1u << count); ++init)
                for (unsigned bad = 0; bad < (1u << count); ++bad) {
                    BOOST_TEST_CONTEXT("states=" << count << " edges=" << edges << " init=" << init << " target=" << bad) {
                        Graph graph(count, edges, init, bad);
                        const int distance = graph.distance();
                        auto result = search(graph, limits);
                        BOOST_REQUIRE(result.verified);
                        BOOST_REQUIRE(result.outcome == (distance < 0 ? Outcome::unreachable : Outcome::reachable));
                        BOOST_CHECK(result.stop == Stop::none);
                        for (unsigned i = 0; i < result.statistics.checked_depths.size(); ++i)
                            BOOST_CHECK_EQUAL(result.statistics.checked_depths[i], i);
                        if (distance >= 0) {
                            BOOST_REQUIRE_EQUAL(result.path.size(), unsigned(distance + 1));
                            BOOST_CHECK_EQUAL(result.statistics.checked_depths.size(), result.path.size());
                            BOOST_CHECK(!result.invariant);
                            BOOST_CHECK(init & (1u << number(result.path.front())));
                            BOOST_CHECK(bad & (1u << number(result.path.back())));
                            for (size_t i = 0; i < result.path.size(); ++i) {
                                BOOST_CHECK_LT(number(result.path[i]), count);
                                if (i) BOOST_CHECK(graph.edge(number(result.path[i - 1]), number(result.path[i])));
                            }
                        } else {
                            BOOST_REQUIRE(result.invariant);
                            BOOST_CHECK_EQUAL(result.vacuous, !init);
                            BOOST_CHECK(result.path.empty());
                            for (unsigned a = 0; a < count; ++a) {
                                const bool inside = result.invariant->evaluate(state(a, graph.bits().size()));
                                if (init & (1u << a)) BOOST_CHECK(inside);
                                if (bad & (1u << a)) BOOST_CHECK(!inside);
                                if (inside) for (unsigned b = 0; b < count; ++b)
                                    if (graph.edge(a, b)) BOOST_CHECK(result.invariant->evaluate(state(b, graph.bits().size())));
                            }
                        }
                        if (!restarts && result.statistics.restarts)
                            BOOST_TEST_MESSAGE("First restart: " << count << ", " << edges << ", " << init << ", " << bad);
                        restarts += result.statistics.restarts;
                        growth += result.statistics.enlargements;
                        concrete += result.statistics.concrete_sat;
                        ++systems;
                    }
                }
    BOOST_CHECK_EQUAL(systems, 33024u);
    BOOST_CHECK_GT(restarts, 0u); BOOST_CHECK_GT(growth, 0u); BOOST_CHECK_GT(concrete, 0u);
}

BOOST_AUTO_TEST_CASE(exhaustive_suffix_includes_short_deadlocked_paths)
{
    load();
    for (unsigned count : {2u, 3u})
        for (unsigned edges = 0; edges < (1u << (count * count)); ++edges)
            for (unsigned bad = 0; bad < (1u << count); ++bad)
                for (unsigned start = 0; start < count; ++start) {
                    Graph graph(count, edges, 1u << start, bad);
                    const auto distance = graph.distance();
                    for (unsigned horizon = 0; horizon <= count; ++horizon) {
                        Engine e("suffix-oracle");
                        emit_suffix(graph, e, 1, horizon); graph.pin(e, 1, start);
                        BOOST_TEST_CONTEXT("states=" << count << " edges=" << edges << " target=" << bad << " start=" << start << " horizon=" << horizon) {
                            BOOST_REQUIRE(e.solve() == (distance >= 0 && unsigned(distance) <= horizon ? STATUS_SAT : STATUS_UNSAT));
                        }
                    }
                }
}

BOOST_AUTO_TEST_CASE(native_model_search_and_assumptions)
{
    load(); algorithms::Algorithm algorithm(model::ModelMgr::INSTANCE().model());
    BOOST_REQUIRE(algorithm.ok());
    for (const auto& [target, distance] : std::vector<std::pair<const char*, int>>{
             {"TRUE", 0}, {"n = 1 && mode = GREEN", 1}, {"n = 3", 3},
             {"n = 4", -1}, {"sub.flag != fixed_bit", -1}, {"FALSE", -1},
             {"!(mode = RED || mode = GREEN || mode = BLUE)", -1},
             {"n = 2 && cells[1]", 2},
             {"!(palette[0] = RED || palette[0] = GREEN || palette[0] = BLUE)", -1}}) {
        BOOST_TEST_CONTEXT(target) {
            ModelSystem system(algorithm, expression(target));
            auto result = search(system);
            BOOST_REQUIRE(result.verified);
            BOOST_REQUIRE(result.outcome == (distance < 0 ? Outcome::unreachable : Outcome::reachable));
            if (distance >= 0) {
                BOOST_REQUIRE_EQUAL(result.path.size(), unsigned(distance + 1));
                BOOST_CHECK(verify_path(system, result.path) == STATUS_SAT);
            } else BOOST_CHECK(verify_invariant(system, *result.invariant) == STATUS_UNSAT);
        }
    }
    for (const auto& [assumption, target, expected, vacuous] : std::vector<std::tuple<const char*, const char*, Outcome, bool>>{
             {"n < 2", "n = 2", Outcome::unreachable, false},
             {"n < 2", "n = 1", Outcome::reachable, false},
             {"n = 7", "TRUE", Outcome::unreachable, true}}) {
        ModelSystem system(algorithm, expression(target), {expression(assumption)});
        auto result = search(system);
        BOOST_REQUIRE(result.verified); BOOST_CHECK(result.outcome == expected); BOOST_CHECK_EQUAL(result.vacuous, vacuous);
    }
    // The suffix must remain satisfiable at a bad deadlock, even with horizon 5.
    ModelSystem deadlock(algorithm, expression("n = 3"));
    Engine suffix("native-deadlock-suffix");
    StatePredicate(algorithm.compiler(), expression("n = 3"), scope()).emit(suffix, 1);
    emit_suffix(deadlock, suffix, 1, 5);
    BOOST_CHECK(suffix.solve() == STATUS_SAT);
}

BOOST_AUTO_TEST_CASE(semantic_eligibility_rejects_hidden_nonlocal_state)
{
    load(); algorithms::Algorithm algorithm(model::ModelMgr::INSTANCE().model());
    for (const char* text : {"future", "distant", "choice", "next(x)", "view.value"}) {
        BOOST_CHECK_THROW(ModelSystem(algorithm, expression(text)), std::invalid_argument);
        BOOST_CHECK_THROW(ModelSystem(algorithm, expression("TRUE"), {expression(text)}), std::invalid_argument);
    }
    BOOST_CHECK_THROW(TransitionRelation(algorithm.compiler(), expression("distant"), scope()), std::invalid_argument);
    BOOST_CHECK_THROW(TransitionRelation(algorithm.compiler(), expression("distant_view.value"), scope()), std::invalid_argument);
    auto& environment = env::Environment::INSTANCE();
    environment.set(expression("gate"), expression("future"));
    BOOST_CHECK_THROW(ModelSystem(algorithm, expression("gate")), std::invalid_argument);
    environment.set(expression("gate"), expression("choice"));
    BOOST_CHECK_THROW(ModelSystem(algorithm, expression("gate")), std::invalid_argument);
    environment.set(expression("gate"), expression("x"));
    ModelSystem input(algorithm, expression("gate"));
    auto reached = search(input);
    BOOST_REQUIRE(reached.verified);
    BOOST_CHECK(reached.outcome == Outcome::reachable);
    BOOST_CHECK_EQUAL(reached.path.size(), 2u);
    environment.set(expression("gate"), nullptr);
    BOOST_CHECK_NO_THROW(TransitionRelation(algorithm.compiler(), expression("next(x) = {TRUE, FALSE}"), scope()));
}

BOOST_AUTO_TEST_CASE(certificates_are_independently_rechecked)
{
    load();
    Graph safe(3, (1u << 1) | (1u << 4), 1, 4); // 0 -> 1 -> 1, bad 2
    auto result = search(safe);
    BOOST_REQUIRE(result.invariant);
    auto candidate = *result.invariant;
    candidate.root = Circuit::False;
    BOOST_CHECK(verify_invariant(safe, candidate) == STATUS_SAT); // excludes INIT
    candidate.root = Circuit::True;
    BOOST_CHECK(verify_invariant(safe, candidate) == STATUS_SAT); // contains target
    candidate.root = candidate.circuit.conjunction(candidate.circuit.negate(candidate.circuit.atom(1)),
                                                   candidate.circuit.negate(candidate.circuit.atom(2)));
    BOOST_CHECK(verify_invariant(safe, candidate) == STATUS_SAT); // not closed
    candidate.root = candidate.circuit.atom(3);
    BOOST_CHECK_THROW(verify_invariant(safe, candidate), std::invalid_argument);
    candidate = *result.invariant; candidate.bits.pop_back();
    BOOST_CHECK_THROW(verify_invariant(safe, candidate), std::invalid_argument);

    Graph reachable(3, (1u << 1) | (1u << 5), 1, 4); // 0 -> 1 -> 2 -> deadlock
    auto witness = search(reachable);
    BOOST_REQUIRE_EQUAL(witness.path.size(), 3u);
    auto mutated = witness.path; mutated[1] = state(0, 2);
    BOOST_CHECK(verify_path(reachable, mutated) == STATUS_UNSAT);
    mutated = witness.path; mutated.front() = state(1, 2);
    BOOST_CHECK(verify_path(reachable, mutated) == STATUS_UNSAT);
    mutated = witness.path; mutated.back() = state(1, 2);
    BOOST_CHECK(verify_path(reachable, mutated) == STATUS_UNSAT);
    BOOST_CHECK_THROW(verify_path(reachable, {}), std::invalid_argument);
    mutated = witness.path; mutated[1].pop_back();
    BOOST_CHECK_THROW(verify_path(reachable, mutated), std::invalid_argument);
}

BOOST_AUTO_TEST_CASE(limits_and_cancellation_never_publish_certificates)
{
    load();
    Graph safe(3, (1u << 1) | (1u << 4), 1, 4);
    Graph reachable(3, (1u << 1) | (1u << 5), 1, 4);
    for (auto event : {Event::concrete, Event::initial_projection, Event::image, Event::inclusion,
                       Event::growth, Event::restart, Event::verify_initial, Event::verify_transition,
                       Event::verify_target, Event::verify_path}) {
        bool hit = false;
        query::QueryContext context; query::ContextScope current(context);
        const auto& graph = (event == Event::restart || event == Event::verify_path) ? reachable : safe;
        auto result = search(graph, {}, [&](Event observed) { if (observed == event) { hit = true; context.cancel(); } });
        BOOST_TEST_CONTEXT("event=" << int(event)) {
            BOOST_REQUIRE(hit); no_certificate(result);
            BOOST_CHECK(result.stop == Stop::interrupted);
            BOOST_CHECK(result.query_stop == query::StopReason::cancelled);
            BOOST_CHECK(context.checked_depths.empty());
        }
    }
    for (unsigned cap = 0; cap < 5; ++cap) {
        Limits limits;
        if (cap == 0) limits.images = 0;
        if (cap == 1) limits.horizon = 0;
        if (cap == 2) limits.invariant_nodes = 0;
        if (cap == 3) limits.interpolation.proof_nodes = 1;
        if (cap == 4) limits.interpolation.circuit_nodes = 0;
        auto result = search(reachable, limits); no_certificate(result);
        BOOST_CHECK(result.stop == (cap == 0 ? Stop::image_limit : cap == 1 ? Stop::horizon_limit : Stop::node_limit));
    }
    for (unsigned budget = 0; budget < 3; ++budget) {
        query::QueryLimits limits;
        if (budget == 0) limits.conflicts = 0;
        if (budget == 1) limits.propagations = 0;
        if (budget == 2) limits.wall_ms = 0;
        query::QueryContext context(limits); query::ContextScope current(context);
        no_certificate(search(safe));
    }
    BOOST_CHECK(search(safe).verified); BOOST_CHECK(search(reachable).verified);
}

BOOST_AUTO_TEST_CASE(query_input_decoding_cancellation_has_no_artifact)
{
    load();
    auto& environment = env::Environment::INSTANCE();
    environment.set(expression("gate"), expression("x"));
    struct ResetInput { ~ResetInput() { env::Environment::INSTANCE().set(expression("gate"), nullptr); } } reset;
    query::QuerySpec spec;
    spec.operation = query::Operation::reach;
    spec.strategy = "interpolation";
    spec.target = expression("n = 2");
    query::QueryContext measured;
    std::map<query::Phase, unsigned> counts;
    measured.checkpoint_hook = [&](query::Phase phase) { ++counts[phase]; };
    BOOST_REQUIRE(query::execute(spec, measured).outcome == query::Outcome::reachable);
    for (auto phase : {query::Phase::solving, query::Phase::decoding}) {
        BOOST_REQUIRE_GT(counts[phase], 0u);
        query::QueryContext context;
        unsigned count = 0;
        context.checkpoint_hook = [&](query::Phase p) {
            if (p == phase && ++count == counts[phase]) context.cancel();
        };
        auto result = query::execute(spec, context);
        BOOST_CHECK(result.status == query::ExecutionStatus::unknown);
        BOOST_CHECK(result.trace.isNull());
        BOOST_CHECK(result.optimality.isNull());
        BOOST_CHECK(result.proof.isNull());
        BOOST_CHECK(!result.witness);
    }
    BOOST_CHECK(query::execute(spec).outcome == query::Outcome::reachable);
}

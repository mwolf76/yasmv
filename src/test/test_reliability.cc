#define BOOST_TEST_DYN_LINK
#include <boost/test/unit_test.hpp>

#include <algorithms/fsm/fsm.hh>
#include <algorithms/sim/simulation.hh>
#include <cmd/cmd.hh>
#include <cmd/commands/commands.hh>
#include <model/module.hh>
#include <sat/engine.hh>
#include <parse.hh>

namespace {
class TestCommand : public cmd::Command {
public:
    TestCommand() : Command(cmd::Interpreter::INSTANCE()) {}
    utils::Variant operator()() override { return utils::Variant(cmd::okMessage); }
};

void clause(sat::Engine& engine, std::initializer_list<Minisat::Lit> literals)
{
    Minisat::vec<Minisat::Lit> values;
    for (auto literal : literals) values.push(literal);
    engine.add_clause(values);
}
}

BOOST_AUTO_TEST_CASE(incremental_solver)
{
    // Run this executable in a fresh process for every supported option tuple.
    const char* switches[] = { "cnf-tautology-removal", "cnf-duplicate-removal", "cnf-subsumption" };
    const char* settings = std::getenv("YASMV_TEST_CNF");
    std::vector<std::string> args { "reliability" };
    if (settings) {
        for (size_t i = 0; i < 3; ++i) {
            args.push_back(std::string("--") + switches[i]);
            args.push_back(settings[i] == '1' ? "yes" : "no");
        }
    }
    std::vector<const char*> argv;
    for (const auto& arg : args) argv.push_back(arg.c_str());
    opts::OptsMgr::INSTANCE().parse_command_line(argv.size(), argv.data());

    sat::Engine engine("incremental-test");
    const auto x = engine.new_sat_var(true);
    const auto y = engine.new_sat_var(true);
    const auto group = engine.new_group();
    // group -> x, including duplicates, tautologies, and an unsorted superset.
    clause(engine, { Minisat::mkLit(group, true), Minisat::mkLit(x) });
    clause(engine, { Minisat::mkLit(x), Minisat::mkLit(group, true) });
    clause(engine, { Minisat::mkLit(y), Minisat::mkLit(x), Minisat::mkLit(group, true) });
    clause(engine, { Minisat::mkLit(y), Minisat::mkLit(y, true) });
    BOOST_REQUIRE(engine.solve() == sat::STATUS_SAT);
    BOOST_CHECK_EQUAL(engine.value(x), 1);
    engine.invert_last_group();
    clause(engine, { Minisat::mkLit(x, true) });
    BOOST_REQUIRE(engine.solve() == sat::STATUS_SAT);
    BOOST_CHECK_EQUAL(engine.value(x), 0);
    engine.invert_last_group();
    BOOST_CHECK(engine.solve() == sat::STATUS_UNSAT);
    const auto failed = engine.failed_groups();
    BOOST_CHECK(std::find(failed.begin(), failed.end(), group) != failed.end());
    engine.invert_last_group();
    BOOST_CHECK(engine.solve() == sat::STATUS_SAT);
    BOOST_CHECK(engine.failed_groups().empty());
    clause(engine, {});
    BOOST_CHECK(engine.solve() == sat::STATUS_UNSAT);

    sat::Engine interrupted("interrupted-test");
    const auto z = interrupted.new_sat_var(true);
    clause(interrupted, { Minisat::mkLit(z), Minisat::mkLit(z, true) });
    interrupted.interrupt();
    BOOST_CHECK(interrupted.solve() == sat::STATUS_UNKNOWN);
    BOOST_CHECK(interrupted.failed_groups().empty());
}

BOOST_AUTO_TEST_CASE(algorithm_status_and_enumeration)
{
    auto& em = expr::ExprMgr::INSTANCE();
    auto& mm = model::ModelMgr::INSTANCE();
    auto& tm = type::TypeMgr::INSTANCE();
    auto& module = *new model::Module(em.make_identifier("main"));
    mm.model().add_module(module);
    for (const char* name : {"x", "y"}) {
        auto id = em.make_identifier(name);
        module.add_var(id, new symb::Variable(module.name(), id, tm.find_boolean()));
    }
    BOOST_REQUIRE(mm.analyze());
    // Independently compiled units must never alias their temporary encodings.
    // This models a cached transition system plus a fresh query compiler.
    {
        compiler::Compiler first, second;
        auto initial = first.process(em.make_empty(), parse::parseExpression("(x ? 1 : 0) = 0"));
        auto goal = second.process(em.make_empty(), parse::parseExpression("!((x ? 1 : 0) != 0)"));
        sat::Engine combined("independent-compilers");
        combined.push(initial, 0);
        combined.push(goal, 0);
        BOOST_CHECK(combined.solve() == sat::STATUS_SAT);
        auto opposite = second.process(em.make_empty(), parse::parseExpression("(x ? 1 : 0) != 0"));
        combined.push(opposite, 0);
        BOOST_CHECK(combined.solve() == sat::STATUS_UNSAT);
    }
    TestCommand command;
    const sat::SolveCallback unknown = [](sat::Engine&) { return sat::STATUS_UNKNOWN; };

    fsm::CheckTransConsistency check(mm.model());
    check.process({}, unknown);
    BOOST_CHECK(check.status() == fsm::FSM_CONSISTENCY_UNDECIDED);
    check.set_limit(2);
    unsigned calls = 0;
    check.process({}, [&calls](sat::Engine& engine) {
        return ++calls == 1 ? engine.solve() : sat::STATUS_UNKNOWN;
    });
    BOOST_CHECK(check.status() == fsm::FSM_CONSISTENCY_UNDECIDED);
    check.process({});
    BOOST_CHECK(check.status() == fsm::FSM_CONSISTENCY_OK);
    check.set_limit(0);
    BOOST_CHECK_THROW(check.process({}), model::SemanticError);

    sim::Simulation simulation(mm.model());
    auto result = simulation.pick_state({}, false, true, -1, unknown);
    BOOST_CHECK_EQUAL(result.count, 0);
    BOOST_CHECK(!result.complete());
    BOOST_CHECK(result.stop == sim::EnumerationStop::unknown);

    calls = 0;
    result = simulation.pick_state({}, false, true, -1, [&calls](sat::Engine& engine) {
        return ++calls == 1 ? engine.solve() : sat::STATUS_UNKNOWN;
    });
    BOOST_CHECK_EQUAL(result.count, 1);
    BOOST_CHECK(!result.complete());
    result = simulation.pick_state({}, false, true, 1);
    BOOST_CHECK_EQUAL(result.count, 1);
    BOOST_CHECK(result.stop == sim::EnumerationStop::limit);
    result = simulation.pick_state({}, false, true, -1);
    BOOST_CHECK_EQUAL(result.count, 4);
    BOOST_CHECK(result.complete());
    auto& wm = witness::WitnessMgr::INSTANCE();
    const auto previous_traces = wm.witnesses().size();
    result = simulation.pick_state({}, true, false, 1);
    BOOST_CHECK_EQUAL(result.count, 1);
    BOOST_CHECK_EQUAL(wm.witnesses().size(), previous_traces + 1);
    BOOST_CHECK_EQUAL(wm.witnesses().back()->size(), 1);
    BOOST_CHECK_THROW(simulation.pick_state({}, false, true, 0), model::SemanticError);
}

BOOST_AUTO_TEST_CASE(variant_copy_assignment)
{
    utils::Variant result;
    for (const auto& value : { utils::Variant(), utils::Variant(std::string("ERROR")),
                              utils::Variant(true), utils::Variant(42) }) {
        result = value;
        BOOST_CHECK_EQUAL(result.is_nil(), value.is_nil());
        if (value.is_string()) BOOST_CHECK_EQUAL(result.as_string(), value.as_string());
        if (value.is_boolean()) BOOST_CHECK_EQUAL(result.as_boolean(), value.as_boolean());
        if (value.is_integer()) BOOST_CHECK_EQUAL(result.as_integer(), value.as_integer());
    }
}

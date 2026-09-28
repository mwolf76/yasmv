#define BOOST_TEST_DYN_LINK
#include <boost/test/unit_test.hpp>

#include <algorithms/fsm/fsm.hh>
#include <algorithms/sim/simulation.hh>
#include <cmd/cmd.hh>
#include <cmd/commands/commands.hh>
#include <model/module.hh>
#include <sat/engine.hh>
#include <sat/logging.hh>
#include <sat/inlining.hh>
#include <parse.hh>
#include <jsoncpp/json/json.h>
#include <fstream>
#include <sstream>

#ifdef Minisat_SolverTypes_h
#error "Engine clients must not include MiniSat headers transitively"
#endif

namespace {
class TestCommand : public cmd::Command {
public:
    TestCommand() : Command(cmd::Interpreter::INSTANCE()) {}
    utils::Variant operator()() override { return utils::Variant(cmd::okMessage); }
};

void clause(sat::Engine& engine, std::initializer_list<sat::Lit> literals)
{
    sat::Lits values;
    for (auto literal : literals) values.push_back(literal);
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

    // Main group zero is a real positive literal, not a clause terminator.
    sat::Engine main_group("main-group-test");
    BOOST_REQUIRE_EQUAL(main_group.groups().size(), 1);
    BOOST_CHECK_EQUAL(main_group.groups().front(), sat::MAINGROUP);
    const sat::Lits main_clause {sat::mkLit(0, true)};
    main_group.add_clause(main_clause);
    BOOST_CHECK(main_clause == sat::Lits({sat::mkLit(0, true)}));
    BOOST_CHECK(main_group.solve() == sat::STATUS_UNSAT);
    const auto main_core = main_group.failed_groups();
    BOOST_CHECK(std::find(main_core.begin(), main_core.end(), 0) != main_core.end());

    sat::Engine engine("incremental-test");
    const auto x = engine.new_sat_var(true);
    const auto y = engine.new_sat_var(true);
    const auto group = engine.new_group();
    const sat::Lits unsorted {sat::mkLit(x), sat::mkLit(group, true), sat::mkLit(x)};
    const auto original = unsorted;
    engine.add_clause(unsorted);
    BOOST_CHECK(unsorted == original);
    // group -> x, including duplicates, tautologies, and an unsorted superset.
    clause(engine, { sat::mkLit(group, true), sat::mkLit(x) });
    clause(engine, { sat::mkLit(x), sat::mkLit(group, true) });
    clause(engine, { sat::mkLit(y), sat::mkLit(x), sat::mkLit(group, true) });
    clause(engine, { sat::mkLit(y), sat::mkLit(y, true) });
    BOOST_REQUIRE(engine.solve() == sat::STATUS_SAT);
    BOOST_CHECK_EQUAL(engine.value(x), 1);
    engine.invert_last_group();
    clause(engine, { sat::mkLit(x, true) });
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
    clause(interrupted, { sat::mkLit(z), sat::mkLit(z, true) });
    interrupted.interrupt();
    BOOST_CHECK(interrupted.solve() == sat::STATUS_UNKNOWN);
    BOOST_CHECK(interrupted.failed_groups().empty());

    sat::Engine negative_group("negative-group-test");
    const auto disabled = negative_group.new_group();
    clause(negative_group, {sat::mkLit(disabled)});
    negative_group.invert_last_group();
    BOOST_REQUIRE(negative_group.solve() == sat::STATUS_UNSAT);
    const auto negative_core = negative_group.failed_groups();
    BOOST_CHECK(std::find(negative_core.begin(), negative_core.end(), -disabled) != negative_core.end());
    negative_group.invert_last_group();
    BOOST_CHECK(negative_group.solve() == sat::STATUS_SAT);

    // Logging must handle empty vectors without unsigned size underflow.
    std::ostringstream logged;
    sat::operator<<(logged, sat::Lits{});
    BOOST_CHECK(logged.str().empty());
    sat::operator<<(logged, sat::Lits{sat::mkLit(0), sat::mkLit(0, true), sat::mkLit(3)});
    BOOST_CHECK_EQUAL(logged.str(), "0 -0 3");
}

BOOST_AUTO_TEST_CASE(packed_microcode_loading)
{
    const auto home = std::getenv("YASMV_HOME");
    BOOST_REQUIRE(home);
    for (const auto name : {"u-add-8.json", "s-add-8.json", "u-mul-4.json", "s-lt-8.json"}) {
        const auto path = boost::filesystem::path(home) / "microcode" / name;
        std::ifstream input(path.string());
        BOOST_REQUIRE(input.good());
        Json::Value document;
        input >> document;
        const auto& packed = document["cnf"];
        sat::InlinedOperatorLoader loader(path);
        const auto& clauses = loader.clauses();
        BOOST_REQUIRE_EQUAL(clauses.size(), packed.size());
        for (Json::ArrayIndex i = 0; i < packed.size(); ++i) {
            BOOST_REQUIRE_EQUAL(clauses[i].size(), packed[i].size());
            for (Json::ArrayIndex j = 0; j < packed[i].size(); ++j) {
                const int encoded = packed[i][j].asInt();
                BOOST_CHECK_EQUAL(sat::toInt(clauses[i][j]), encoded);
                BOOST_CHECK_EQUAL(sat::var(clauses[i][j]), encoded / 2);
                BOOST_CHECK_EQUAL(sat::sign(clauses[i][j]), bool(encoded % 2));
            }
        }
    }
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

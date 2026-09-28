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
#include <limits>
#include <thread>
#include <random>
#include <set>
#include <type_traits>

#ifdef Minisat_SolverTypes_h
#error "Engine clients must not include MiniSat headers transitively"
#endif

static_assert(std::is_same_v<decltype(std::declval<sat::Engine&>().groups()), const sat::Groups&>);

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

void pigeonhole(sat::Engine& engine, unsigned holes = 8)
{
    std::vector<std::vector<sat::Var>> variables(holes + 1);
    for (auto& pigeon : variables) {
        sat::Lits clause;
        for (unsigned hole = 0; hole < holes; ++hole) {
            pigeon.push_back(engine.new_sat_var(true));
            clause.push_back(sat::mkLit(pigeon.back()));
        }
        engine.add_clause(clause);
    }
    for (unsigned hole = 0; hole < holes; ++hole)
        for (unsigned p = 0; p <= holes; ++p)
            for (unsigned q = p + 1; q <= holes; ++q)
                engine.add_clause({sat::mkLit(variables[p][hole], true),
                                   sat::mkLit(variables[q][hole], true)});
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

BOOST_AUTO_TEST_CASE(cadical_result_lifetime_and_limits)
{
    sat::Engine engine("result-lifetime");
    const auto x = engine.new_sat_var(true);
    engine.add_clause({sat::mkLit(x)});
    BOOST_REQUIRE(engine.solve() == sat::STATUS_SAT);
    BOOST_CHECK_EQUAL(engine.value(x), 1);
    const auto y = engine.new_sat_var(true);
    BOOST_CHECK(engine.status() == sat::STATUS_UNKNOWN);
    BOOST_CHECK(!engine.assigned(x));
    BOOST_CHECK_THROW(engine.value(x), std::logic_error);
    BOOST_REQUIRE(engine.solve() == sat::STATUS_SAT);
    BOOST_CHECK(engine.assigned(y)); // unused declared bits have complete values.
    engine.add_clause({sat::mkLit(x, true)});
    BOOST_CHECK(!engine.assigned(x));
    BOOST_REQUIRE(engine.solve() == sat::STATUS_UNSAT);
    engine.add_clause({});
    BOOST_CHECK(engine.failed_groups().empty());

    sat::Engine limited("limits");
    limited.configure(0, -1);
    BOOST_CHECK(limited.solve() == sat::STATUS_UNKNOWN);
    limited.configure(-1, 0);
    BOOST_CHECK(limited.solve() == sat::STATUS_UNKNOWN);
    limited.configure(std::numeric_limits<int64_t>::max(), std::numeric_limits<int64_t>::max());
    BOOST_CHECK(limited.solve() == sat::STATUS_SAT);
    limited.configure(-1, -1);
    BOOST_CHECK(limited.solve() == sat::STATUS_SAT);
    BOOST_CHECK_THROW(limited.configure(-2, -1), std::invalid_argument);
    std::thread canceller([&] { limited.interrupt(); });
    canceller.join();
    BOOST_CHECK(limited.solve() == sat::STATUS_UNKNOWN);
    BOOST_CHECK_THROW(limited.value(0), std::logic_error);
}

BOOST_AUTO_TEST_CASE(cadical_search_budgets_and_accounting)
{
    for (bool propagation : {false, true}) {
        query::QueryLimits limits;
        if (propagation) limits.propagations = 1;
        else limits.conflicts = 1;
        query::QueryContext context(limits);
        query::ContextScope scope(context);
        sat::Engine engine("search-budget");
        pigeonhole(engine);
        BOOST_CHECK(engine.solve() == sat::STATUS_UNKNOWN);
        BOOST_CHECK(context.stop == (propagation ? query::StopReason::propagation_budget :
                                                  query::StopReason::conflict_budget));
        BOOST_CHECK((propagation ? context.propagations_used : context.conflicts_used) >= 1);
        BOOST_CHECK(engine.failed_groups().empty());
    }
    query::QueryContext context;
    query::ContextScope scope(context);
    sat::Engine engine("accounting");
    pigeonhole(engine);
    BOOST_REQUIRE(engine.solve() == sat::STATUS_UNSAT);
    const auto conflicts = context.conflicts_used, propagations = context.propagations_used;
    BOOST_CHECK(conflicts > 0);
    BOOST_CHECK(propagations > 0);
    BOOST_CHECK(engine.solve() == sat::STATUS_UNSAT);
    BOOST_CHECK(context.conflicts_used >= conflicts);
    BOOST_CHECK(context.propagations_used >= propagations);
    // An exhausted cumulative budget stops the next solve before a trivial answer.
    context.limits.conflicts = context.conflicts_used;
    BOOST_CHECK(engine.solve() == sat::STATUS_UNKNOWN);
    BOOST_CHECK(context.stop == query::StopReason::conflict_budget);
}

BOOST_AUTO_TEST_CASE(cadical_group_updates_are_transactional)
{
    sat::Engine engine("group-lifetime");
    const auto group = engine.new_group();
    engine.add_clause({sat::mkLit(group)});
    BOOST_REQUIRE(engine.solve() == sat::STATUS_SAT);
    auto groups = engine.groups();
    // Merely inspecting or editing a copy must not invalidate the model.
    groups.back() = -group;
    BOOST_CHECK(engine.assigned(group));
    BOOST_CHECK_THROW(engine.set_groups({0, -group, std::numeric_limits<int>::min()}), std::out_of_range);
    BOOST_CHECK_THROW(engine.set_groups({0, -group, group + 1}), std::out_of_range);
    BOOST_CHECK(engine.assigned(group));
    BOOST_CHECK_EQUAL(engine.groups().back(), group);
    engine.set_groups(groups);
    BOOST_CHECK(!engine.assigned(group));
    BOOST_REQUIRE(engine.solve() == sat::STATUS_UNSAT);
    BOOST_CHECK(!engine.failed_groups().empty());
    engine.set_groups({0, group});
    BOOST_CHECK(engine.failed_groups().empty());
    BOOST_CHECK(engine.status() == sat::STATUS_UNKNOWN);
    BOOST_REQUIRE(engine.solve() == sat::STATUS_SAT);
    BOOST_CHECK_EQUAL(engine.value(group), 1);
}

BOOST_AUTO_TEST_CASE(cadical_small_formula_oracle)
{
    // Independent exhaustive truth tables, not another SAT solver or its choices.
    const auto satisfies = [](unsigned model, const sat::LitsVector& clauses, const sat::Groups& groups) {
        for (auto group : groups)
            if (bool(model & (1u << std::abs(group))) != (group >= 0)) return false;
        for (const auto& clause : clauses) {
            bool holds = false;
            for (auto literal : clause)
                holds |= bool(model & (1u << sat::var(literal))) != sat::sign(literal);
            if (!holds) return false;
        }
        return true;
    };
    const auto possible = [&](const sat::LitsVector& clauses, const sat::Groups& groups) {
        for (unsigned model = 0; model < 256; ++model)
            if (satisfies(model, clauses, groups)) return true;
        return false;
    };
    std::mt19937 random(0xCA01CA1);
    unsigned sat_results = 0, unsat_results = 0;
    for (unsigned trial = 0; trial < 16; ++trial) {
        sat::Engine engine("truth-table");
        for (unsigned bit = 0; bit < 4; ++bit) engine.new_sat_var(true);
        for (unsigned selector = 0; selector < 3; ++selector) engine.new_group();
        const auto all_groups = engine.groups();
        sat::LitsVector clauses;
        // Incremental batches retain learned clauses across every polarity tuple.
        for (unsigned batch = 0; batch < 3; ++batch) {
            for (unsigned i = 0; i < 6; ++i) {
                sat::Lits clause {sat::mkLit(5 + random() % 3, true)};
                for (unsigned j = 0, width = 1 + random() % 3; j < width; ++j)
                    clause.push_back(sat::mkLit(1 + random() % 4, random() % 2));
                clauses.push_back(clause);
                engine.add_clause(clause);
            }
            for (unsigned mask = 0; mask < 8; ++mask) {
                auto groups = all_groups;
                for (unsigned i = 1; i < groups.size(); ++i)
                    if (!(mask & (1u << (i - 1)))) groups[i] = -groups[i];
                engine.set_groups(groups);
                const bool expected = possible(clauses, groups);
                const auto status = engine.solve();
                BOOST_REQUIRE(status == (expected ? sat::STATUS_SAT : sat::STATUS_UNSAT));
                if (expected) {
                    ++sat_results;
                    unsigned model = 0;
                    for (unsigned bit = 0; bit < 8; ++bit) {
                        BOOST_REQUIRE(engine.assigned(bit));
                        model |= unsigned(engine.value(bit)) << bit;
                    }
                    BOOST_CHECK(satisfies(model, clauses, groups));
                    BOOST_CHECK(engine.failed_groups().empty());
                } else {
                    ++unsat_results;
                    const auto core = engine.failed_groups();
                    for (auto group : core)
                        BOOST_CHECK(std::find(groups.begin(), groups.end(), group) != groups.end());
                    BOOST_CHECK(!possible(clauses, core));
                    engine.set_groups(core);
                    BOOST_CHECK(engine.failed_groups().empty());
                    BOOST_CHECK(engine.solve() == sat::STATUS_UNSAT);
                }
            }
        }
    }
    BOOST_CHECK(sat_results > 0);
    BOOST_CHECK(unsat_results > 0);
    BOOST_CHECK_EQUAL(sat_results + unsat_results, 384);
}

BOOST_AUTO_TEST_CASE(cadical_unconstrained_enumeration)
{
    sat::Engine engine("unused-bits");
    std::vector<sat::Var> bits;
    for (unsigned i = 0; i < 4; ++i) bits.push_back(engine.new_sat_var(true));
    std::set<unsigned> seen;
    for (unsigned i = 0; i < 16; ++i) {
        BOOST_REQUIRE(engine.solve() == sat::STATUS_SAT);
        unsigned value = 0;
        sat::Lits block;
        for (unsigned bit = 0; bit < bits.size(); ++bit) {
            BOOST_REQUIRE(engine.assigned(bits[bit]));
            const auto assigned = engine.value(bits[bit]);
            value |= unsigned(assigned) << bit;
            block.push_back(sat::mkLit(bits[bit], assigned));
        }
        BOOST_CHECK(seen.insert(value).second);
        engine.add_clause(block);
        BOOST_CHECK_THROW(engine.value(bits.front()), std::logic_error);
    }
    BOOST_CHECK_EQUAL(seen.size(), 16);
    BOOST_CHECK(engine.solve() == sat::STATUS_UNSAT);
}

BOOST_AUTO_TEST_CASE(cadical_multi_engine_accounting_and_reconfiguration)
{
    query::QueryContext context;
    query::ContextScope scope(context);
    sat::Engine first("first-account"), second("second-account");
    pigeonhole(first);
    pigeonhole(second);
    BOOST_REQUIRE(first.solve() == sat::STATUS_UNSAT);
    const auto conflicts = context.conflicts_used, propagations = context.propagations_used;
    BOOST_REQUIRE(conflicts > 0);
    BOOST_REQUIRE(propagations > 0);
    BOOST_REQUIRE(second.solve() == sat::STATUS_UNSAT);
    BOOST_CHECK(context.conflicts_used > conflicts);
    BOOST_CHECK(context.propagations_used > propagations);
    // Stop reason precedence is first-wins, including cancellation afterwards.
    context.cancel(query::StopReason::conflict_budget);
    context.cancel(query::StopReason::cancelled);
    BOOST_CHECK(context.stop == query::StopReason::conflict_budget);
}

BOOST_AUTO_TEST_CASE(cadical_relative_budgets_and_active_cancellation)
{
    sat::Engine limited("relative-allowance");
    pigeonhole(limited);
    limited.configure(1, -1);
    BOOST_CHECK(limited.solve() == sat::STATUS_UNKNOWN);
    BOOST_CHECK(limited.solve() == sat::STATUS_UNKNOWN);
    limited.configure(-1, -1);
    BOOST_CHECK(limited.solve() == sat::STATUS_UNSAT);
    {
        query::QueryContext context;
        query::ContextScope scope(context);
        sat::Engine engine("active-cancellation");
        // Commit before starting the canceller so there is no encoding checkpoint
        // between the solving hook and the native call.
        engine.enable_cnf_optimization(false);
        pigeonhole(engine, 13);
        std::atomic<bool> solving {false};
        context.checkpoint_hook = [&](query::Phase phase) {
            if (phase == query::Phase::solving) solving.store(true);
        };
        std::jthread canceller([&] {
            while (!solving.load()) std::this_thread::yield();
            std::this_thread::sleep_for(std::chrono::milliseconds(10));
            context.cancel();
        });
        auto status = sat::STATUS_UNKNOWN;
        try { status = engine.solve(); }
        catch (const query::Cancelled&) {
            // A descheduled solving thread can receive cancellation at the
            // last checkpoint before native entry. This is inconclusive too.
        }
        canceller.join();
        BOOST_CHECK(status == sat::STATUS_UNKNOWN);
        BOOST_CHECK(context.stop == query::StopReason::cancelled);
        BOOST_CHECK(engine.failed_groups().empty());
        BOOST_CHECK(!engine.assigned(0));
    }
    query::QueryContext fresh;
    query::ContextScope scope(fresh);
    sat::Engine recovered("after-cancellation");
    BOOST_CHECK(recovered.solve() == sat::STATUS_SAT);
    BOOST_CHECK(fresh.stop == query::StopReason::none);
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

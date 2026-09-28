// Standalone contracts for the pinned CaDiCaL release; no yasmv backend yet.
#include <cadical.hpp>

#include <atomic>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <initializer_list>
#include <iostream>
#include <set>
#include <stdexcept>
#include <thread>
#include <vector>

namespace {
using CaDiCaL::Solver;
constexpr int SAT = 10, UNSAT = 20, UNKNOWN = 0;

// Checks must remain enabled when testing a release library with -DNDEBUG.
#define CHECK(condition) do { if (!(condition)) throw std::runtime_error(#condition); } while (false)

void configure(Solver& solver, bool search_only = false)
{
    CHECK(solver.set("quiet", 1));
    CHECK(solver.set("seed", 7));
    CHECK(solver.set("factorcheck", 2));
    if (search_only) {
        CHECK(solver.configure("plain"));
        CHECK(solver.set("lucky", 0));
        CHECK(solver.set("walk", 0));
        CHECK(solver.set("terminateint", 0));
    }
}

void clause(Solver& solver, std::initializer_list<int> literals)
{
    for (int literal : literals) {
        CHECK(literal != 0);
        solver.add(literal);
    }
    solver.add(0);
}

// An independently specified UNSAT search problem, with no initial units.
void pigeonhole(Solver& solver, int holes)
{
    std::vector<std::vector<int>> variables(holes + 1);
    for (auto& pigeon : variables)
        for (int h = 0; h < holes; ++h)
            pigeon.push_back(solver.declare_one_more_variable());
    for (const auto& pigeon : variables) {
        for (int variable : pigeon) solver.add(variable);
        solver.add(0);
    }
    for (int h = 0; h < holes; ++h)
        for (int p = 0; p <= holes; ++p)
            for (int q = p + 1; q <= holes; ++q)
                clause(solver, {-variables[p][h], -variables[q][h]});
}

void version_and_configuration()
{
    // rel-3.0.1 still has CADICAL_PATCH == 0 in its header.
    CHECK(std::strcmp(Solver::version(), "3.0.1") == 0);
    Solver solver;
    configure(solver);
    CHECK(solver.get("seed") == 7);
    CHECK(!solver.set("yasmv-invalid-option", 1));
    CHECK(!solver.limit("propagations", 1));
    CHECK(solver.is_valid_limit("conflicts"));
    CHECK(solver.get_statistic_value("yasmv-invalid-statistic") == -1);
    std::cout << "CaDiCaL " << Solver::version() << '\n';
}

void allocation_and_freezing()
{
    Solver solver;
    configure(solver);
    CHECK(solver.vars() == 0);
    int first = solver.declare_one_more_variable();
    CHECK(first == 1); // yasmv's internal variable zero needs a mapping.
    int last = solver.declare_more_variables(3);
    CHECK(last == first + 3);
    CHECK(solver.vars() == last);
    solver.freeze(first);
    solver.freeze(-first);
    CHECK(solver.frozen(first));
    solver.melt(first);
    CHECK(solver.frozen(first)); // freeze is reference-counted.
    solver.melt(-first);
    CHECK(!solver.frozen(first));
    clause(solver, {first});
    CHECK(solver.solve() == SAT);
    CHECK(solver.val(first) == first);
    int next = solver.declare_one_more_variable();
    CHECK(next > last);
    CHECK(solver.state() != CaDiCaL::SATISFIED);
    clause(solver, {-next});
    CHECK(solver.solve() == SAT);
    CHECK(solver.val(next) == -next);
}

void incremental_selectors()
{
    Solver solver;
    configure(solver);
    int main = solver.declare_one_more_variable();
    int group = solver.declare_one_more_variable();
    int value = solver.declare_one_more_variable();
    solver.freeze(group);
    solver.freeze(value);
    clause(solver, {-group, value});
    solver.assume(main);
    solver.assume(group);
    CHECK(solver.solve() == SAT);
    CHECK(solver.val(value) == value);
    clause(solver, {-value});
    CHECK(solver.state() != CaDiCaL::SATISFIED);
    solver.assume(main);
    solver.assume(-group);
    CHECK(solver.solve() == SAT);
    CHECK(solver.val(value) == -value);
    solver.assume(main);
    solver.assume(group);
    CHECK(solver.solve() == UNSAT);
    CHECK(solver.failed(group));
    CHECK(!solver.failed(main));
    CHECK(!solver.failed(-group));
    solver.assume(-group);
    CHECK(solver.solve() == SAT);
    clause(solver, {});
    CHECK(solver.solve() == UNSAT);
}

void signed_cores_and_assumption_reset()
{
    for (int sign : {-1, 1}) {
        Solver solver;
        configure(solver);
        int x = solver.declare_one_more_variable();
        int y = solver.declare_one_more_variable();
        int irrelevant = solver.declare_one_more_variable();
        clause(solver, {-sign * x, -sign * y});
        std::vector<int> assumptions {sign * x, sign * y, irrelevant};
        for (int literal : assumptions) solver.assume(literal);
        CHECK(solver.solve() == UNSAT);
        std::vector<int> core;
        for (int literal : assumptions)
            if (solver.failed(literal)) core.push_back(literal);
        CHECK(core == std::vector<int>({sign * x, sign * y}));
        // Copy before any state-changing operation, then recheck the core.
        for (int literal : core) solver.assume(literal);
        CHECK(solver.solve() == UNSAT);
        CHECK(solver.solve() == SAT); // assumptions do not persist.
        solver.assume(x);
        solver.assume(-x);
        CHECK(solver.solve() == UNSAT);
        CHECK(solver.failed(x));
        CHECK(solver.failed(-x));
        CHECK(solver.solve() == SAT);
    }
}

void unconstrained_model_enumeration()
{
    Solver solver;
    configure(solver);
    int x = solver.declare_one_more_variable();
    int y = solver.declare_one_more_variable();
    std::set<int> models;
    for (int i = 0; i < 4; ++i) {
        CHECK(solver.solve() == SAT);
        int vx = solver.val(x), vy = solver.val(y);
        CHECK(std::abs(vx) == x);
        CHECK(std::abs(vy) == y);
        CHECK(solver.val(-x) == vx);
        CHECK(models.insert((vx > 0) + 2 * (vy > 0)).second);
        clause(solver, {-vx, -vy});
    }
    CHECK(models == std::set<int>({0, 1, 2, 3}));
    CHECK(solver.solve() == UNSAT);
}

void preprocessing_and_extension_safe_allocation()
{
    Solver solver;
    configure(solver);
    CHECK(solver.set("factor", 1));
    int x = solver.declare_one_more_variable();
    int y = solver.declare_one_more_variable();
    clause(solver, {x, y});
    clause(solver, {-x, -y});
    int status = solver.simplify(3);
    CHECK(status == SAT || status == UNKNOWN);
    CHECK(solver.solve() == SAT);
    CHECK((solver.val(x) > 0) != (solver.val(y) > 0));
    const int previous_max = solver.vars();
    int fresh = solver.declare_one_more_variable();
    CHECK(fresh > previous_max);
    clause(solver, {fresh});
    clause(solver, {x}); // reuse potentially preprocessed, unfrozen variables.
    CHECK(solver.solve() == SAT);
    CHECK(solver.val(x) == x);
    CHECK(solver.val(y) == -y);
    CHECK(solver.val(fresh) == fresh);
    clause(solver, {y});
    CHECK(solver.solve() == UNSAT);
}

void conflict_limits_and_counters()
{
    Solver solver;
    configure(solver, true);
    pigeonhole(solver, 6);
    CHECK(solver.limit("conflicts", 0));
    CHECK(solver.solve() == UNKNOWN);
    auto before = solver.get_statistic_value("conflicts");
    auto initial = before;
    int64_t used = 0;
    for (int i = 0; i < 3; ++i) {
        CHECK(solver.limit("conflicts", 1));
        CHECK(solver.solve() == UNKNOWN);
        auto after = solver.get_statistic_value("conflicts");
        CHECK(after > before);
        used += after - before;
        before = after;
    }
    CHECK(used == before - initial);
    CHECK(solver.get_statistic_value("propagations") > 0);
    CHECK(solver.get_statistic_value("decisions") > 0);
    CHECK(solver.get_statistic_value("clauses") >= 0);
    // No limit call: a previous solve's limit must not leak into this solve.
    CHECK(solver.solve() == UNSAT);
    CHECK(solver.get_statistic_value("conflicts") > before);
}

class FlagTerminator : public CaDiCaL::Terminator {
public:
    std::atomic<bool> requested {false};
    unsigned calls = 0;
    bool terminate() override { ++calls; return requested.load(); }
};

void pre_requested_termination_and_reuse()
{
    FlagTerminator terminator; // outlives the solver's connection.
    Solver solver;
    configure(solver, true);
    pigeonhole(solver, 6);
    terminator.requested = true;
    solver.connect_terminator(&terminator);
    CHECK(solver.solve() == UNKNOWN);
    CHECK(terminator.calls > 0);
    terminator.requested = false;
    CHECK(solver.solve() == UNSAT);
    solver.disconnect_terminator();
}

class HandshakeTerminator : public CaDiCaL::Terminator {
public:
    std::atomic<bool> entered {false}, requested {false};
    bool terminate() override
    {
        entered = true;
        // Deterministic test synchronization, not production callback behavior.
        while (!requested.load()) std::this_thread::yield();
        return true;
    }
};

void cross_thread_cancellation()
{
    HandshakeTerminator terminator;
    Solver solver;
    configure(solver, true);
    pigeonhole(solver, 6);
    solver.connect_terminator(&terminator);
    std::atomic<bool> finished {false};
    std::thread canceller([&] {
        while (!terminator.entered.load() && !finished.load())
            std::this_thread::yield();
        terminator.requested = true; // this thread never touches the solver.
    });
    int status = solver.solve();
    finished = true;
    canceller.join();
    CHECK(terminator.entered.load());
    CHECK(status == UNKNOWN);
    solver.disconnect_terminator();
    CHECK(solver.solve() == UNSAT);
}

class PropagationTerminator : public CaDiCaL::Terminator {
public:
    Solver& solver;
    int64_t baseline;
    bool reached = false;
    explicit PropagationTerminator(Solver& value)
        : solver(value), baseline(value.get_statistic_value("propagations")) {}
    bool terminate() override
    {
        reached = solver.get_statistic_value("propagations") - baseline >= 1;
        return reached;
    }
};

void cooperative_propagation_limit()
{
    Solver solver;
    configure(solver, true);
    pigeonhole(solver, 6);
    PropagationTerminator terminator(solver);
    solver.connect_terminator(&terminator);
    int status = solver.solve();
    solver.disconnect_terminator(); // terminator was constructed after solver.
    CHECK(status == UNKNOWN);
    CHECK(terminator.reached);
    auto used = solver.get_statistic_value("propagations") - terminator.baseline;
    CHECK(used >= 1); // callback granularity permits overshoot.
    std::cout << "Propagation threshold 1 stopped after " << used << '\n';
    CHECK(solver.solve() == UNSAT);
}
} // namespace

int main()
{
    const std::vector<std::pair<const char*, std::function<void()>>> tests {
        {"version and configuration", version_and_configuration},
        {"allocation and freezing", allocation_and_freezing},
        {"incremental selectors", incremental_selectors},
        {"signed cores and assumption reset", signed_cores_and_assumption_reset},
        {"unconstrained model enumeration", unconstrained_model_enumeration},
        {"preprocessing and extension-safe allocation", preprocessing_and_extension_safe_allocation},
        {"conflict limits and counters", conflict_limits_and_counters},
        {"pre-requested termination and reuse", pre_requested_termination_and_reuse},
        {"cross-thread cancellation", cross_thread_cancellation},
        {"cooperative propagation limit", cooperative_propagation_limit},
    };
    for (const auto& [name, test] : tests) {
        try {
            test();
            std::cout << "PASS: " << name << std::endl;
        } catch (const std::exception& error) {
            std::cerr << "FAIL: " << name << ": " << error.what() << std::endl;
            return 1;
        }
    }
    std::cout << "All " << tests.size() << " CaDiCaL API tests passed" << std::endl;
}

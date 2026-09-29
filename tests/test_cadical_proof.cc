// Standalone proof feasibility gate; production solving is unchanged.
#include <cadical.hpp>
#include <tracer.hpp>
#include <sat/proof.hh>

#include <algorithm>
#include <climits>
#include <cstring>
#include <functional>
#include <iostream>
#include <optional>
#include <random>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

namespace {
using namespace sat::proof;
#define CHECK(condition) do { if (!(condition)) throw std::runtime_error(#condition); } while (false)

class Probe : public CaDiCaL::Tracer {
public:
    ResolutionProof proof;
    std::string error;
    std::optional<Partition> submitting;
    Clause submitted;
    size_t originals = 0, derived = 0, deletions = 0, queries = 0;
    std::optional<NodeId> conclusion;

    // Do not unwind through CaDiCaL internals. A callback error poisons the
    // entire probe, and is reported after control returns from the solver.
    template<class F> void event(F fn) noexcept
    {
        if (!error.empty()) return;
        try { fn(); }
        catch (const std::exception& e) { error = e.what(); }
    }
    void check() const { if (!error.empty()) throw std::runtime_error(error); }
    void add_original_clause(int64_t id, bool, const Clause& clause, bool restored) override
    {
        event([&] {
            if (restored) { proof.restore(id, clause); return; }
            CHECK(submitting.has_value());
            CHECK(std::set<int>(clause.begin(), clause.end()) ==
                  std::set<int>(submitted.begin(), submitted.end()));
            proof.original(id, clause, *submitting);
            submitting.reset();
            ++originals;
        });
    }
    void add_derived_clause(int64_t id, bool, int witness, const Clause& clause,
                            const std::vector<int64_t>& hints) override
    {
        event([&] { proof.derive(id, clause, hints, witness); ++derived; });
    }
    void delete_clause(int64_t id, bool, const Clause& clause) override
    {
        event([&] { proof.erase(id, clause); ++deletions; });
    }
    void conclude_unsat(CaDiCaL::ConclusionType type, const std::vector<int64_t>& ids) override
    {
        event([&] {
            CHECK(type == CaDiCaL::CONFLICT && ids.size() == 1);
            conclusion = proof.conclude(ids.front());
        });
    }
    void report_status(int status, int64_t id) override
    {
        event([&] { if (status == 20 && id) (void)proof.conclude(id); });
    }
    void solve_query() override { event([&] { CHECK(++queries == 1); }); }
    void add_assumption(int) override { event([] { throw std::runtime_error("Native assumptions unsupported; submit partitioned units"); }); }
    void add_constraint(const Clause&) override { event([] { throw std::runtime_error("Native constraint unsupported"); }); }
    void add_assumption_clause(int64_t, const Clause&, const std::vector<int64_t>&) override
    { event([] { throw std::runtime_error("Assumption proof unsupported"); }); }
    void notify_equivalence(int, int) override
    { event([] { throw std::runtime_error("Equivalence notification unsupported"); }); }
    // weaken_minus, strengthen and demote only change solver bookkeeping;
    // they grant no new proof fact. Actual additions/deletions are checked.
};

struct SolverProbe {
    Probe tracer; // outlives solver and is explicitly disconnected
    CaDiCaL::Solver solver;
    SolverProbe()
    {
        CHECK(solver.configure("plain"));
        CHECK(solver.set("quiet", 1));
        CHECK(solver.set("seed", 7));
        CHECK(solver.set("factor", 0));
        CHECK(solver.set("lucky", 0));
        CHECK(solver.set("walk", 0));
        solver.connect_proof_tracer(&tracer, true);
    }
    ~SolverProbe() { solver.disconnect_proof_tracer(&tracer); }
    void add(const Clause& c, Partition partition = Partition::a)
    {
        CHECK(!tracer.submitting);
        tracer.submitted = c;
        tracer.submitting = partition;
        for (int lit : c) { CHECK(lit && lit != INT_MIN); solver.add(lit); }
        solver.add(0);
        tracer.check();
        CHECK(!tracer.submitting);
    }
    int solve()
    {
        const int status = solver.solve();
        tracer.check();
        solver.conclude();
        tracer.check();
        CHECK((status == 20) == tracer.conclusion.has_value());
        return status;
    }
};

// A second checker for the resulting explicit DAG, independent of RUP replay.
void check_dag(const ResolutionProof& proof)
{
    const auto& nodes = proof.nodes();
    for (size_t i = 0; i < nodes.size(); ++i) {
        const auto& n = nodes[i];
        if (n.rule == Rule::original) continue;
        CHECK(n.left < i);
        std::set<int> expected(nodes[n.left].clause.begin(), nodes[n.left].clause.end());
        if (n.rule == Rule::weakening) {
            for (int lit : expected) CHECK(std::count(n.clause.begin(), n.clause.end(), lit));
        } else {
            CHECK(n.right < i && expected.erase(n.pivot) == 1);
            bool pivot_seen = false;
            for (int lit : nodes[n.right].clause) {
                if (lit == -n.pivot) pivot_seen = true;
                else expected.insert(lit);
            }
            CHECK(pivot_seen);
            CHECK(expected == std::set<int>(n.clause.begin(), n.clause.end()));
            for (int lit : expected) CHECK(!expected.count(-lit));
        }
    }
}

void roots_and_units()
{
    SolverProbe empty;
    empty.add({}, Partition::b);
    CHECK(empty.solve() == 20);
    CHECK(empty.tracer.proof.nodes()[*empty.tracer.conclusion].partition == Partition::b);
    SolverProbe units;
    units.add({1}, Partition::a);
    units.add({1}, Partition::b); // same clause, distinct origin and ID
    units.add({-1, 2});
    units.add({-2}, Partition::b);
    CHECK(units.solve() == 20);
    CHECK(units.tracer.originals == 4 && units.tracer.derived > 0);
    CHECK(units.tracer.proof.nodes()[units.tracer.proof.node(1)].partition == Partition::a);
    check_dag(units.tracer.proof);
}

void pigeonholes()
{
    for (int holes = 2; holes <= 5; ++holes) {
        SolverProbe probe;
        auto variable = [holes](int p, int h) { return p * holes + h + 1; };
        for (int p = 0; p <= holes; ++p) {
            Clause at_least_one;
            for (int h = 0; h < holes; ++h) at_least_one.push_back(variable(p, h));
            probe.add(at_least_one, Partition::a);
        }
        for (int h = 0; h < holes; ++h)
            for (int p = 0; p <= holes; ++p)
                for (int q = p + 1; q <= holes; ++q)
                    probe.add({-variable(p, h), -variable(q, h)}, Partition::b);
        CHECK(probe.solve() == 20);
        CHECK(probe.solver.get_statistic_value("conflicts") > 0);
        CHECK(probe.tracer.derived > 0);
        check_dag(probe.tracer.proof);
    }
}

bool satisfiable(const std::vector<Clause>& clauses, unsigned variables)
{
    for (unsigned valuation = 0; valuation < (1u << variables); ++valuation) {
        bool satisfied = true;
        for (const auto& clause : clauses) {
            bool value = false;
            for (int lit : clause)
                value |= bool(valuation & (1u << (std::abs(lit) - 1))) == (lit > 0);
            satisfied &= value;
        }
        if (satisfied) return true;
    }
    return false;
}

void truth_table_oracle()
{
    // Every subset of the eight two-variable unit/binary clauses.
    const std::vector<Clause> pool{{1}, {-1}, {2}, {-2}, {1,2}, {1,-2}, {-1,2}, {-1,-2}};
    size_t sat = 0, unsat = 0;
    for (unsigned mask = 0; mask < (1u << pool.size()); ++mask) {
        SolverProbe probe;
        std::vector<Clause> clauses;
        for (size_t i = 0; i < pool.size(); ++i) if (mask & (1u << i)) {
            clauses.push_back(pool[i]);
            probe.add(pool[i], i % 2 ? Partition::a : Partition::b);
        }
        const bool expected = satisfiable(clauses, 2);
        CHECK(probe.solve() == (expected ? 10 : 20));
        if (expected) ++sat; else ++unsat;
        check_dag(probe.tracer.proof);
    }
    CHECK(sat && unsat);
    // Deterministic larger random formulas, again checked exhaustively.
    std::mt19937 random(391);
    for (int sample = 0; sample < 120; ++sample) {
        SolverProbe probe;
        std::vector<Clause> clauses;
        for (int n = 0; n < 24; ++n) {
            Clause clause;
            for (int v = 1; v <= 5; ++v)
                if (random() % 2) clause.push_back(random() % 2 ? v : -v);
            if (clause.empty()) clause.push_back(1);
            clauses.push_back(clause);
            probe.add(clause, n % 2 ? Partition::a : Partition::b);
        }
        CHECK(probe.solve() == (satisfiable(clauses, 5) ? 10 : 20));
        check_dag(probe.tracer.proof);
    }
}

void weakening_and_lifecycle()
{
    ResolutionProof proof;
    proof.original(1, {1}, Partition::a);
    proof.derive(2, {1, 2}, {1}); // RUP proves a stronger subclause
    CHECK(proof.nodes().back().rule == Rule::weakening);
    proof.erase(1, {1});
    proof.restore(1, {1});
    CHECK(proof.nodes()[proof.node(1)].partition == Partition::a);
    proof.erase(2, {2, 1});
    proof.restore(2, {1, 2}); // restored derived clauses retain their proof
    CHECK(proof.nodes()[proof.node(2)].rule == Rule::weakening);
    proof.original(3, {-1}, Partition::b);
    proof.derive(4, {}, {1, 3});
    (void)proof.conclude(4);
    proof.erase(1, {1}); // DAG ancestry survives deletion
    check_dag(proof);
}

void rejects(const std::function<void()>& operation)
{
    try { operation(); }
    catch (const std::invalid_argument&) { return; }
    throw std::runtime_error("Invalid proof accepted");
}

void malformed_proofs()
{
    ResolutionProof p;
    p.original(1, {1}, Partition::a);
    p.original(2, {-1, 2}, Partition::b);
    rejects([&] { p.original(1, {1}, Partition::b); });
    rejects([&] { p.original(0, {}, Partition::a); });
    rejects([&] { p.original(3, {0}, Partition::a); });
    rejects([&] { p.original(3, {INT_MIN}, Partition::a); });
    rejects([&] { p.original(3, {1, -1}, Partition::a); });
    rejects([&] { p.derive(3, {}, {}); });
    rejects([&] { p.derive(3, {}, {99}); });
    rejects([&] { p.derive(3, {}, {-1}); });
    rejects([&] { p.derive(3, {}, {1}, 1); });
    rejects([&] { p.derive(3, {}, {2, 1}); }); // wrong hint order
    rejects([&] { p.derive(3, {}, {1, 2}); }); // missing conflict
    rejects([&] { p.derive(3, {-1}, {1}); }); // satisfied antecedent
    rejects([&] { p.derive(3, {1}, {1, 2}); }); // hints after conflict
    rejects([&] { (void)p.conclude(1); });
    rejects([&] { p.erase(1, {-1}); });
    rejects([&] { p.restore(1, {1}); });
    p.erase(1, {1});
    rejects([&] { p.derive(3, {1}, {1}); });
    rejects([&] { p.restore(1, {-1}); });
    rejects([&] { p.restore(99, {1}); });
    p.restore(1, {1});
    p.derive(3, {2}, {1, 2}); // checker remains usable after rejection
    check_dag(p);
}

void materialized_assumptions()
{
    SolverProbe probe;
    probe.add({-1, 2}, Partition::a); // active formula group
    probe.add({-2}, Partition::b);
    probe.add({1}, Partition::a); // assumption as an attributed original unit
    CHECK(probe.solve() == 20);
    check_dag(probe.tracer.proof);

    SolverProbe unsupported;
    unsupported.add({1});
    unsupported.solver.assume(-1);
    CHECK(!unsupported.tracer.error.empty());
    CHECK(!unsupported.tracer.conclusion);
}
} // namespace

int main()
{
    try {
        CHECK(std::strcmp(CaDiCaL::Solver::version(), "3.0.1") == 0);
        CHECK(std::strcmp(CaDiCaL::Solver::signature(), "cadical-3.0.1-c607304") == 0);
        for (const auto& test : std::vector<std::pair<const char*, std::function<void()>>>{
                 {"roots, duplicates and propagation", roots_and_units},
                 {"search refutations", pigeonholes},
                 {"exhaustive and random truth-table oracles", truth_table_oracle},
                 {"weakening, deletion and restoration", weakening_and_lifecycle},
                 {"malformed proofs", malformed_proofs},
                 {"materialized assumptions", materialized_assumptions}}) {
            test.second();
            std::cout << "PASS " << test.first << '\n';
        }
    } catch (const std::exception& e) {
        std::cerr << "CaDiCaL proof gate failed: " << e.what() << '\n';
        return 1;
    }
}

#ifndef YASMV_SAT_PROOF_TRACER_HH
#define YASMV_SAT_PROOF_TRACER_HH

// Backend implementation detail: native solver types never enter Engine's API.
#include <sat/proof.hh>
#include <tracer.hpp>
#include <exception>
#include <optional>
#include <set>
#include <stdexcept>

namespace sat::proof {
class ProofTracer : public CaDiCaL::Tracer {
    static void require(bool value) {
        if (!value) throw std::invalid_argument("Unsupported or malformed proof callback");
    }
public:
    ResolutionProof proof;
    explicit ProofTracer(std::function<void()> checkpoint = {},
                         size_t node_limit = std::numeric_limits<size_t>::max())
        : proof(std::move(checkpoint), node_limit) {}
    bool failed() const { return failure != nullptr; }
    std::exception_ptr failure;
    std::optional<Partition> submitting;
    Clause submitted;
    size_t originals = 0, derived = 0, deletions = 0, queries = 0;
    std::optional<NodeId> conclusion;

    // Do not unwind through CaDiCaL internals. A callback error poisons the
    // entire probe, and is reported after control returns from the solver.
    template<class F> void event(F fn) noexcept
    {
        if (failed()) return;
        try { fn(); }
        catch (...) { failure = std::current_exception(); }
    }
    void check() const { if (failure) std::rethrow_exception(failure); }
    void add_original_clause(int64_t id, bool, const Clause& clause, bool restored) override
    {
        event([&] {
            if (restored) { proof.restore(id, clause); return; }
            require(submitting.has_value());
            require(std::set<int>(clause.begin(), clause.end()) ==
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
            require(type == CaDiCaL::CONFLICT && ids.size() == 1);
            conclusion = proof.conclude(ids.front());
        });
    }
    void report_status(int status, int64_t id) override
    {
        event([&] { if (status == 20 && id) (void)proof.conclude(id); });
    }
    void solve_query() override { event([&] { require(++queries == 1); }); }
    void add_assumption(int) override { event([] { throw std::runtime_error("Native assumptions unsupported; submit partitioned units"); }); }
    void add_constraint(const Clause&) override { event([] { throw std::runtime_error("Native constraint unsupported"); }); }
    void add_assumption_clause(int64_t, const Clause&, const std::vector<int64_t>&) override
    { event([] { throw std::runtime_error("Assumption proof unsupported"); }); }
    void notify_equivalence(int, int) override
    { event([] { throw std::runtime_error("Equivalence notification unsupported"); }); }
    // weaken_minus, strengthen and demote only change solver bookkeeping;
    // they grant no new proof fact. Actual additions/deletions are checked.
};

} // namespace sat::proof
#endif

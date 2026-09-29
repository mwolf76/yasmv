#ifndef YASMV_REACH_INTERPOLATION_HH
#define YASMV_REACH_INTERPOLATION_HH

#include <algorithms/base.hh>
#include <sat/interpolation.hh>
#include <optional>

namespace reach::interpolation {

using Bits = std::vector<enc::TCBI>;
using State = std::vector<bool>;
using Path = std::vector<State>;

// Internal finite-state system contract. All three formulas include legal-state
// restrictions: initial = INIT & C, transition = C & TRANS & C', target = C & F.
// initial(false) is the semantic complement, not the negation of auxiliary CNF.
// Every emitted clause must be conditional on guard (a raw Engine variable).
// bits() lists the entire state in canonical frame zero, preserving FROZEN.
class System {
public:
    virtual ~System() = default;
    virtual const Bits& bits() const = 0;
    virtual void initial(sat::Engine&, step_t, bool positive = true, sat::group_t guard = sat::MAINGROUP) const = 0;
    virtual void transition(sat::Engine&, step_t, sat::group_t guard = sat::MAINGROUP) const = 0;
    virtual void target(sat::Engine&, step_t, sat::group_t guard = sat::MAINGROUP) const = 0;
};

// Owns compiled units for the currently validated model, its effective inputs,
// and the supplied state assumptions. The model/environment must stay immutable.
class ModelSystem final : public System {
public:
    ModelSystem(algorithms::Algorithm&, expr::Expr_ptr target, const expr::ExprVector& assumptions = {});
    const Bits& bits() const override { return bits_; }
    void initial(sat::Engine&, step_t, bool positive = true, sat::group_t guard = sat::MAINGROUP) const override;
    void transition(sat::Engine&, step_t, sat::group_t guard = sat::MAINGROUP) const override;
    void target(sat::Engine&, step_t, sat::group_t guard = sat::MAINGROUP) const override;
private:
    Bits bits_;
    std::vector<sat::StatePredicate> init_, legal_;
    std::vector<sat::TransitionRelation> trans_;
    sat::StatePredicate target_;
    void legal(sat::Engine&, step_t, sat::group_t) const;
};

// Atoms are one-based indices in bits. The graph contains only semantic bits;
// its own fresh Tseitin variables are generated each time it is emitted.
struct StateFormula {
    explicit StateFormula(Bits bits = {}, size_t node_limit = std::numeric_limits<sat::Circuit::Ref>::max() / 2);
    sat::Circuit circuit;
    sat::Circuit::Ref root = sat::Circuit::False;
    Bits bits;
    void emit(sat::Engine&, step_t, bool positive = true) const;
    bool evaluate(const State&) const;
};

enum class Event { concrete, initial_projection, image, inclusion, growth, restart,
                   verify_initial, verify_transition, verify_target, verify_path };
using Observer = std::function<void(Event)>;
struct Limits {
    int64_t horizon = -1, images = -1;
    sat::InterpolationLimits interpolation;
    size_t invariant_nodes = std::numeric_limits<sat::Circuit::Ref>::max() / 2;
};
struct Statistics {
    uint64_t images = 0, enlargements = 0, restarts = 0, concrete_sat = 0, spurious_sat = 0;
    uint64_t proof_nodes = 0;
    size_t circuit_nodes = 0;
    unsigned horizon = 0;
    std::vector<unsigned> checked_depths;
};
enum class Outcome { unknown, reachable, unreachable };
enum class Stop { none, horizon_limit, image_limit, node_limit, interrupted, solver_unknown };
struct Result {
    Outcome outcome = Outcome::unknown;
    Stop stop = Stop::none;
    query::StopReason query_stop = query::StopReason::none;
    bool verified = false, vacuous = false;
    Statistics statistics;
    Path path;
    std::optional<StateFormula> invariant;
};

// A bad state may occur at any depth <= horizon. Continuations (including all
// their auxiliary clauses) are guarded, so deadlocks need no artificial stutter.
void emit_suffix(const System&, sat::Engine&, step_t first, unsigned horizon);
sat::status_t verify_invariant(const System&, const StateFormula&, const Observer& = {});
sat::status_t verify_path(const System&, const Path&, const Observer& = {});

// Fresh image proofs, increasing suffix horizons, and an incremental concrete
// search for shortest paths. UNKNOWN/limits/cancellation publish no certificate.
// Malformed systems or failed verification are errors, never proof conclusions.
Result search(const System&, Limits = {}, const Observer& = {});

} // namespace reach::interpolation
#endif

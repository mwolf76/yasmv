#ifndef YASMV_SAT_INTERPOLATION_HH
#define YASMV_SAT_INTERPOLATION_HH

#include <sat/circuit.hh>
#include <sat/engine.hh>
#include <compiler/compiler.hh>

namespace sat {

// Compile both semantic polarities. Negating a CNF with existential auxiliaries
// would not represent the complement of the state predicate.
class StatePredicate {
public:
    StatePredicate(compiler::Compiler&, expr::Expr_ptr expression, expr::Expr_ptr scope);
    void emit(Engine&, step_t frame, bool positive = true, group_t guard = MAINGROUP) const;
private:
    compiler::Unit positive_, negative_;
};

// A time-homogeneous relation over the current and next state. Nondeterminism
// is admitted, but absolute times and references beyond the next frame are not.
class TransitionRelation {
public:
    TransitionRelation(compiler::Compiler&, expr::Expr_ptr expression, expr::Expr_ptr scope);
    void emit(Engine&, step_t frame, group_t guard = MAINGROUP) const;
private:
    compiler::Unit unit_;
};

class PartitionedCnf {
public:
    struct Clause { proof::Clause literals; proof::Partition partition; };
    // Both engines must be distinct recording instances for this model.
    // Shared semantic bits must lie on cut_frame, or be frozen parameters.
    PartitionedCnf(const Engine& a, const Engine& b, step_t cut_frame);
    const std::vector<Clause>& clauses() const { return clauses_; }
    int variables() const { return variables_; }
    const std::map<Circuit::Atom, int>& interface() const { return interface_; }
    // Interpolant atoms refer to canonical frame zero; frozen bits stay frozen.
    const std::map<Circuit::Atom, enc::TCBI>& state_bits() const { return state_bits_; }
    // Fresh ordinary solvers check A => J and J AND B = false. UNKNOWN is not
    // verification; SAT is a failed Craig condition, including mutated J.
    status_t verify(const Circuit&, Circuit::Ref) const;
private:
    int variables_ = 0;
    std::vector<Clause> clauses_;
    std::map<Circuit::Atom, int> interface_;
    std::map<Circuit::Atom, enc::TCBI> state_bits_;
};

struct InterpolationLimits {
    size_t proof_nodes = std::numeric_limits<size_t>::max();
    size_t circuit_nodes = std::numeric_limits<Circuit::Ref>::max() / 2;
};
struct InterpolationResult {
    status_t status = STATUS_UNKNOWN;
    bool verified = false;
    Circuit circuit;
    Circuit::Ref root = Circuit::False;
    std::map<Circuit::Atom, enc::TCBI> state_bits;
    size_t proof_nodes = 0;
};

InterpolationResult compute_interpolant(const PartitionedCnf&, InterpolationLimits = {});
// Instantiate a canonical interpolant in any frame. Each call uses fresh
// circuit auxiliaries; semantic bits are mapped through TCBI, never native IDs.
void emit_interpolant(Engine&, const InterpolationResult&, step_t frame, bool positive = true);

} // namespace sat
#endif

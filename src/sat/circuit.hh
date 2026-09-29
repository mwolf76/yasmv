#ifndef YASMV_SAT_CIRCUIT_HH
#define YASMV_SAT_CIRCUIT_HH

#include <sat/proof.hh>
#include <functional>
#include <limits>
#include <map>
#include <set>

namespace sat {

// Hash-consed AND graph with complemented edges. Atoms belong to the caller's
// semantic dictionary; they are never solver variable IDs or encoding helpers.
class Circuit {
public:
    using Atom = uint64_t;
    using Ref = uint32_t;
    static constexpr Ref False = 0, True = 1;
    explicit Circuit(std::function<void()> checkpoint = {}, size_t limit = std::numeric_limits<Ref>::max() / 2);
    Ref atom(Atom);
    Ref negate(Ref) const;
    Ref conjunction(Ref, Ref);
    Ref disjunction(Ref a, Ref b) { return negate(conjunction(negate(a), negate(b))); }
    Ref import(const Circuit&, Ref, const std::function<Atom(Atom)>& rename);
    std::set<Atom> support(Ref) const;
    bool evaluate(Ref, const std::function<bool(Atom)>&) const;
    // Emit definitions with fresh auxiliaries on every call, for either polarity.
    // Callbacks use signed nonzero DIMACS literals, not packed sat::Lit.
    int encode(Ref, const std::function<int()>& fresh,
               const std::function<int(Atom)>& atom_literal,
               const std::function<void(const proof::Clause&)>& emit) const;
    size_t size() const { return nodes_.size() - 1; }

private:
    struct Node { Atom atom; Ref left, right; };
    std::vector<Node> nodes_{{0, 0, 0}};
    std::map<Atom, Ref> atoms_;
    std::map<std::pair<Ref, Ref>, Ref> ands_;
    std::function<void()> checkpoint_;
    size_t limit_;
    void tick() const;
    void valid(Ref) const;
    Ref append(Node);
    std::vector<size_t> order(Ref) const;
};

// Extract labels from a checked resolution DAG. The dictionary must authorize
// every shared input variable. Missing authorization is an error, never a new
// state atom. Weakening carries its parent's label unchanged.
Circuit::Ref interpolate(const proof::ResolutionProof&, proof::NodeId root,
                         const std::map<int, Circuit::Atom>& shared,
                         Circuit&, const std::function<void()>& checkpoint = {});

} // namespace sat
#endif

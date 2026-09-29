#ifndef YASMV_SAT_PROOF_HH
#define YASMV_SAT_PROOF_HH

#include <cstddef>
#include <cstdint>
#include <map>
#include <vector>

namespace sat::proof {

// Proof literals are signed nonzero integers, not yasmv's packed Lit values.
using Clause = std::vector<int>;
using Id = int64_t;
using NodeId = size_t;
enum class Partition { a, b };
enum class Rule { original, resolution, weakening };

struct Node {
    Clause clause;
    Rule rule;
    Partition partition = Partition::a; // meaningful only for original nodes
    NodeId left = 0, right = 0;
    int pivot = 0; // signed literal in the left antecedent
};

// A checked, nonincremental refutation. No solver headers or global managers.
// Nodes survive deletion of solver clauses; deleted IDs cannot be antecedents.
class ResolutionProof {
public:
    void original(Id, const Clause&, Partition);
    void restore(Id, const Clause&);
    void erase(Id, const Clause&);
    void derive(Id, const Clause&, const std::vector<Id>& hints, int witness = 0);
    NodeId conclude(Id) const;
    const std::vector<Node>& nodes() const { return nodes_; }
    NodeId node(Id) const;

private:
    struct Entry { NodeId node; bool active; };
    std::vector<Node> nodes_;
    std::map<Id, Entry> clauses_;
    void fresh(Id) const;
};

} // namespace sat::proof
#endif

#include <sat/proof.hh>

#include <algorithm>
#include <climits>
#include <set>
#include <stdexcept>
#include <string>
#include <utility>

namespace sat::proof {
namespace {
void require(bool condition, const char* message)
{
    if (!condition) throw std::invalid_argument(std::string("Invalid resolution proof: ") + message);
}

Clause normalize(const Clause& clause)
{
    std::set<int> literals;
    for (int lit : clause) {
        require(lit != 0 && lit != INT_MIN, "invalid literal");
        require(!literals.count(-lit), "tautological clause unsupported");
        literals.insert(lit);
    }
    return Clause(literals.begin(), literals.end());
}

Clause resolve(const Clause& left, const Clause& right, int pivot)
{
    require(std::binary_search(left.begin(), left.end(), pivot) &&
            std::binary_search(right.begin(), right.end(), -pivot), "missing pivot");
    Clause result;
    for (int lit : left) if (lit != pivot) result.push_back(lit);
    for (int lit : right) if (lit != -pivot) result.push_back(lit);
    return normalize(result);
}
} // namespace

void ResolutionProof::fresh(Id id) const
{
    require(id > 0 && !clauses_.count(id), "duplicate or invalid clause ID");
}

NodeId ResolutionProof::node(Id id) const
{
    const auto found = clauses_.find(id);
    require(found != clauses_.end() && found->second.active, "missing or deleted antecedent");
    return found->second.node;
}

void ResolutionProof::original(Id id, const Clause& clause, Partition partition)
{
    fresh(id);
    auto normalized = normalize(clause);
    clauses_.emplace(id, Entry{nodes_.size(), true});
    nodes_.push_back({std::move(normalized), Rule::original, partition});
}

void ResolutionProof::restore(Id id, const Clause& clause)
{
    const auto found = clauses_.find(id);
    require(found != clauses_.end() && !found->second.active, "invalid restoration");
    require(nodes_[found->second.node].clause == normalize(clause), "changed restored clause");
    // Keep the previous derivation/partition, even for a restored derived clause.
    found->second.active = true;
}

void ResolutionProof::erase(Id id, const Clause& clause)
{
    require(nodes_[node(id)].clause == normalize(clause), "changed deleted clause");
    clauses_.at(id).active = false;
}

void ResolutionProof::derive(Id id, const Clause& clause,
                             const std::vector<Id>& hints, int witness)
{
    fresh(id);
    require(witness == 0, "RAT/extension step unsupported");
    const auto target = normalize(clause);
    require(!hints.empty(), "missing RUP antecedents");
    // Assume the negated candidate clause, then replay ordered unit propagation.
    std::set<int> assigned;
    for (int lit : target) assigned.insert(-lit);
    std::vector<std::pair<int, NodeId>> reasons;
    NodeId conflict = 0;
    bool contradicted = false;
    for (size_t i = 0; i < hints.size(); ++i) {
        require(hints[i] > 0, "RAT hint unsupported");
        const auto antecedent = node(hints[i]);
        int unit = 0;
        for (int lit : nodes_[antecedent].clause) {
            require(!assigned.count(lit), "satisfied RUP antecedent");
            if (!assigned.count(-lit)) {
                require(unit == 0, "nonunit RUP antecedent");
                unit = lit;
            }
        }
        if (!unit) {
            require(i + 1 == hints.size(), "hints after conflict");
            conflict = antecedent;
            contradicted = true;
        } else {
            assigned.insert(unit);
            reasons.emplace_back(unit, antecedent);
        }
    }
    require(contradicted, "RUP chain has no conflict");

    // Resolve the conflict backwards through relevant reasons. Unused unit
    // propagations do not participate in the resolution derivation.
    for (auto it = reasons.rbegin(); it != reasons.rend(); ++it) {
        const int pivot = -it->first;
        const auto& current = nodes_[conflict].clause;
        if (!std::binary_search(current.begin(), current.end(), pivot)) continue;
        auto resolvent = resolve(current, nodes_[it->second].clause, pivot);
        nodes_.push_back({std::move(resolvent), Rule::resolution, Partition::a,
                          conflict, it->second, pivot});
        conflict = nodes_.size() - 1;
    }
    const auto& result = nodes_[conflict].clause;
    require(std::includes(target.begin(), target.end(), result.begin(), result.end()),
            "resolvent is not a subclause of candidate");
    if (result != target) {
        // Explicit weakening preserves the antecedent's interpolation label.
        nodes_.push_back({target, Rule::weakening, Partition::a, conflict});
        conflict = nodes_.size() - 1;
    }
    clauses_.emplace(id, Entry{conflict, true});
}

NodeId ResolutionProof::conclude(Id id) const
{
    const auto root = node(id);
    require(nodes_[root].clause.empty(), "conclusion is not the empty clause");
    return root;
}
} // namespace sat::proof

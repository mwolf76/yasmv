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

Clause normalize(const Clause& clause, const std::function<void()>& tick)
{
    std::set<int> literals;
    for (int lit : clause) {
        tick();
        require(lit != 0 && lit != INT_MIN, "invalid literal");
        require(!literals.count(-lit), "tautological clause unsupported");
        literals.insert(lit);
    }
    return Clause(literals.begin(), literals.end());
}

void resolve(const Clause& left, const Clause& right, int pivot, Clause& output, const std::function<void()>& tick)
{
    require(std::binary_search(left.begin(), left.end(), pivot) &&
            std::binary_search(right.begin(), right.end(), -pivot), "missing pivot");
    // Both parents are normalized. Merge into the reusable next buffer rather
    // than allocating a tree and a new literal buffer at every resolution.
    output.clear();
    auto a = left.begin(), b = right.begin();
    while (a != left.end() || b != right.end()) {
        tick();
        if (a != left.end() && *a == pivot) { ++a; continue; }
        if (b != right.end() && *b == -pivot) { ++b; continue; }
        if (b == right.end() || (a != left.end() && *a < *b)) output.push_back(*a++);
        else if (a == left.end() || *b < *a) output.push_back(*b++);
        else { output.push_back(*a++); ++b; }
    }
    // Compare negative and positive literals by decreasing magnitude. Parents
    // exclude zero and INT_MIN, so negation is safe; reject complementary pairs.
    size_t low = 0, high = output.size();
    while (low < high && output[low] < 0 && output[high-1] > 0) {
        tick();
        const auto negative = -output[low], positive = output[high-1];
        require(negative != positive, "tautological clause unsupported");
        if (negative > positive) ++low; else --high;
    }
}
} // namespace

void ResolutionProof::fresh(Id id) const
{
    tick();
    require(id > 0 && !clauses_.count(id), "duplicate or invalid clause ID");
}

NodeId ResolutionProof::node(Id id) const
{
    tick();
    const auto found = clauses_.find(id);
    require(found != clauses_.end() && found->second.active, "missing or deleted antecedent");
    return found->second.node;
}

const Clause& ResolutionProof::clause(NodeId id) const
{
    require(id < nodes_.size() && nodes_[id].clause_index != Node::no_clause,
            "node has no retained clause");
    return retained_.at(nodes_[id].clause_index);
}

void ResolutionProof::retain(NodeId id, Clause clause)
{
    auto& n = nodes_.at(id);
    // Different solver IDs can name the same already checked derivation.
    if (n.clause_index != Node::no_clause) {
        require(retained_.at(n.clause_index) == clause, "changed named clause");
        return;
    }
    const auto index = retained_.size();
    retained_.push_back(std::move(clause));
    n.clause_index = index;
    auto& memory = n.rule == Rule::original ? original_ : derived_;
    ++memory.clauses;
    memory.literals += retained_.back().size();
    memory.capacity += retained_.back().capacity();
}

void ResolutionProof::original(Id id, const Clause& clause, Partition partition)
{
    fresh(id);
    auto normalized = normalize(clause, [this] { tick(); });
    append({Rule::original, partition});
    expanded_literals_ += normalized.size();
    retain(nodes_.size() - 1, std::move(normalized));
    clauses_.emplace(id, Entry{nodes_.size() - 1, true});
    ++active_ids_;
}

void ResolutionProof::restore(Id id, const Clause& clause)
{
    const auto found = clauses_.find(id);
    require(found != clauses_.end() && !found->second.active, "invalid restoration");
    require(this->clause(found->second.node) == normalize(clause, [this] { tick(); }), "changed restored clause");
    // Keep the previous derivation/partition, even for a restored derived clause.
    found->second.active = true;
    ++active_ids_;
}

void ResolutionProof::erase(Id id, const Clause& clause)
{
    require(this->clause(node(id)) == normalize(clause, [this] { tick(); }), "changed deleted clause");
    clauses_.at(id).active = false;
    --active_ids_;
}

void ResolutionProof::derive(Id id, const Clause& clause,
                             const std::vector<Id>& hints, int witness)
{
    fresh(id);
    require(witness == 0, "RAT/extension step unsupported");
    auto target = normalize(clause, [this] { tick(); });
    require(!hints.empty(), "missing RUP antecedents");
    // Assume the negated candidate clause, then replay ordered unit propagation.
    std::set<int> assigned;
    for (int lit : target) assigned.insert(-lit);
    std::vector<std::pair<int, NodeId>> reasons;
    NodeId conflict = 0;
    bool contradicted = false;
    for (size_t i = 0; i < hints.size(); ++i) {
        tick();
        require(hints[i] > 0, "RAT hint unsupported");
        const auto antecedent = node(hints[i]);
        int unit = 0;
        for (int lit : this->clause(antecedent)) {
            tick();
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
    // Intermediate clauses live only in these rolling buffers. The graph
    // retains the same checked resolution steps and pivot orientation.
    Clause rolling, next;
    const Clause* current = &this->clause(conflict);
    for (auto it = reasons.rbegin(); it != reasons.rend(); ++it) {
        tick();
        const int pivot = -it->first;
        if (!std::binary_search(current->begin(), current->end(), pivot)) continue;
        resolve(*current, this->clause(it->second), pivot, next, [this] { tick(); });
        temporary_capacity_peak_ = std::max(temporary_capacity_peak_, rolling.capacity() + next.capacity());
        rolling.swap(next);
        current = &rolling;
        append({Rule::resolution, Partition::a, conflict, it->second, pivot});
        expanded_literals_ += rolling.size();
        conflict = nodes_.size() - 1;
    }
    const auto& result = *current;
    require(std::includes(target.begin(), target.end(), result.begin(), result.end()),
            "resolvent is not a subclause of candidate");
    if (result != target) {
        // Explicit weakening preserves the antecedent's interpolation label.
        append({Rule::weakening, Partition::a, conflict});
        expanded_literals_ += target.size();
        conflict = nodes_.size() - 1;
    }
    retain(conflict, std::move(target));
    clauses_.emplace(id, Entry{conflict, true});
    ++active_ids_;
}

NodeId ResolutionProof::conclude(Id id) const
{
    const auto root = node(id);
    require(clause(root).empty(), "conclusion is not the empty clause");
    return root;
}
void ResolutionProof::append(Node node)
{
    tick();
    if (nodes_.size() >= node_limit_) throw std::length_error("Resolution proof node limit exceeded");
    nodes_.push_back(std::move(node));
    if (observer_ && nodes_.size() % 4096 == 0) observer_(*this);
}
ResolutionProof::Memory ResolutionProof::memory() const
{
    const auto literals = original_.literals + derived_.literals;
    const auto capacity = original_.capacity + derived_.capacity;
    return {nodes_.size(), nodes_.capacity(), literals, capacity, active_ids_, clauses_.size(),
            nodes_.capacity() * sizeof(Node), capacity * sizeof(int),
            clauses_.size() * sizeof(decltype(clauses_)::value_type),
            retained_.capacity() * sizeof(Clause), expanded_literals_, temporary_capacity_peak_ * sizeof(int),
            original_, derived_};
}
} // namespace sat::proof

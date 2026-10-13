#include <sat/circuit.hh>
#include <sat/interpolation_diagnostics.hh>

#include <algorithm>
#include <climits>
#include <stdexcept>

namespace sat {
Circuit::Circuit(std::function<void()> checkpoint, size_t limit)
    : checkpoint_(std::move(checkpoint)), limit_(limit) {}
void Circuit::tick() const { if (checkpoint_) checkpoint_(); }
void Circuit::valid(Ref r) const
{
    if (r / 2 >= nodes_.size()) throw std::invalid_argument("Invalid circuit reference");
}
Circuit::Ref Circuit::append(Node node)
{
    tick();
    if (size() >= limit_ || nodes_.size() > std::numeric_limits<Ref>::max() / 2)
        throw std::length_error("Circuit node limit exceeded");
    const auto result = static_cast<Ref>(nodes_.size() * 2);
    nodes_.push_back(node);
    return result;
}
Circuit::Ref Circuit::atom(Atom atom)
{
    tick();
    if (!atom) throw std::invalid_argument("Circuit atom zero is reserved");
    if (auto i = atoms_.find(atom); i != atoms_.end()) return i->second;
    const auto ref = append({atom, 0, 0});
    atoms_.emplace(atom, ref);
    return ref;
}
Circuit::Ref Circuit::negate(Ref r) const { valid(r); return r ^ 1; }
Circuit::Ref Circuit::conjunction(Ref a, Ref b)
{
    tick(); valid(a); valid(b);
    if (a == False || b == False || a == (b ^ 1)) return False;
    if (a == True) return b;
    if (b == True || a == b) return a;
    if (a > b) std::swap(a, b);
    const auto key = std::make_pair(a, b);
    if (auto i = ands_.find(key); i != ands_.end()) return i->second;
    const auto result = append({0, a, b});
    ands_.emplace(key, result);
    return result;
}
std::vector<Circuit::Ref> Circuit::order(Ref root) const
{
    valid(root);
    // Internal IDs are dense and parents precede children. Bound scratch space
    // by the root, not by unrelated nodes appended later to this circuit.
    std::vector<uint8_t> seen(root / 2 + 1);
    std::vector<Ref> pending, result;
    const auto enqueue = [&](Ref id) {
        if (id && !seen[id]) { seen[id] = 1; pending.push_back(id); }
    };
    enqueue(root / 2);
    while (!pending.empty()) {
        tick();
        const auto id = pending.back(); pending.pop_back();
        result.push_back(id);
        const auto& n = nodes_[id];
        if (!n.atom) { enqueue(n.left / 2); enqueue(n.right / 2); }
    }
    // Preserve the former ascending order, including callback/CNF allocation
    // order. Sorting only reachable IDs avoids scanning an unrelated prefix.
    size_t comparisons = 0;
    std::sort(result.begin(), result.end(), [&](Ref a, Ref b) {
        if (++comparisons % 4096 == 0) tick();
        return a < b;
    });
    tick();
    return result;
}
Circuit::Ref Circuit::import(const Circuit& source, Ref root,
                              const std::function<Atom(Atom)>& rename)
{
    const auto ids = source.order(root);
    std::vector<Ref> result(root / 2 + 1, False);
    auto edge = [&](Ref r) { return result.at(r / 2) ^ (r & 1); };
    for (const auto id : ids) {
        tick();
        const auto n = source.nodes_[id]; // copy: importing into the same graph is allowed
        result[id] = n.atom ? atom(rename(n.atom)) : conjunction(edge(n.left), edge(n.right));
    }
    return edge(root);
}
void Circuit::visit(Ref root, const std::function<void(Ref, Atom, Ref, Ref)>& visitor) const
{
    for (auto id : order(root)) {
        tick();
        const auto& node = nodes_[id];
        visitor(static_cast<Ref>(id * 2), node.atom, node.left, node.right);
    }
}
std::set<Circuit::Atom> Circuit::support(Ref root) const
{
    std::set<Atom> result;
    for (auto id : order(root)) { tick(); if (nodes_[id].atom) result.insert(nodes_[id].atom); }
    return result;
}
bool Circuit::evaluate(Ref root, const std::function<bool(Atom)>& value) const
{
    valid(root);
    std::vector<uint8_t> values(root / 2 + 1);
    auto edge = [&](Ref r) { return values.at(r / 2) != bool(r & 1); };
    for (auto id : order(root)) {
        tick(); const auto& n = nodes_[id];
        values[id] = n.atom ? value(n.atom) : edge(n.left) && edge(n.right);
    }
    return edge(root);
}
int Circuit::encode(Ref root, const std::function<int()>& fresh,
                    const std::function<int(Atom)>& atom_literal,
                    const std::function<void(const proof::Clause&)>& emit) const
{
    auto literal = [](int x) {
        if (!x || x == INT_MIN) throw std::invalid_argument("Invalid circuit CNF literal");
        return x;
    };
    const auto ids = order(root);
    // A dedicated constant is local to this emission, even across polarities.
    const int truth = literal(fresh()); emit({truth});
    std::vector<int> values(root / 2 + 1);
    values[0] = -truth;
    auto edge = [&](Ref r) { return (r & 1) ? -values.at(r / 2) : values.at(r / 2); };
    for (auto id : ids) {
        tick(); const auto& n = nodes_[id];
        if (n.atom) values[id] = literal(atom_literal(n.atom));
        else {
            const int z = literal(fresh()), a = edge(n.left), b = edge(n.right);
            emit({-z, a}); emit({-z, b}); emit({z, -a, -b}); values[id] = z;
        }
    }
    return edge(root);
}

Circuit::Ref interpolate(const proof::ResolutionProof& proof, proof::NodeId root,
                         const std::map<int, Circuit::Atom>& shared, Circuit& circuit,
                         const std::function<void()>& checkpoint)
{
    const auto tick = [&] { if (checkpoint) checkpoint(); };
    const auto& nodes = proof.nodes();
    auto* diagnostic = diagnostics::enabled() ? diagnostics::current() : nullptr;
    if (diagnostic) diagnostic->phase("interpolant_ancestry_begin", &proof);
    if (root >= nodes.size() || !proof.clause(root).empty())
        throw std::invalid_argument("Interpolation requires a checked empty clause");
    std::map<int, unsigned> ownership;
    size_t original_nodes = 0, original_literals = 0;
    // Classify against all originals, including those absent from the refutation.
    for (size_t id = 0; id < nodes.size(); ++id) {
        tick();
        const auto& n = nodes[id];
        if (n.rule != proof::Rule::original) continue;
        const auto& clause = proof.clause(id);
        ++original_nodes; original_literals += clause.size();
        for (int lit : clause) { tick(); ownership[std::abs(lit)] |= n.partition == proof::Partition::a ? 1 : 2; }
    }
    std::set<Circuit::Atom> authorized_atoms;
    for (auto [var, sides] : ownership) {
        tick();
        if (sides == 3 && (!shared.count(var) || !shared.at(var)))
            throw std::invalid_argument("Interpolant interface contains an unauthorized shared variable");
        if (sides == 3 && !authorized_atoms.insert(shared.at(var)).second)
            throw std::invalid_argument("Distinct shared variables cannot alias a state atom");
    }
    // Unlike solver IDs, graph IDs form a dense append-only range. Marks and
    // labels can index that range directly, without one tree allocation per
    // ancestor. Keep classifying *all* originals above, even after the root.
    std::vector<uint8_t> needed(root + 1);
    size_t needed_count = 0, pending_capacity_peak = 0;
    {
        std::vector<proof::NodeId> todo;
        const auto enqueue = [&](proof::NodeId id) {
            if (!needed[id]) {
                needed[id] = 1;
                todo.push_back(id);
                pending_capacity_peak = std::max(pending_capacity_peak, todo.capacity());
            }
        };
        enqueue(root);
        while (!todo.empty()) {
            tick(); const auto id = todo.back(); todo.pop_back();
            ++needed_count;
            if (diagnostic && needed_count % 4096 == 0) diagnostic->progress(proof);
            const auto& n = nodes[id];
            if (n.rule != proof::Rule::original) {
                if (n.left >= id) throw std::invalid_argument("Invalid proof DAG order");
                enqueue(n.left);
                if (n.rule == proof::Rule::resolution) {
                    if (n.right >= id) throw std::invalid_argument("Invalid proof DAG order");
                    enqueue(n.right);
                }
            }
        }
    }
    if (diagnostic) diagnostic->counters("proof_ancestry", {{"needed_proof_nodes",needed_count},
        {"stored_proof_nodes",nodes.size()},{"original_nodes",original_nodes},{"original_literals",original_literals}});
    if (diagnostic) diagnostic->phase("interpolant_labels_begin", &proof);
    std::vector<Circuit::Ref> labels(root + 1);
    size_t labelled = 0;
    for (size_t id = 0; id < needed.size(); ++id) {
        tick();
        if (!needed[id]) continue;
        const auto& n = nodes[id];
        auto label = Circuit::True;
        if (n.rule == proof::Rule::original && n.partition == proof::Partition::a) {
            label = Circuit::False;
            for (int lit : proof.clause(id)) {
                tick();
                if (ownership.at(std::abs(lit)) != 3) continue;
                auto leaf = circuit.atom(shared.at(std::abs(lit)));
                label = circuit.disjunction(label, lit < 0 ? circuit.negate(leaf) : leaf);
            }
        } else if (n.rule == proof::Rule::weakening) label = labels.at(n.left);
        else if (n.rule == proof::Rule::resolution) {
            const auto a = labels.at(n.left), b = labels.at(n.right);
            label = ownership.at(std::abs(n.pivot)) == 1
                ? circuit.disjunction(a, b) : circuit.conjunction(a, b);
        }
        labels[id] = label;
        if (diagnostic && ++labelled % 4096 == 0) diagnostic->progress(proof, &circuit);
    }
    if (diagnostic) diagnostic->counters("interpolant_traversal", {
        {"interpolant_mark_bytes",needed.capacity() * sizeof(decltype(needed)::value_type)},
        {"interpolant_label_bytes",labels.capacity() * sizeof(Circuit::Ref)},
        {"interpolant_pending_bytes_peak",pending_capacity_peak * sizeof(proof::NodeId)}});
    return labels.at(root);
}
} // namespace sat

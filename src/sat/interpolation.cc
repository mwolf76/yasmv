#include <sat/interpolation.hh>
#include <env/environment.hh>
#include <symb/proxy.hh>
#include <symb/classes.hh>
#include <symb/symb_iter.hh>

#include <climits>
#include <set>
#include <stdexcept>

namespace sat {
namespace {
void checkpoint() { query::checkpoint(query::Phase::encoding); }
bool deterministic_state(expr::Expr_ptr e, expr::Expr_ptr scope, unsigned depth = 0)
{
    query::checkpoint(query::Phase::compilation);
    if (!e) return true;
    if (depth > 512) throw std::invalid_argument("State predicate expansion is too deep");
    auto& em = expr::ExprMgr::INSTANCE();
    if (e->symb() == expr::NEXT || e->symb() == expr::ASSIGNMENT || e->symb() == expr::AT ||
        em.is_set(e) || em.is_set_comma(e)) return false;
    if (em.is_constant(e) || e->symb() == expr::QSTRING || e->symb() == expr::INSTANT || e->symb() == expr::TYPE) return true;
    if (em.is_dot(e)) return deterministic_state(e->rhs(), em.make_dot(scope, e->lhs()), depth + 1);
    if (em.is_identifier(e)) {
        symb::ResolverProxy resolver;
        const auto full = em.make_dot(scope, e);
        auto symbol = resolver.symbol(full);
        if (symbol->is_define()) return deterministic_state(symbol->as_define().body(), scope, depth + 1);
        if (symbol->is_parameter()) {
            auto rewrite = model::ModelMgr::INSTANCE().rewrite_parameter(full);
            return deterministic_state(rewrite->rhs(), rewrite->lhs(), depth + 1);
        }
        if (symbol->is_variable() && symbol->as_variable().is_input())
            return deterministic_state(env::Environment::INSTANCE().get(e), scope, depth + 1);
        return true;
    }
    return deterministic_state(e->lhs(), scope, depth + 1) && deterministic_state(e->rhs(), scope, depth + 1);
}
compiler::Unit compile_state(compiler::Compiler& compiler, expr::Expr_ptr expression, expr::Expr_ptr scope)
{
    if (!expression || !scope || !deterministic_state(expression, scope) ||
        !model::ModelMgr::INSTANCE().type(expression, scope)->is_boolean())
        throw std::invalid_argument("Interpolation requires a deterministic Boolean state predicate");
    return compiler.process(scope, expression);
}
Lits convert(const proof::Clause& clause, const std::vector<Var>& vars)
{
    Lits result;
    for (int lit : clause) { checkpoint(); result.push_back(mkLit(vars.at(std::abs(lit)), lit < 0)); }
    return result;
}
std::vector<Var> allocate(Engine& engine, int count)
{
    std::vector<Var> vars(1, -1);
    for (int i = 0; i < count; ++i) vars.push_back(engine.new_sat_var());
    return vars;
}
// Adapter used solely for circuit emission. These DIMACS integers index owned
// Engine Vars (+1); they never refer directly to backend-native variables.
void emit_clause(Engine& engine, const proof::Clause& clause)
{
    Lits result;
    for (int lit : clause) { checkpoint(); result.push_back(mkLit(std::abs(lit) - 1, lit < 0)); }
    engine.add_clause(result);
}
} // namespace

StatePredicate::StatePredicate(compiler::Compiler& compiler, expr::Expr_ptr expression, expr::Expr_ptr scope)
    : positive_(compile_state(compiler, expression, scope)),
      negative_(compiler.process(scope, expr::ExprMgr::INSTANCE().make_not(expression))) {}
void StatePredicate::emit(Engine& engine, step_t frame, bool positive) const
{
    engine.push(positive ? positive_ : negative_, frame);
}

PartitionedCnf::PartitionedCnf(const Engine& a, const Engine& b, step_t cut_frame)
{
    if (&a == &b || a.mode() != Engine::Mode::record || b.mode() != Engine::Mode::record)
        throw std::invalid_argument("Interpolation requires distinct recording engines");
    // Build a whitelist from model declarations. Compiler-generated DD bits can
    // also have TCBIs, but do not occur in this semantic-state catalog.
    std::map<expr::Expr_ptr, bool, std::less<expr::Expr_ptr>> catalog;
    auto& em = expr::ExprMgr::INSTANCE();
    symb::SymbIter symbols(model::ModelMgr::INSTANCE().model());
    while (symbols.has_next()) {
        checkpoint(); const auto [scope, symbol] = symbols.next();
        if (!symbol->is_variable()) continue;
        const auto& variable = symbol->as_variable();
        if (variable.is_temp() || variable.is_input() || variable.type()->is_instance()) continue;
        catalog.emplace(em.make_dot(scope, symbol->name()), variable.is_frozen());
    }
    TCBI2VarMap semantic;
    std::map<int, enc::TCBI> bits;
    std::map<int, unsigned> used;
    const auto fresh = [&] {
        if (variables_ == INT_MAX) throw std::length_error("Partitioned CNF variable limit exceeded");
        return ++variables_;
    };
    auto append = [&](const Engine& source, proof::Partition partition) {
        std::map<Var, int> local;
        auto variable = [&](Var var) {
            if (auto found = local.find(var); found != local.end()) return found->second;
            int id;
            const auto tcbi = source.encoded_bits().find(var);
            if (tcbi != source.encoded_bits().end() && catalog.count(tcbi->second.expr())) {
                const auto& bit = tcbi->second;
                if (catalog.at(bit.expr()) != (bit.time() == FROZEN))
                    throw std::logic_error("State bit has inconsistent frozen identity");
                auto found = semantic.find(bit);
                if (found != semantic.end()) id = found->second;
                else { id = fresh(); semantic.emplace(bit, id); bits.emplace(id, bit); }
            } else id = fresh();
            local.emplace(var, id);
            return id;
        };
        for (const auto& source_clause : source.recorded_clauses()) {
            checkpoint();
            std::set<int> normalized;
            for (auto lit : source_clause) {
                checkpoint(); const int id = variable(var(lit));
                normalized.insert(sign(lit) ? -id : id);
            }
            bool tautology = false;
            for (int lit : normalized) if (normalized.count(-lit)) { tautology = true; break; }
            if (tautology) continue;
            for (int lit : normalized) used[std::abs(lit)] |= partition == proof::Partition::a ? 1 : 2;
            clauses_.push_back({{normalized.begin(), normalized.end()}, partition});
        }
    };
    append(a, proof::Partition::a);
    append(b, proof::Partition::b);
    for (const auto& [id, bit] : bits) {
        checkpoint();
        if (used[id] != 3) continue;
        const bool frozen = bit.time() == FROZEN;
        if (!frozen && bit.absolute_time() != cut_frame)
            throw std::invalid_argument("Shared state variable lies outside the interpolation cut");
        const Circuit::Atom atom = interface_.size() + 1;
        interface_.emplace(atom, id);
        state_bits_.emplace(atom, enc::TCBI(enc::UCBI(bit.expr(), frozen ? FROZEN : 0, bit.bitno()), 0));
    }
}

status_t PartitionedCnf::verify(const Circuit& circuit, Circuit::Ref root) const
{
    for (auto atom : circuit.support(root))
        if (!interface_.count(atom)) throw std::invalid_argument("Interpolant has noninterface support");
    for (auto partition : {proof::Partition::a, proof::Partition::b}) {
        Engine engine("verify-interpolant");
        const auto vars = allocate(engine, variables_);
        for (const auto& clause : clauses_) {
            checkpoint();
            if (clause.partition == partition) engine.add_clause(convert(clause.literals, vars));
        }
        const auto desired = partition == proof::Partition::a ? circuit.negate(root) : root;
        const int top = circuit.encode(desired, [&] { return engine.new_sat_var() + 1; },
            [&](Circuit::Atom atom) { return vars.at(interface_.at(atom)) + 1; },
            [&](const proof::Clause& c) { emit_clause(engine, c); });
        emit_clause(engine, {top});
        const auto status = engine.solve();
        if (status != STATUS_UNSAT) return status;
    }
    return STATUS_UNSAT;
}

InterpolationResult compute_interpolant(const PartitionedCnf& input, InterpolationLimits limits)
{
    Engine engine("interpolation-proof", Engine::Mode::proof, limits.proof_nodes);
    const auto vars = allocate(engine, input.variables());
    for (const auto& clause : input.clauses()) {
        checkpoint(); engine.add_proof_clause(convert(clause.literals, vars), clause.partition);
    }
    const auto status = engine.solve();
    if (status != STATUS_UNSAT) {
        InterpolationResult result; result.status = status; return result;
    }
    InterpolationResult result;
    result.circuit = Circuit(checkpoint, limits.circuit_nodes);
    std::map<int, Circuit::Atom> shared;
    for (auto [atom, variable] : input.interface()) shared.emplace(engine.proof_variable(vars.at(variable)), atom);
    result.root = interpolate(engine.resolution_proof(), engine.proof_root(), shared, result.circuit, checkpoint);
    const auto verification = input.verify(result.circuit, result.root);
    if (verification == STATUS_UNKNOWN) return InterpolationResult();
    if (verification != STATUS_UNSAT) throw std::logic_error("Interpolant failed fresh Craig-condition checks");
    checkpoint();
    result.status = STATUS_UNSAT;
    result.verified = true;
    result.state_bits = input.state_bits();
    result.proof_nodes = engine.resolution_proof().nodes().size();
    return result;
}

void emit_interpolant(Engine& engine, const InterpolationResult& result, step_t frame, bool positive)
{
    if (result.status != STATUS_UNSAT || !result.verified)
        throw std::invalid_argument("Cannot emit an unverified interpolant");
    const auto root = positive ? result.root : result.circuit.negate(result.root);
    const int top = result.circuit.encode(root, [&] { return engine.new_sat_var() + 1; },
        [&](Circuit::Atom atom) {
            const auto& bit = result.state_bits.at(atom);
            return engine.tcbi_to_var(enc::TCBI(enc::UCBI(bit.expr(), bit.time(), bit.bitno()), frame)) + 1;
        }, [&](const proof::Clause& c) { emit_clause(engine, c); });
    emit_clause(engine, {top});
}
} // namespace sat

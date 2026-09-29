#include <algorithms/reach/interpolation.hh>
#include <env/environment.hh>
#include <query/source.hh>
#include <symb/classes.hh>
#include <symb/symb_iter.hh>

#include <algorithm>
#include <tuple>

namespace reach::interpolation {
namespace {
void tick() { query::checkpoint(query::Phase::compilation); }
expr::Expr_ptr domain(expr::Expr_ptr value, type::Type_ptr type)
{
    tick();
    auto& em = expr::ExprMgr::INSTANCE();
    auto result = em.make_true();
    if (type->is_enum()) {
        result = em.make_false();
        for (auto literal : type->as_enum()->literals()) {
            tick(); result = em.make_or(result, em.make_eq(value, literal));
        }
    } else if (type->is_array()) {
        for (unsigned i = 0; i < type->as_array()->nelems(); ++i) {
            tick();
            result = em.make_and(result, domain(em.make_subscript(value, em.make_const(i)), type->as_array()->of()));
        }
    }
    return result;
}
} // namespace

ModelSystem::ModelSystem(algorithms::Algorithm& algorithm, expr::Expr_ptr target, const expr::ExprVector& assumptions)
    : target_(algorithm.compiler(), target, algorithm.em().make_empty())
{
    auto& em = algorithm.em();
    auto& compiler = algorithm.compiler();
    auto& model = algorithm.model();
    if (&model != &model::ModelMgr::INSTANCE().model() || !algorithm.ok())
        throw std::invalid_argument("Interpolation model does not match the validated snapshot");
    std::vector<std::pair<expr::Expr_ptr, model::Module*>> pending{{em.make_empty(), &model.main_module()}};
    const auto collect = [&](expr::Expr_ptr scope, const expr::ExprVector& init,
                             const expr::ExprVector& invar, const expr::ExprVector& trans) {
        for (auto e : init) { tick(); init_.emplace_back(compiler, e, scope); }
        for (auto e : invar) { tick(); legal_.emplace_back(compiler, e, scope); }
        for (auto e : trans) { tick(); trans_.emplace_back(compiler, e, scope); }
    };
    while (!pending.empty()) {
        tick();
        const auto [scope, module] = pending.back(); pending.pop_back();
        // Module::add_var generates enum membership as equality to a set.
        // Expand that exact domain formula to deterministic Boolean membership
        // before compiling its complement; negating a nondeterministic choice
        // would not denote the complement of the legal-state set.
        auto invar = module->invar();
        for (const auto& [id, variable] : module->vars()) {
            tick();
            if (!variable->type()->is_enum()) continue;
            const auto generated = em.make_eq(id, variable->type()->repr());
            for (auto& clause : invar) {
                tick();
                if (clause == generated) clause = domain(id, variable->type());
            }
        }
        collect(scope, module->init(), invar, module->trans());
        for (const auto& [id, variable] : module->vars()) {
            tick();
            if (variable->type()->is_instance())
                pending.emplace_back(em.make_dot(scope, id), &model.module(variable->type()->as_instance()->name()));
        }
    }
    auto& environment = env::Environment::INSTANCE();
    collect(em.make_empty(), environment.extra_init(), environment.extra_invar(), environment.extra_trans());
    for (auto e : assumptions) { tick(); legal_.emplace_back(compiler, e, em.make_empty()); }

    // Domain constraints are state predicates too, including arrays of enums.
    // Inputs are effective expressions, never additional state coordinates.
    std::vector<std::tuple<std::string, expr::Expr_ptr, symb::Variable*>> variables;
    symb::SymbIter symbols(model);
    while (symbols.has_next()) {
        tick();
        const auto [scope, symbol] = symbols.next();
        if (!symbol->is_variable()) continue;
        auto& variable = symbol->as_variable();
        if (variable.is_input() || variable.is_temp() || variable.type()->is_instance()) continue;
        const auto full = em.make_dot(scope, symbol->name());
        legal_.emplace_back(compiler, domain(symbol->name(), variable.type()), scope);
        variables.emplace_back(source::print(full), full, &variable);
    }
    std::sort(variables.begin(), variables.end());
    auto& encodings = enc::EncodingMgr::INSTANCE();
    for (const auto& [name, full, variable] : variables) {
        tick(); (void)name;
        const expr::TimedExpr key(full, variable->is_frozen() ? FROZEN : 0);
        auto encoding = encodings.find_encoding(key);
        if (!encoding) {
            encoding = encodings.make_encoding(variable->type());
            encodings.register_encoding(key, encoding);
        }
        for (const auto& bit : encoding->bits()) {
            tick();
            bits_.emplace_back(encodings.find_ucbi(bit.getNode()->index), 0);
        }
    }
}

void ModelSystem::legal(sat::Engine& engine, step_t frame, sat::group_t guard) const
{
    for (const auto& clause : legal_) clause.emit(engine, frame, true, guard);
}
void ModelSystem::initial(sat::Engine& engine, step_t frame, bool positive, sat::group_t guard) const
{
    if (positive) {
        legal(engine, frame, guard);
        for (const auto& clause : init_) clause.emit(engine, frame, true, guard);
    } else {
        // NOT(conjunction) is a disjunction of semantic complements. Fresh raw
        // selectors activate individual branches; no selector is assumed true.
        sat::Lits alternatives{sat::mkLit(guard, true)};
        for (const auto* clauses : {&init_, &legal_}) for (const auto& clause : *clauses) {
            query::checkpoint(query::Phase::encoding);
            const auto select = engine.new_sat_var();
            clause.emit(engine, frame, false, select);
            alternatives.push_back(sat::mkLit(select));
        }
        engine.add_clause(alternatives);
    }
}
void ModelSystem::transition(sat::Engine& engine, step_t frame, sat::group_t guard) const
{
    if (frame >= LAST_POSITIVE_TIME) throw std::invalid_argument("Transition exceeds the forward time range");
    legal(engine, frame, guard);
    legal(engine, frame + 1, guard);
    for (const auto& relation : trans_) relation.emit(engine, frame, guard);
}
void ModelSystem::target(sat::Engine& engine, step_t frame, sat::group_t guard) const
{
    legal(engine, frame, guard);
    target_.emit(engine, frame, true, guard);
}
} // namespace reach::interpolation

#ifndef YASMV_QUERY_EXPRESSIONS_HH
#define YASMV_QUERY_EXPRESSIONS_HH
#include <env/environment.hh>
#include <query/runtime.hh>
#include <symb/proxy.hh>
namespace query {
    // Inspect definitions too: a state goal must not hide NEXT behind an alias.
    inline bool state_expression(expr::Expr_ptr e, bool allow_timed = false,
                                 expr::Expr_ptr scope = nullptr, unsigned depth = 0)
    {
        checkpoint(Phase::compilation);
        if (!e) return true;
        if (depth > 512) throw std::invalid_argument("Expression expansion is too deep");
        auto& em = expr::ExprMgr::INSTANCE();
        if (!scope) scope = em.make_empty();
        if (e->symb() == expr::NEXT || e->symb() == expr::ASSIGNMENT) return false;
        if (e->symb() == expr::AT) return allow_timed && state_expression(e->rhs(), allow_timed, scope, depth + 1);
        if (em.is_constant(e) || e->symb() == expr::QSTRING || e->symb() == expr::INSTANT || e->symb() == expr::TYPE) return true;
        if (em.is_dot(e)) return state_expression(e->rhs(), allow_timed, em.make_dot(scope, e->lhs()), depth + 1);
        if (em.is_identifier(e)) {
            symb::ResolverProxy resolver;
            auto symbol = resolver.symbol(em.make_dot(scope, e));
            if (symbol->is_define()) return state_expression(symbol->as_define().body(), allow_timed, scope, depth + 1);
            if (symbol->is_variable() && symbol->as_variable().is_input())
                return state_expression(env::Environment::INSTANCE().get(e), allow_timed, scope, depth + 1);
            return true;
        }
        return state_expression(e->lhs(), allow_timed, scope, depth + 1) && state_expression(e->rhs(), allow_timed, scope, depth + 1);
    }
} // namespace query
#endif

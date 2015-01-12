/**
 *  @file internals.cc
 *
 *  Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU Lesser General Public
 *  License as published by the Free Software Foundation; either
 *  version 2.1 of the License, or (at your option) any later version.
 *
 *  This library is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public
 *  License along with this library; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/

#include <common.hh>

#include <expr/expr.hh>
#include <type/type.hh>
#include <symb/proxy.hh>

#include <model/model_mgr.hh>
#include <model/type_checker/type_checker.hh>

// fun: T -> T
void TypeChecker::walk_unary_fsm_postorder(const Expr_ptr expr)
{ /* no checks */ }

void TypeChecker::walk_unary_ltl_postorder(const Expr_ptr expr)
{ /* no checks */ }

// fun: arithm -> arithm
void TypeChecker::walk_unary_arithmetical_postorder(const Expr_ptr expr)
{ PUSH_TYPE( check_arithmetical(expr->lhs())); }

// fun: logical -> logical
void TypeChecker::walk_unary_logical_postorder(const Expr_ptr expr)
{ PUSH_TYPE( check_logical(expr->lhs())); }

// fun: arithm, arithm -> arithm
void TypeChecker::walk_binary_arithmetical_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();
    Type_ptr rhs_type = check_arithmetical(expr->rhs());
    Type_ptr lhs_type = check_arithmetical(expr->lhs());
    PUSH_TYPE( tm.result_type( expr, lhs_type, rhs_type));
}

// fun: logical x logical -> logical
void TypeChecker::walk_binary_fsm_postorder(const Expr_ptr expr)
{
    Type_ptr rhs_type = check_logical(expr->rhs());
    (void) rhs_type;

    Type_ptr lhs_type = check_logical(expr->lhs());

    PUSH_TYPE( lhs_type );
}

void TypeChecker::walk_binary_ltl_postorder(const Expr_ptr expr)
{
    Type_ptr rhs_type = check_logical(expr->rhs()); (void) rhs_type;
    Type_ptr lhs_type = check_logical(expr->lhs());
    PUSH_TYPE( lhs_type );
}

// fun: logical x logical -> logical
void TypeChecker::walk_binary_logical_postorder(const Expr_ptr expr)
{
    Type_ptr rhs_type = check_logical( expr->rhs()); (void) rhs_type;
    Type_ptr lhs_type = check_logical( expr->lhs());
    PUSH_TYPE( lhs_type );
}

void TypeChecker::walk_binary_cast_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();
    Type_ptr rhs_type = check_arithmetical(expr->rhs());
    Type_ptr lhs_type = check_arithmetical(expr->lhs());
    PUSH_TYPE( tm.result_type( expr, lhs_type, rhs_type ));
}

/* specialized for shift ops (use rhs) */
void TypeChecker::walk_binary_shift_postorder(const Expr_ptr expr)
{
    Type_ptr rhs_type = check_arithmetical(expr->rhs());
    Type_ptr lhs_type = check_arithmetical(expr->lhs()); (void) lhs_type;
    PUSH_TYPE( rhs_type );
}

// fun: arithmetical x arithmetical -> boolean
void TypeChecker::walk_binary_relational_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();

    Type_ptr rhs_type = check_arithmetical(expr->rhs());
    Type_ptr lhs_type = check_arithmetical(expr->lhs());
    PUSH_TYPE( tm.result_type( expr, lhs_type, rhs_type));
}

// fun:  boolean x T -> T
void TypeChecker::walk_ternary_cond_postorder(const Expr_ptr expr)
{
    Type_ptr rhs_type = f_type_stack.back(); f_type_stack.pop_back();
    Type_ptr lhs_type = check_logical(expr->lhs()); (void) lhs_type;
    PUSH_TYPE( rhs_type );
}

// fun: (boolean ? T) x T -> T
void TypeChecker::walk_ternary_ite_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();

    POP_TYPE(rhs);
    POP_TYPE(lhs);

    Type_ptr res = tm.result_type( expr, tm.find_boolean(), lhs, rhs);
    PUSH_TYPE(res);
}

void TypeChecker::memoize_result (Expr_ptr expr)
{
    Type_ptr type = f_type_stack.back();
    f_map[ FQExpr(f_ctx_stack.back(),
                  find_canonical_expr(expr)) ] = type;
}

/* This is used to attempt for a better memoization, but it's not
   really critical */
Expr_ptr TypeChecker::find_canonical_expr(Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();

    /* time is not relevant here */
    while (em.is_next(expr)) {
        expr = expr->lhs();
    }

    if (em.is_unary_ltl(expr)) {
        return em.make_F(expr->lhs());
    }
    else if (em.is_binary_relational(expr)) {
        return em.make_lt(expr->lhs(), expr->rhs());
    }
    else if (em.is_binary_arithmetical(expr)) {
        return em.make_add(expr->lhs(), expr->rhs());
    }
    else if (em.is_binary_logical(expr)) {
        return em.make_and(expr->lhs(), expr->rhs());
    }
    else if (em.is_subscript(expr)) {
        return em.make_subscript(expr->lhs(),
                                 find_canonical_expr( expr->rhs()));
    }
    else if (em.is_params(expr)) {
        return em.make_subscript(expr->lhs(),
                                 find_canonical_expr( expr->rhs()));
    }
    else if (em.is_binary_ltl(expr)) {
        return em.make_U(find_canonical_expr( expr->lhs()),
                         find_canonical_expr( expr->rhs()));
    }
    else if (em.is_comma(expr)) {
        return em.make_comma(find_canonical_expr( expr->lhs()),
                             find_canonical_expr( expr->rhs()));
    }
    else if (em.is_cast(expr)) {
        return em.make_cast( find_canonical_expr( expr->lhs()),
                             find_canonical_expr( expr->rhs()));
    }
    else if (em.is_type(expr)) {
        return em.make_type( find_canonical_expr( expr->lhs()),
                             find_canonical_expr( expr->rhs()));
    }

    /* no rewrites */
    else if (em.is_dot(expr) ||
             em.is_unary_arithmetical(expr) ||
             em.is_unary_logical(expr) ||
             em.is_ite(expr) ||
             em.is_cond(expr) ||
             em.is_identifier(expr) ||
             em.is_int_numeric(expr)) {
        return expr;
    }

    DEBUG << expr << std::endl;
    assert ( false ); // unreachable
}

Type_ptr TypeChecker::type(Expr_ptr expr, Expr_ptr ctx)
{
    /* to avoid a number of cache misses due to compiler rewrites,
       we squeeze types in equivalence classes: Relationals -> lhs
       '<' rhs, Arithmetical -> lhs '+' rhs */
    FQExpr key( ctx, find_canonical_expr( expr));

    TypeReg::const_iterator eye = f_map.find(key);
    Type_ptr res = NULL;

    // cache miss, fallback to walker
    if (eye == f_map.end()) {
        res = process( expr, ctx);
    }
    else {
        res = (*eye).second;
    }

    assert(NULL != res);
    return res;
}

void TypeChecker::pre_hook()
{}
void TypeChecker::post_hook()
{}

void TypeChecker::pre_node_hook(Expr_ptr expr)
{}

void TypeChecker::post_node_hook(Expr_ptr expr)
{ memoize_result(expr); }

Type_ptr TypeChecker::check_logical(Expr_ptr expr)
{
    POP_TYPE(res);
    assert (NULL != res);

    if (res -> is_boolean())
        return res;

    throw BadType(expr, res);
    return NULL; /* unreachable */
}

Type_ptr TypeChecker::check_arithmetical(Expr_ptr expr)
{
    POP_TYPE(res);
    assert (NULL != res);

    if (res -> is_algebraic())
        return res;

    throw BadType(expr, res);
    return NULL; /* unreachable */
}

Type_ptr TypeChecker::check_scalar(Expr_ptr expr)
{
    POP_TYPE(res);
    assert (NULL != res);

    if (res -> is_scalar())
        return res;

    throw BadType(expr, res);
    return NULL; /* unreachable */
}

Type_ptr TypeChecker::check_array(Expr_ptr expr)
{
    POP_TYPE(res);
    assert (NULL != res);

    if (res -> is_array())
        return res;

    throw BadType(expr, res);
    return NULL; /* unreachable */
}


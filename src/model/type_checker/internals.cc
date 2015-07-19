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
{ PUSH_TYPE( check_logical(expr->lhs())); }

// fun: arithm -> arithm
void TypeChecker::walk_unary_arithmetical_postorder(const Expr_ptr expr)
{ PUSH_TYPE( check_arithmetical(expr->lhs())); }

// fun: logical -> logical
void TypeChecker::walk_unary_logical_postorder(const Expr_ptr expr)
{ PUSH_TYPE( check_logical(expr->lhs())); }

// fun: arithm, arithm -> arithm
void TypeChecker::walk_binary_arithmetical_postorder(const Expr_ptr expr)
{
    Type_ptr rhs
        (check_arithmetical(expr->rhs()));

    Type_ptr lhs
        (check_arithmetical(expr->lhs()));

    // matching types are most definitely ok
    if (rhs == lhs ) {
        PUSH_TYPE(rhs);
        return ;
    }

    AlgebraicType_ptr arhs
        (dynamic_cast <AlgebraicType_ptr>(rhs));

    AlgebraicType_ptr alhs
        (dynamic_cast <AlgebraicType_ptr>(lhs));

    if (alhs -> width() != arhs -> width())
        throw TypeMismatch( expr, alhs, arhs );

    if (arhs -> is_constant() && ! alhs -> is_constant()) {
        PUSH_TYPE(alhs);
        return ;
    }

    if (alhs -> is_constant() && ! arhs -> is_constant()) {
        PUSH_TYPE(arhs);
        return ;
    }

    assert( false );
}

// fun: logical x logical -> logical
void TypeChecker::walk_binary_fsm_postorder(const Expr_ptr expr)
{
    Type_ptr rhs_type = check_logical(expr->rhs()); (void) rhs_type;
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
    assert( false );
    // TODO
#if 0
    Type_ptr rhs_type = check_arithmetical(expr->rhs());
    Type_ptr lhs_type = check_arithmetical(expr->lhs());
    PUSH_TYPE( result_type( expr, lhs_type, rhs_type ));
#endif
}

void TypeChecker::walk_binary_shift_postorder(const Expr_ptr expr)
{
    Type_ptr rhs_type = check_arithmetical(expr->rhs());
    Type_ptr lhs_type = check_arithmetical(expr->lhs()); (void) lhs_type;
    PUSH_TYPE( rhs_type );
}

// fun: arithmetical x arithmetical -> boolean
void TypeChecker::walk_binary_relational_postorder(const Expr_ptr expr)
{
    TypeMgr& tm
        (f_owner.tm());

    Type_ptr boolean
        (tm.find_boolean());

    Type_ptr rhs
        (check_arithmetical(expr->rhs()));

    Type_ptr lhs
        (check_arithmetical(expr->lhs()));

    // matching types are most definitely ok
    if (rhs == lhs ) {
        PUSH_TYPE(boolean);
        return ;
    }

    AlgebraicType_ptr arhs
        (dynamic_cast <AlgebraicType_ptr>(rhs));

    AlgebraicType_ptr alhs
        (dynamic_cast <AlgebraicType_ptr>(lhs));

    if (alhs -> width() != arhs -> width())
        throw TypeMismatch( expr, alhs, arhs );

    if (arhs -> is_constant() && ! alhs -> is_constant()) {
        PUSH_TYPE(boolean);
        return ;
    }

    if (alhs -> is_constant() && ! arhs -> is_constant()) {
        PUSH_TYPE(boolean);
        return ;
    }
}

// fun: logical/arithmetical/enum x logical/arithmetical/enum -> boolean
void TypeChecker::walk_binary_equality_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();
    POP_TYPE(rhs_type);

    if (rhs_type -> is_boolean()) {
        Type_ptr lhs_type = check_logical(expr->lhs()); (void) lhs_type;
        PUSH_TYPE( tm.find_boolean());
    }
    else if (rhs_type -> is_algebraic()) {
        Type_ptr lhs_type = check_arithmetical(expr->lhs());

        if (rhs_type == lhs_type)  {
            PUSH_TYPE( tm.find_boolean());
            return ;
        }

        if (lhs_type -> width() !=
            rhs_type -> width())
            throw TypeMismatch( expr, lhs_type, rhs_type );

        if (rhs_type -> is_constant() &&
            ! lhs_type -> is_constant()) {
            PUSH_TYPE( tm.find_boolean());
            return ;
        }

        if (lhs_type -> is_constant() &&
            ! rhs_type -> is_constant()) {
            PUSH_TYPE( tm.find_boolean());
            return ;
        }

        assert(false);
    }
    else if (rhs_type -> is_enum()) {
        POP_TYPE( lhs_type );
        if (lhs_type != rhs_type)
            throw TypeMismatch(expr, lhs_type, rhs_type);

        PUSH_TYPE( tm.find_boolean());
    }
    else if (rhs_type -> is_array()) {
        POP_TYPE( lhs_type );
        if (lhs_type != rhs_type)
            throw TypeMismatch(expr, lhs_type, rhs_type);

        PUSH_TYPE( tm.find_boolean());
    }
    else assert(false);
}

// fun: (boolean ? T) x T -> T
void TypeChecker::walk_ternary_ite_postorder(const Expr_ptr expr)
{
    POP_TYPE(rhs_type);
    POP_TYPE(lhs_type);

    POP_TYPE(cnd);
    if (! cnd -> is_boolean())
        throw BadType( expr -> lhs() -> lhs(), cnd );

    PUSH_TYPE(lhs_type);
    if (rhs_type -> is_boolean()) {
        Type_ptr lhs_type = check_logical(expr->lhs()); (void) lhs_type;
        PUSH_TYPE( TypeMgr::INSTANCE().find_boolean());
    }
    else if (rhs_type -> is_algebraic()) {
        Type_ptr lhs_type = check_arithmetical(expr->lhs());

        if (rhs_type == lhs_type)  {
            PUSH_TYPE( rhs_type );
            return ;
        }

        if (lhs_type -> width() !=
            rhs_type -> width())
            throw TypeMismatch( expr, lhs_type, rhs_type );

        if (rhs_type -> is_constant() &&
            ! lhs_type -> is_constant()) {
            PUSH_TYPE( rhs_type );
            return ;
        }

        if (lhs_type -> is_constant() &&
            ! rhs_type -> is_constant()) {
            PUSH_TYPE( lhs_type );
            return ;
        }

        assert(false);
    }
    else if (rhs_type -> is_enum()) {
        POP_TYPE( lhs_type );
        if (lhs_type != rhs_type)
            throw TypeMismatch(expr, lhs_type, rhs_type);

        PUSH_TYPE( rhs_type );
    }
    else assert(false);
}

void TypeChecker::memoize_result (Expr_ptr expr)
{
    Expr_ptr key
        (f_owner.em().make_dot( f_ctx_stack.back(), expr));
    Type_ptr type
        (f_type_stack.back());

    f_map[ key ] = type;
}

Type_ptr TypeChecker::type(Expr_ptr expr, Expr_ptr ctx)
{
    /* to avoid a number of cache misses due to compiler rewrites,
       we squeeze types in equivalence classes: Relationals -> lhs
       '<' rhs, Arithmetical -> lhs '+' rhs */
    Expr_ptr key
        (f_owner.em().make_dot(ctx, expr));

    TypeReg::const_iterator eye
        (f_map.find(key));
    Type_ptr res
        (NULL);

    // cache miss, fallback to walker
    if (eye == f_map.end())
        res = process( expr, ctx);
    else
        res = (*eye).second;

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

// services
bool TypeChecker::cache_miss(const Expr_ptr expr)
{
    ExprMgr& em
        (f_owner.em());
    Expr_ptr key
        (em.make_dot( f_ctx_stack.back(), expr));

    TypeReg::iterator eye
        (f_map.find(key));

    if (eye != f_map.end()) {
        Type_ptr res = (*eye).second;
        PUSH_TYPE(res);
        return false;
    }

    return true;
}



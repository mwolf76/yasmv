/**
 *  @file analysis.cc
 *
 *  Copyright (C) 2011-2015 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
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
#include <compiler.hh>

bool Compiler::is_binary_boolean(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    Expr_ptr ctx (f_ctx_stack.back());

    /* AND, OR, XOR, XNOR, IFF, IMPLIES */
    if (em.is_binary_logical(expr))

        return (f_owner.type(expr->lhs(), ctx) -> is_boolean() &&
                f_owner.type(expr->rhs(), ctx) -> is_boolean());

    return false;
}

bool Compiler::is_binary_enumerative(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    Expr_ptr ctx (f_ctx_stack.back());

    /* AND (bw), OR(bw), XOR(bw), XNOR(bw), IFF(bw),
       IMPLIES(bw), LT, LE, GT, GE, EQ, NE, PLUS, SUB, DIV, MUL, MOD */
    if ((em.is_binary_arithmetical(expr)) ||
        (em.is_binary_relational(expr)))

        return (f_owner.type(expr->lhs(), ctx) -> is_enum() &&
                f_owner.type(expr->rhs(), ctx) -> is_enum() );

    return false;
}

bool Compiler::is_binary_algebraic(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    Expr_ptr ctx (f_ctx_stack.back());

    if ((em.is_binary_logical(expr)) ||
        (em.is_binary_arithmetical(expr)) ||
        (em.is_binary_relational(expr)))

        return
            f_owner.type(expr->rhs(), ctx) -> is_algebraic() &&
            f_owner.type(expr->lhs(), ctx) -> is_algebraic();

    return false;
}

bool Compiler::is_unary_boolean(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    Expr_ptr ctx (f_ctx_stack.back());

    /*  NOT, () ? */
    if (em.is_unary_logical(expr))
        return f_owner.type(expr->lhs(), ctx) -> is_boolean();

    return false;
}

bool Compiler::is_unary_enumerative(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    Expr_ptr ctx (f_ctx_stack.back());

    /* unary : ? (), : (), NEG, NOT(bw) */
    if (em.is_unary_arithmetical(expr))
        return (f_owner.type(expr->lhs(), ctx) -> is_enum());

    return false;
}

/* checks lhs is array, and rhs is algebraic */
bool Compiler::is_subscript_algebraic(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    Expr_ptr ctx (f_ctx_stack.back());

    /* SUBSCRIPT */
    if (em.is_subscript(expr)) {

        FQExpr rhs(f_ctx_stack.back(), expr->rhs());
        FQExpr lhs(f_ctx_stack.back(), expr->lhs());
        return (f_owner.type(expr->lhs(), ctx) -> is_array() &&
                f_owner.type(expr->rhs(), ctx) -> is_algebraic()) ;
    }

    return false;
}

bool Compiler::is_unary_algebraic(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    Expr_ptr ctx (f_ctx_stack.back());

    if ((em.is_unary_logical(expr)) ||
        (em.is_unary_arithmetical(expr)))

        return f_owner.type(expr->lhs(), ctx) -> is_algebraic();

    return false;
}

/* same as is_binary_boolean, checks only lhs and rhs */
bool Compiler::is_ite_boolean(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    Expr_ptr ctx (f_ctx_stack.back());

    /* ITE */
    if (em.is_ite(expr))
        return (f_owner.type(expr->lhs(), ctx) -> is_boolean() &&
                f_owner.type(expr->rhs(), ctx) -> is_boolean()) ;

    return false;
}

/* same as  is_binary_enumerative, checks only lhs and rhs */
bool Compiler::is_ite_enumerative(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    Expr_ptr ctx (f_ctx_stack.back());

    /* ITE (bw) */
    if (em.is_ite(expr))
        return (f_owner.type(expr->lhs(), ctx) -> is_enum() &&
                f_owner.type(expr->rhs(), ctx) -> is_enum()) ;

    return false;
}

/* similar to is_binary_algebraic, checks only lhs and rhs */
bool Compiler::is_ite_algebraic(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    Expr_ptr ctx (f_ctx_stack.back());

    if (em.is_ite(expr))
        return
            f_owner.type(expr-> rhs(), ctx) -> is_algebraic() &&
            f_owner.type(expr-> lhs(), ctx) -> is_algebraic();

    return false;
}


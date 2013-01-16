/**
 *  @file integer.cc
 *  @brief Boolean compiler - integer consts manipulations
 *
 *  This module contains definitions and services that implement the
 *  booolean expressions compilation into a form which is suitable for
 *  the SAT analysis. Current implementation uses ADDs to perform
 *  expression manipulation and booleanization. Expressions are
 *  assumed to be type-safe, only boolean expressions on arithmetic
 *  predicates are supported. The final result of expression
 *  compilation must be a 0-1 ADD which is suitable for CNF clauses
 *  injection directly into the SAT solver. The compilation engine is
 *  implemented using a simple walker pattern: (a) on preorder, return
 *  true if the node has not yet been visited; (b) always do in-order
 *  (for binary nodes); (c) perform proper compilation in post-order
 *  hooks.
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

#include <expr.hh>
#include <compiler.hh>

void Compiler::integer_neg(const Expr_ptr expr)
{
    const ADD top = f_add_stack.back(); f_add_stack.pop_back();

    f_add_stack.push_back(top.Negate());
}

void Compiler::integer_plus(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();

    f_add_stack.push_back(lhs.Plus(rhs));
    f_type_stack.pop_back(); // consume one, leave the other
}

void Compiler::integer_sub(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();

    f_add_stack.push_back(lhs.Minus(rhs));
    f_type_stack.pop_back(); // consume one, leave the other
}

void Compiler::integer_mul(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();

    f_add_stack.push_back(lhs.Times(rhs));
    f_type_stack.pop_back(); // consume one, leave the other
}

void Compiler::integer_div(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();

    f_add_stack.push_back(lhs.Divide(rhs));
    f_type_stack.pop_back(); // consume one, leave the other
}

void Compiler::integer_mod(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();

    f_add_stack.push_back(lhs.Modulus(rhs));
    f_type_stack.pop_back(); // consume one, leave the other
}

void Compiler::integer_and(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();

    f_add_stack.push_back(lhs.BWTimes(rhs)); /* bitwise integer arithmetic */
    f_type_stack.pop_back(); // consume one, leave the other
}

void Compiler::integer_or(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();

    f_add_stack.push_back(lhs.BWOr(rhs)); /* bitwise integer arithmetic */
    f_type_stack.pop_back(); // consume one, leave the other
}

void Compiler::integer_xor(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();

    f_add_stack.push_back(lhs.BWXor(rhs)); /* bitwise integer arithmetic */
    f_type_stack.pop_back(); // consume one, leave the other
}

void Compiler::integer_xnor(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();

    f_add_stack.push_back(lhs.BWXnor(rhs)); /* bitwise integer arithmetic */
    f_type_stack.pop_back(); // consume one, leave the other
}

void Compiler::integer_implies(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();

    f_add_stack.push_back(lhs.BWCmpl().BWXor(rhs)); /* bitwise integer arithmetic */
    f_type_stack.pop_back(); // consume one, leave the other
}

void Compiler::integer_lshift(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();

    f_add_stack.push_back(lhs.LShift(rhs)); /* bitwise integer arithmetic */
    f_type_stack.pop_back(); // consume one, leave the other
}

void Compiler::integer_rshift(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();

    f_add_stack.push_back(lhs.RShift(rhs)); /* bitwise integer arithmetic */
    f_type_stack.pop_back(); // consume one, leave the other
}

void Compiler::integer_equals(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();

    f_add_stack.push_back(lhs.Equals(rhs));
    f_type_stack.pop_back(); // consume one, leave the other
}

void Compiler::integer_not_equals(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();

    f_add_stack.push_back(lhs.Equals(rhs).Cmpl());
    f_type_stack.pop_back(); // consume one, leave the other
}

void Compiler::integer_gt(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();

    f_add_stack.push_back(rhs.LT(lhs)); // simulate GT op
    f_type_stack.pop_back(); // consume one, leave the other
}

void Compiler::integer_ge(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();

    f_add_stack.push_back(rhs.LEQ(lhs)); // simulate GEQ op
    f_type_stack.pop_back(); // consume one, leave the other
}

void Compiler::integer_lt(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();

    f_add_stack.push_back(lhs.LT(rhs));
    f_type_stack.pop_back(); // consume one, leave the other
}

void Compiler::integer_le(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();

    f_add_stack.push_back(lhs.LEQ(rhs));
    f_type_stack.pop_back(); // consume one, leave the other
}

void Compiler::integer_ite(const Expr_ptr expr)
{
#if 0 // LATER
    TypeMgr& tm = f_owner.tm();

    FQExpr key(expr); const Type_ptr type = f_owner.type(key);
    unsigned width = tm.as_algebraic(type)->width();

    const ADD tmp = f_add_stack.back(); f_add_stack.pop_back();
    algebraic_from_integer_const(width); // rhs

    f_add_stack.push_back(tmp);
    algebraic_from_integer_const(width);  // lhs

    /* fix type stack, constants are always unsigned */
    f_type_stack.pop_back();
    f_type_stack.pop_back();
    f_type_stack.push_back( tm.find_unsigned( width ));
    f_type_stack.push_back( tm.find_unsigned( width ));

    /* re-uses general algorithm */
    algebraic_ite(expr);
#endif
}

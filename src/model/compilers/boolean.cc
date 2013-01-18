/**
 *  @file boolean.cc
 *  @brief Boolean compiler - boolean manipulations
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

void Compiler::boolean_not(const Expr_ptr expr)
{
    POP_ADD(lhs);
    f_add_stack.push_back(lhs.Cmpl());
}

void Compiler::boolean_and(const Expr_ptr expr)
{
    POP_TWO(rhs, lhs);
    PUSH_ADD(lhs.Times(rhs)); /* 0, 1 logic uses arithmetic product for AND */

    f_type_stack.pop_back(); // consume one, leave the other
}

void Compiler::boolean_or(const Expr_ptr expr)
{
    POP_TWO(rhs, lhs);
    PUSH_ADD(lhs.Or(rhs));

    f_type_stack.pop_back(); // consume one, leave the other
}

void Compiler::boolean_xor(const Expr_ptr expr)
{
    POP_TWO(rhs, lhs);
    PUSH_ADD(lhs.Xor(rhs));

    f_type_stack.pop_back(); // consume one, leave the other
}

void Compiler::boolean_xnor(const Expr_ptr expr)
{
    POP_TWO(rhs, lhs);
    PUSH_ADD(lhs.Xnor(rhs));

    f_type_stack.pop_back(); // consume one, leave the other
}

void Compiler::boolean_implies(const Expr_ptr expr)
{
    POP_TWO(rhs, lhs);
    PUSH_ADD(lhs.Cmpl().Or(rhs));

    f_type_stack.pop_back(); // consume one, leave the other
}

// just aliases..
void Compiler::boolean_equals(const Expr_ptr expr)
{ boolean_xnor(expr); }
void Compiler::boolean_not_equals(const Expr_ptr expr)
{ boolean_xor(expr); }

void Compiler::boolean_ite(const Expr_ptr expr)
{
    POP_TWO(rhs, lhs);
    POP_ADD(cnd);
    PUSH_ADD(cnd.Ite(lhs, rhs));

    // consume two operand types, leave the third
    f_type_stack.pop_back();
    f_type_stack.pop_back();
}

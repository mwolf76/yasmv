/**
 *  @file fixed.cc
 *  @brief Boolean compiler - fixed consts manipulations
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
#define PROFILE_COMPILER

#include <common.hh>

#include <expr.hh>
#include <compiler.hh>

void Compiler::fixed_neg(const Expr_ptr expr)
{ integer_neg(expr); }

void Compiler::fixed_plus(const Expr_ptr expr)
{ integer_plus(expr); }

void Compiler::fixed_sub(const Expr_ptr expr)
{ integer_sub(expr); }

void Compiler::fixed_mul(const Expr_ptr expr)
{
    assert( false ); // TODO
}

void Compiler::fixed_div(const Expr_ptr expr)
{
        assert( false ); // TODO
}

void Compiler::fixed_mod(const Expr_ptr expr)
{
        assert( false ); // TODO
}

void Compiler::fixed_equals(const Expr_ptr expr)
{ integer_equals(expr); }

void Compiler::fixed_not_equals(const Expr_ptr expr)
{ integer_not_equals(expr); }

void Compiler::fixed_gt(const Expr_ptr expr)
{ integer_gt(expr); }

void Compiler::fixed_ge(const Expr_ptr expr)
{ integer_ge(expr); }

void Compiler::fixed_lt(const Expr_ptr expr)
{ integer_lt(expr); }

void Compiler::fixed_le(const Expr_ptr expr)
{ integer_le(expr); }

void Compiler::fixed_ite(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();

    FQExpr key(expr); const Type_ptr type = f_owner.type(key);
    unsigned width = tm.calculate_width(type);

    assert( 0 == f_tmp_stack.size() );
    algebraic_from_fxd_const(width); // rhs
    algebraic_from_fxd_const(width); // lhs
    flush_operands();

    /* fix type stack, constants are always unsigned */
    f_type_stack.pop_back();
    f_type_stack.pop_back();
    f_type_stack.push_back( type );
    f_type_stack.push_back( type );

    /* re-uses general algorithm */
    algebraic_ite(expr);
}
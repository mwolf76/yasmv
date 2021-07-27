/**
 * @file expr/walker/typedefs.hh
 * @brief Expression walker pattern implementation, type definitions.
 *
 * This header file contains the declarations required by the Expression
 * Walker class.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/

#ifndef EXPR_WALKER_TYPEDEFS_H
#define EXPR_WALKER_TYPEDEFS_H

#include <expr/expr.hh>
#include <stack>

namespace expr {

// enums in C++ are non-extensible, thus we have to keep all possible
// values together in one place.
typedef enum {
    DEFAULT,
    RETURN,

    // -- LTL ops
    F_1,
    G_1,
    X_1,
    U_1, U_2,
    R_1, R_2,

    // -- Simple walkers
    AT_1, AT_2, NEXT_1, PREV_1, NEG_1, NOT_1, BW_NOT_1,

    PLUS_1, PLUS_2,
    SUB_1, SUB_2,
    MUL_1, MUL_2,
    DIV_1, DIV_2,
    MOD_1, MOD_2,

    AND_1, AND_2,
    BW_AND_1, BW_AND_2,

    OR_1, OR_2,
    BW_OR_1, BW_OR_2,

    BW_XOR_1, BW_XOR_2,
    BW_XNOR_1, BW_XNOR_2,

    GUARD_1, GUARD_2,
    IMPLIES_1, IMPLIES_2,

    RSHIFT_1, RSHIFT_2,
    LSHIFT_1, LSHIFT_2,

    ASSIGNMENT_1, ASSIGNMENT_2,

    EQ_1, EQ_2,
    NE_1, NE_2,
    GT_1, GT_2,
    GE_1, GE_2,
    LT_1, LT_2,
    LE_1, LE_2,

    // ite
    ITE_1, ITE_2,
    COND_1, COND_2,

    // dot notation for identifiers
    DOT_1, DOT_2,

    // subscripts ([])
    SUBSCRIPT_1, SUBSCRIPT_2,

    // sets ({})
    SET_1,
    SET_COMMA_1, SET_COMMA_2,

    // arrays ([])
    ARRAY_1,
    ARRAY_COMMA_1, ARRAY_COMMA_2,

    // params (())
    PARAMS_1, PARAMS_2,

    CAST_1, CAST_2,
    TYPE_1, TYPE_2,

} entry_point;

// reserved for expr walkers
struct activation_record {
    entry_point pc;
    Expr_ptr expr;

    activation_record(const Expr_ptr e)
        : pc(DEFAULT)
        , expr(e)
    {}
};

typedef std::stack<struct activation_record> walker_stack;

};

#endif /* EXPR_WALKER_TYPEDEFS_H */

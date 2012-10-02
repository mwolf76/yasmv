/**
 *  @file expr_walker.hh
 *  @brief Expression algorithm-unaware walk pattern implementation
 *
 *  This module contains definitions and services that implement an
 *  optimized storage for expressions. Expressions are stored in a
 *  Directed Acyclic Graph (DAG) for data sharing.
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

#ifndef EXPR_WALKER_H
#define EXPR_WALKER_H

#include <common.hh>
#include <expr.hh>

// enums in C++ are non-extensible, thus we have to keep all possible
// values together in one place.
typedef enum {
    DEFAULT,
    RETURN,

    F_1, G_1, X_1, U_1, U_2, R_1, R_2,
    AF_1, AG_1, AX_1, AU_1, AU_2, AR_1, AR_2,
    EF_1, EG_1, EX_1, EU_1, EU_2, ER_1, ER_2,

    NEXT_1,
    NEG_1,
    NOT_1,

    PLUS_1, PLUS_2, // FIXME: when proper cudd namespace is established, I *want* ADD back here!
    SUB_1, SUB_2,
    MUL_1, MUL_2,
    DIV_1, DIV_2,
    MOD_1, MOD_2,

    AND_1, AND_2,
    OR_1, OR_2,

    XOR_1, XOR_2,
    XNOR_1, XNOR_2,

    IMPLIES_1, IMPLIES_2,
    IFF_1, IFF_2,

    RSHIFT_1, RSHIFT_2,
    LSHIFT_1, LSHIFT_2,

    EQ_1, EQ_2,
    NE_1, NE_2,
    GT_1, GT_2,
    GE_1, GE_2,
    LT_1, LT_2,
    LE_1, LE_2,

    ITE_1, ITE_2,
    COND_1, COND_2,

    DOT_1, DOT_2,

} entry_point;

// reserved for walkers
struct activation_record {
    entry_point pc;
    Expr_ptr expr;

    activation_record(const Expr_ptr e)
        : pc(DEFAULT) , expr(e)
    {}
};

typedef stack<struct activation_record> walker_stack;

class WalkerException : public Exception
{};

// raised when the walker has encountered an unsupported entry point
class UnsupportedEntryPointException : public WalkerException {
public:
    UnsupportedEntryPointException(entry_point ep)
        : f_ep(ep)
    {}

    virtual const char* what() const throw() {
        ostringstream oss;
        oss << "Unsupported entry point (" << f_ep << ")";
        return oss.str().c_str();
    }

private:
    entry_point f_ep;
};

// reaised when the walker has encountered an unsupported operator
class UnsupportedOperatorException : public WalkerException {
public:
    UnsupportedOperatorException(ExprType et)
        : f_et(et)
    {}

    virtual const char* what() const throw() {
        ostringstream oss;
        oss << "Unsupported operator (" << f_et << ")";
        return oss.str().c_str();
    }

private:
    ExprType f_et;
};

// walker base class
class Walker {
public:
    Walker();
    virtual ~Walker();

    virtual Walker& operator() (const Expr_ptr expr);

protected:
    walker_stack f_recursion_stack;

    // extra-hooks
    virtual void pre_hook()
    {}
    virtual void post_hook()
    {}

    virtual void walk() =0;
};

#endif

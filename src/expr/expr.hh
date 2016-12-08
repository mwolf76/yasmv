/**
 * @file expr.hh
 * @brief Expression management
 *
 * This header file contains the declarations required by the Expr
 * struct.
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

#ifndef EXPR_H
#define EXPR_H

#include <set>
#include <vector>

#include <common/common.hh>

#include <expr/atom.hh>

typedef enum {

    // -- linear temporal logic expressions ------------------------------------
    F, G, X, U, R,

    // -- primary expressions --------------------------------------------------

    /* time shift operator (nesting supported) */
    NEXT,

    /* arithmetical operators */
    NEG, PLUS, SUB, DIV, MUL, MOD,

    /* bitwise operators */
    BW_NOT, BW_AND, BW_OR, BW_XOR, BW_XNOR,

    /* logical operators */
    NOT, AND, OR, IMPLIES, GUARD /* reserved for TRANSes */,

    /* shift operators */
    LSHIFT, RSHIFT,

    /* type operators */
    TYPE, CAST,

    /* assignment operator */
    ASSIGNMENT,

    /* relational operators */
    EQ, NE, GE, GT, LE, LT,

    /* conditionals */
    ITE, COND,

    /* identifiers */
    IDENT, DOT,

    /* declarations */
    BOOL, SIGNED, UNSIGNED,

    /* defines */
    PARAMS, // (), binary
    PARAMS_COMMA,

    /* arrays */
    ARRAY, // [] unary
    ARRAY_COMMA,

    SUBSCRIPT, // [], binary

    SET, // {}, unary
    SET_COMMA,

    // -- Nullary
    ICONST, // decimal constants
    HCONST, // hex constants
    OCONST, // octal constants
    BCONST, // binary constants

    // undefined
    UNDEF,

} ExprType;

// An Expression consists of an AST symbol, which is the expression
// main operator, operands which depend on the type of operator and a
// context, in which the expression has to evaluated.
typedef struct Expr_TAG *Expr_ptr;
typedef struct Expr_TAG {

    // AST symb type
    ExprType f_symb;

    union {
        // identifiers
        Atom_ptr f_atom;

        // numeric constants
        value_t f_value;

        // operators
        struct  {
            Expr_ptr f_lhs;
            Expr_ptr f_rhs; // NULL for unary ops
        };
    } u;

    // accessors
    inline ExprType symb() const
    { return f_symb; }

    inline Atom& atom() const
    {
        assert (IDENT == f_symb);
        return *u.f_atom;
    }

    value_t value() const;

    inline Expr_ptr lhs()
    { return u.f_lhs; }
    inline Expr_ptr rhs()
    { return u.f_rhs; }

    // identifiers
    inline Expr_TAG(const Atom& atom)
    : f_symb(IDENT)
    { u.f_atom = const_cast<Atom *>(& atom); }

    // binary expr (rhs is NULL for unary ops)
    inline Expr_TAG(ExprType symb, Expr_ptr lhs, Expr_ptr rhs)
        : f_symb(symb)
    {
        u.f_lhs = lhs;
        u.f_rhs = rhs;
    }

    // numeric constants, are treated as machine size consts.
    inline Expr_TAG(ExprType symb, value_t value)
        : f_symb(symb)
    {
        assert (symb == ICONST ||
                symb == HCONST ||
                symb == OCONST ||
                symb == BCONST);

        u.f_value = value;
    }

    // nullary nodes (errors, undefined)
    inline Expr_TAG(ExprType symb)
        : f_symb(symb)
    {
        assert( symb == UNDEF );
    }

} Expr;

typedef std::vector<Expr_ptr> ExprVector;
typedef ExprVector* ExprVector_ptr;

struct LexicographicOrdering {
    int operator() (const Expr_ptr x, const Expr_ptr y) const;
};

typedef std::set<Expr_ptr, LexicographicOrdering> ExprSet;
typedef ExprSet* ExprSet_ptr;

std::ostream& operator<<(std::ostream& os, const Expr_ptr expr);

struct ExprHash {
    long operator() (const Expr& k) const;
};

struct ExprEq {
    bool operator() (const Expr& x, const Expr& y) const;
};

typedef boost::unordered_set<Expr, ExprHash, ExprEq> ExprPool;
typedef std::pair<ExprPool::iterator, bool> ExprPoolHit;

/* FIXME: how does this stuff belong here?!? */

/** -- shortcurts to simplify the manipulation of the internal ctx stack -- */
#define TOP_CTX(tp)                            \
    const Expr_ptr (tp)(f_ctx_stack.back())

#define DROP_CTX()                             \
    f_ctx_stack.pop_back()

#define POP_CTX(tp)                            \
    TOP_CTX(tp); DROP_CTX()

#define PUSH_CTX(tp)                           \
    f_ctx_stack.push_back(tp)

/** -- shortcurts to simplify the manipulation of the internal time stack -- */
#define TOP_TIME(step)                          \
    const step_t (step)(f_time_stack.back())

#define DROP_TIME()                             \
    f_time_stack.pop_back()

#define POP_TIME(step)                          \
    TOP_TIME(step); DROP_TIME()

#define PUSH_TIME(step)                         \
    f_time_stack.push_back(step)

#endif /* EXPR_H */

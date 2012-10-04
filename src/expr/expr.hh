/**
 *  @file expr.hh
 *  @brief Expression management
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
#ifndef EXPR_H
#define EXPR_H

#include <common.hh>
#include <atom.hh>

typedef enum {

    // -- primary expressions --------------------------------------------------

    /* propositional next (nesting supported) */
    NEXT,

    /* arithmetical operators */
    NEG, PLUS, SUB, DIV, MUL, MOD,

    /* logical/bitwise operators */
    NOT, AND, OR, XOR, XNOR, IMPLIES, IFF, LSHIFT, RSHIFT,

    // future
    // LROTATE, RROTATE,

    /* relational operators */
    EQ, NE, GE, GT, LE, LT,

    /* conditionals */
    ITE, COND,

    /* leaves */
    ICONST, UWCONST, SWCONST, IDENT, DOT, NIL,

    /* future
    COUNT, // count( <pred>, x0, ..., xk ) -> number of elems satisfying pred
    ANY,   // any( <pred>, x0, ..., xk ) -> pick one elem among those satisfying pred

    -- PRED is_even(x) := (x % 2 == 0); // unary predicate
    -- PRED ALL(x) := TRUE              //

    -- COUNT (is_even, a, b, c, d)
    -- ANY( { TRUE }, a, b, c, d) // perl-like

    */

    // -- temporal logic ops ---------------------------------------------------

    /* LTL ops */
    F, G, X, U, R,

    /* CTL ops */
    AF, EF, AG, EG, AX, EX, AU, EU, AR, ER,

    // -- declarations ---------------------------------------------------------

    // types
    BOOL, SIGNED, UNSIGNED,

    PARAMS, // int type decls, module and function params (e.g '()')

    /* utils */
    // SUBSCRIPT, (simiilar to bits but [] instead of ()) - future for arrays
    RANGE,

    COMMA, SET, // reserved for enums

} ExprType;

// system-wide expr
typedef struct Expr_TAG Expr;
typedef Expr* Expr_ptr;

// An Expression consists of an AST symbol, which is the expression
// main operator, operands which depend on the type of operator and a
// context, in which the expression has to evaluated.
struct Expr_TAG {

    // AST symb type
    ExprType f_symb;

    union {
        // identifiers
        Atom_ptr f_atom;

        // operators
        struct  {
            Expr_ptr f_lhs;
            Expr_ptr f_rhs; // NULL for unary ops
        };

        // word and numeric constants
        struct {
            size_t f_size;
            value_t f_value;
        };
    } u;

    // accessors
    inline Atom_ptr atom()
    { return u.f_atom; }

    inline size_t size()
    { return u.f_size; }
    inline value_t value()
    { return u.f_value; }

    inline Expr_ptr lhs()
    { return u.f_lhs; }
    inline Expr_ptr rhs()
    { return u.f_rhs; }

    inline Expr_TAG()
        : f_symb(NIL)
    {}

    // identifiers
    inline Expr_TAG(const Atom& atom)
    : f_symb(IDENT)
    { u.f_atom = const_cast<Atom *>(& atom); }

    // word constants
    inline Expr_TAG(ExprType symb, size_t size, value_t value)
        : f_symb(symb)
    {
        assert ((symb == UWCONST) || (symb == SWCONST));

        u.f_size = size;
        u.f_value = value;
    }

    // int constants, are treated as machine size word constants
    inline Expr_TAG(ExprType symb, value_t value)
        : f_symb(symb)
    {
        assert (symb == ICONST);

        u.f_size = sizeof(value_t);
        u.f_value = value;
    }

    // ordinary expr
    inline Expr_TAG(ExprType symb, Expr_TAG* lhs, Expr_TAG* rhs)
        : f_symb(symb)
    {
        u.f_lhs = lhs;
        u.f_rhs = rhs;
    }

}; // Expr_TAG

// system-wide expr
typedef Expr* Expr_ptr;

typedef vector<Expr_ptr> ExprVector;
typedef ExprVector* ExprVector_ptr;

typedef set<Expr_ptr> ExprSet;
typedef ExprSet* ExprSet_ptr;

// for logging purposes
ostream& operator<<(ostream& os, const Expr_ptr t);

class BadWordConstException : public Exception {
public:
    BadWordConstException(const char* msg)
    : f_msg(msg)
    {}

    virtual const char* what() const throw() {
        return f_msg;
    }

    virtual ~BadWordConstException() throw()
    {}

protected:
    const char* f_msg;
};

#endif

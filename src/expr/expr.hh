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

typedef enum {

    // -- linear temporal logic expressions ------------------------------------
    F, G, X, U, R,

    // -- primary expressions --------------------------------------------------

    /* time shift operators (nesting supported) */
    NEXT, PREV,

    /* arithmetical operators */
    NEG, PLUS, SUB, DIV, MUL, MOD,

    /* logical/bitwise operators */
    NOT, AND, OR, XOR, XNOR, IMPLIES, IFF, LSHIFT, RSHIFT,

    /* type operators */
    TYPE, CAST,

    // future
    // LROTATE, RROTATE,

    /* relational operators */
    EQ, NE, GE, GT, LE, LT,

    /* conditionals */
    ITE, COND,

    /* leaves */
    ICONST, // decimal constants
    HCONST, // hex constants
    OCONST, // octal constants

    /* identifiers */
    IDENT, DOT,

    /* declarations */
    BOOL, SIGNED, UNSIGNED,

    /* defines */
    PARAMS, // (), binary

    /* arrays */
    SUBSCRIPT, // [], binary

    // TODO
    SET, // {}, unary

    COMMA,

    // error handling
    ERROR,
} ExprType;

// An Expression consists of an AST symbol, which is the expression
// main operator, operands which depend on the type of operator and a
// context, in which the expression has to evaluated.

/* using STL string as basic atom class */
typedef string Atom;
typedef Atom* Atom_ptr;

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

    inline value_t value()
    {
        assert (ICONST == f_symb ||
                HCONST == f_symb ||
                OCONST == f_symb );
        return u.f_value;
    }

    inline Expr_ptr lhs()
    { return u.f_lhs; }
    inline Expr_ptr rhs()
    { return u.f_rhs; }

    // identifiers
    inline Expr_TAG(const Atom& atom)
    : f_symb(IDENT)
    { u.f_atom = const_cast<Atom *>(& atom); }

    // numeric constants, are treated as machine size consts.
    inline Expr_TAG(ExprType symb, value_t value)
        : f_symb(symb)
    {
        assert (symb == ICONST ||
                symb == HCONST ||
                symb == OCONST );

        u.f_value = value;
    }

    // binary expr (rhs is NULL for unary ops)
    inline Expr_TAG(ExprType symb, Expr_ptr lhs, Expr_ptr rhs)
        : f_symb(symb)
    {
        u.f_lhs = lhs;
        u.f_rhs = rhs;
    }

} Expr;

typedef vector<Expr_ptr> ExprVector;
typedef ExprVector* ExprVector_ptr;

typedef set<Expr_ptr> ExprSet;
typedef ExprSet* ExprSet_ptr;

// TODO: split this into multiple headers

typedef class FQExpr* FQExpr_ptr;
class FQExpr {
public:
    FQExpr(Expr_ptr expr); // default ctx, default time
    FQExpr(Expr_ptr ctx, Expr_ptr expr, step_t time = 0);

    FQExpr(const FQExpr& fqexpr);

    inline Expr_ptr ctx() const
    { return f_ctx; }

    inline Expr_ptr expr() const
    { return f_expr; }

    inline step_t time() const
    { return f_time; }

    inline bool operator==(const FQExpr& other)
    {
        return
            f_ctx  == other.f_ctx  &&
            f_expr == other.f_expr &&
            f_time == other.f_time  ;
    }

private:
    // expression ctx (default for the FSM is 'main')
    Expr_ptr f_ctx;

    // expression body
    Expr_ptr f_expr;

    // expression time (default is 0)
    step_t f_time;
};

/* Normal forms literals */
class PolarizedLiteral {
public:
    PolarizedLiteral(Expr_ptr literal, bool polarity = true);

    inline Expr_ptr literal() const
    { return f_literal; }

    inline bool polarity() const
    { return f_polarity; }

private:
    // literal
    Expr_ptr f_literal;

    // polarity
    bool f_polarity;
};

/* Untimed Canonical Bit Identifiers */
class UCBI {
public:
    UCBI(Expr_ptr ctx, Expr_ptr expr, step_t timeofs, unsigned bitno);
    UCBI(const UCBI& ucbi);

    inline Expr_ptr ctx() const
    { return f_ctx; }

    inline Expr_ptr expr() const
    { return f_expr; }

    inline step_t time() const
    { return f_time; }

    inline unsigned bitno() const
    { return f_bitno; }

private:
    // expression ctx (default is 'main')
    Expr_ptr f_ctx;

    // expression body
    Expr_ptr f_expr;

    // expression time (default is 0)
    step_t f_time;

    // bit number
    unsigned f_bitno;
};

/* Timed Canonical Bit Identifiers */
class TCBI {
public:
    TCBI(Expr_ptr ctx, Expr_ptr expr, step_t timeofs, unsigned bitno, step_t timebase);
    TCBI(const TCBI& tcbi);

    inline Expr_ptr ctx() const
    { return f_ctx; }

    inline Expr_ptr expr() const
    { return f_expr; }

    inline step_t time() const
    { return f_time; }

    inline unsigned bitno() const
    { return f_bitno; }

    inline step_t base() const
    { return f_base; }

private:
    // expression ctx (default is 'main')
    Expr_ptr f_ctx;

    // expression body
    Expr_ptr f_expr;

    // expression time (default is 0)
    step_t f_time;

    // bit number
    unsigned f_bitno;

    // time base (default is 0)
    step_t f_base;
};

ostream& operator<<(ostream& os, const Expr_ptr expr);
ostream& operator<<(ostream& os, const FQExpr& fqexpr);
ostream& operator<<(ostream& os, const UCBI& ucbi);
ostream& operator<<(ostream& os, const TCBI& tcbi);

// TODO: move this!
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

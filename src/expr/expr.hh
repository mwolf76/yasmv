/**
 * @file expr.hh
 * @brief Expression management
 *
 * This header file contains the declarations required by the Expr
 * struct.
 *
 * Copyright (C) 2012-2021 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
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

/** -- shortcurts to simplify the manipulation of the internal expr stack -- */
#define TOP_EXPR(expr)      \
    const auto expr         \
    {                       \
        f_expr_stack.back() \
    }

#define DROP_EXPR() \
    f_expr_stack.pop_back()

#define POP_EXPR(expr) \
    TOP_EXPR(expr);    \
    DROP_EXPR()

#define PUSH_EXPR(expr) \
    f_expr_stack.push_back(expr)

namespace expr {

    typedef enum {

        // -- primary expressions --------------------------------------------------

        /* time shift operators (nesting supported) */
        AT,
        NEXT,

        /* arithmetical operators */
        NEG,
        PLUS,
        SUB,
        DIV,
        MUL,
        MOD, /* not using the more familiar word 'ADD' for addition to prevent confusion with ADDs. */

        /* bitwise operators */
        BW_NOT,
        BW_AND,
        BW_OR,
        BW_XOR,
        BW_XNOR,

        /* logical operators */
        NOT,
        AND,
        OR,
        IMPLIES,

        /* reserved for TRANSes */
        GUARD,

        /* shift operators */
        LSHIFT,
        RSHIFT,

        /* type operators */
        TYPE,
        CAST,

        /* assignment operator */
        ASSIGNMENT,

        /* relational operators */
        EQ,
        NE,
        GE,
        GT,
        LE,
        LT,

        /* conditionals */
        ITE,
        COND,

        /* identifiers */
        QSTRING,
        IDENT,
        DOT,

        /* declarations */
        BOOL,
        SIGNED,
        UNSIGNED,

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

        // -- Time constants
        INSTANT,
        INTERVAL,

        // undefined
        UNDEF,

    } ExprType;

    // An Expression consists of an AST symbol, which is the expression
    // main operator, operands which depend on the type of operator and a
    // context, in which the expression has to evaluated.
    typedef struct Expr_TAG* Expr_ptr;
    typedef struct Expr_TAG {

        // AST symb type
        ExprType f_symb;

        union {
            // identifiers
            Atom_ptr f_atom;

            // numeric constants
            value_t f_value;

            // operators
            struct {
                Expr_ptr f_lhs;
                Expr_ptr f_rhs; // NULL for unary ops
            };
        } u;

        // accessors
        inline ExprType symb() const
        {
            return f_symb;
        }

        Atom& atom() const;
        value_t value() const;

        inline Expr_ptr lhs()
        {
            return u.f_lhs;
        }
        inline Expr_ptr rhs()
        {
            return u.f_rhs;
        }

        // identifiers and strings
        inline Expr_TAG(ExprType symb, const Atom& atom)
        {
            assert(IDENT == symb || QSTRING == symb);
            f_symb = symb;
            u.f_atom = const_cast<Atom*>(&atom);
        }

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
            assert(symb == ICONST ||
                   symb == HCONST ||
                   symb == OCONST ||
                   symb == BCONST ||
                   symb == INSTANT);

            u.f_value = value;
        }

        // nullary nodes (errors, undefined)
        inline Expr_TAG(ExprType symb)
            : f_symb(symb)
        {
            assert(symb == UNDEF);
        }

    } Expr;

    typedef std::vector<Expr_ptr> ExprVector;
    typedef ExprVector* ExprVector_ptr;

    struct LexicographicOrdering {
        int operator()(const Expr_ptr x, const Expr_ptr y) const;
    };

    typedef std::set<Expr_ptr, LexicographicOrdering> ExprSet;
    typedef ExprSet* ExprSet_ptr;

    std::ostream& operator<<(std::ostream& os, const Expr_ptr expr);

    struct ExprHash {
        long operator()(const Expr& k) const;
    };

    struct ExprEq {
        bool operator()(const Expr& x, const Expr& y) const;
    };

    typedef boost::unordered_set<Expr, ExprHash, ExprEq> ExprPool;
    typedef std::pair<ExprPool::iterator, bool> ExprPoolHit;

};     // namespace expr
#endif /* EXPR_H */

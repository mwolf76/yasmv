/**
 *  @file expr_mgr.hh
 *  @brief Expression management. ExprMgr class
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
#ifndef EXPR_MGR_H
#define EXPR_MGR_H

#include <expr.hh>
#include <pool.hh>

typedef class ExprMgr* ExprMgr_ptr;
class ExprMgr  {
public:
    // -- expr makers (mostly inlined) -----------------------------------------

    /* LTL */
    inline Expr_ptr make_F(Expr_ptr expr)
    { return make_expr(F, expr, NULL); }

    inline Expr_ptr make_G(Expr_ptr expr)
    { return make_expr(G, expr, NULL); }

    inline Expr_ptr make_X(Expr_ptr expr)
    { return make_expr(X, expr, NULL); }

    inline Expr_ptr make_U(Expr_ptr lhs, Expr_ptr rhs)
    { return make_expr(U, lhs, rhs); }

    inline Expr_ptr make_R(Expr_ptr lhs, Expr_ptr rhs)
    { return make_expr(R, lhs, rhs); }

    /* CTL (A ops) */
    inline Expr_ptr make_AF(Expr_ptr expr)
    { return make_expr(AF, expr, NULL); }

    inline Expr_ptr make_AG(Expr_ptr expr)
    { return make_expr(AG, expr, NULL); }

    inline Expr_ptr make_AX(Expr_ptr expr)
    { return make_expr(AX, expr, NULL); }

    inline Expr_ptr make_AU(Expr_ptr lhs, Expr_ptr rhs)
    { return make_expr(AU, lhs, rhs); }

    inline Expr_ptr make_AR(Expr_ptr lhs, Expr_ptr rhs)
    { return make_expr(AR, lhs, rhs); }

    /* CTL (E ops) */
    inline Expr_ptr make_EF(Expr_ptr expr)
    { return make_expr(EF, expr, NULL); }

    inline Expr_ptr make_EG(Expr_ptr expr)
    { return make_expr(EG, expr, NULL); }

    inline Expr_ptr make_EX(Expr_ptr expr)
    { return make_expr(EX, expr, NULL); }

    inline Expr_ptr make_EU(Expr_ptr lhs, Expr_ptr rhs)
    { return make_expr(EU, lhs, rhs); }

    inline Expr_ptr make_ER(Expr_ptr lhs, Expr_ptr rhs)
    { return make_expr(ER, lhs, rhs); }

    /* primary expressions */
    inline Expr_ptr make_next(Expr_ptr expr)
    { return make_expr(NEXT, expr, NULL); }

    /* arithmetical operators */
    inline Expr_ptr make_neg(Expr_ptr expr)
    { return make_expr(NEG, expr, NULL); }

    inline Expr_ptr make_add(Expr_ptr a, Expr_ptr b)
    { return make_expr(PLUS, a, b); }

    inline Expr_ptr make_sub(Expr_ptr a, Expr_ptr b)
    { return make_expr(SUB, a, b); }

    inline Expr_ptr make_div(Expr_ptr a, Expr_ptr b)
    { return make_expr(DIV, a, b); }

    inline Expr_ptr make_mul(Expr_ptr a, Expr_ptr b)
    { return make_expr(MUL, a, b); }

    inline Expr_ptr make_mod(Expr_ptr a, Expr_ptr b)
    { return make_expr(MOD, a, b); }

    /* logical/bitwise operators */
    inline Expr_ptr make_not(Expr_ptr expr)
    { return make_expr(NOT, expr, NULL); }

    inline Expr_ptr make_and(Expr_ptr a, Expr_ptr b)
    { return make_expr(AND, a, b); }

    inline Expr_ptr make_or(Expr_ptr a, Expr_ptr b)
    { return make_expr(OR, a, b); }

    inline Expr_ptr make_lshift(Expr_ptr a, Expr_ptr b)
    { return make_expr(LSHIFT, a, b); }

    inline Expr_ptr make_rshift(Expr_ptr a, Expr_ptr b)
    { return make_expr(RSHIFT, a, b); }

    inline Expr_ptr make_xor(Expr_ptr a, Expr_ptr b)
    { return make_expr(XOR, a, b); }

    inline Expr_ptr make_xnor(Expr_ptr a, Expr_ptr b)
    { return make_expr(XNOR, a, b); }

    inline Expr_ptr make_implies(Expr_ptr a, Expr_ptr b)
    { return make_expr(IMPLIES, a, b); }

    inline Expr_ptr make_iff(Expr_ptr a, Expr_ptr b)
    { return make_expr(IFF, a, b); }

    /* relational operators */
    inline Expr_ptr make_eq(Expr_ptr a, Expr_ptr b)
    { return make_expr(EQ, a, b); }

    inline Expr_ptr make_ne(Expr_ptr a, Expr_ptr b)
    { return make_expr(NE, a, b); }

    inline Expr_ptr make_ge(Expr_ptr a, Expr_ptr b)
    { return make_expr(GE, a, b); }

    inline Expr_ptr make_gt(Expr_ptr a, Expr_ptr b)
    { return make_expr(GT, a, b); }

    inline Expr_ptr make_le(Expr_ptr a, Expr_ptr b)
    { return make_expr(LE, a, b); }

    inline Expr_ptr make_lt(Expr_ptr a, Expr_ptr b)
    { return make_expr(LT, a, b); }

    inline Expr_ptr make_cond(Expr_ptr a, Expr_ptr b)
    { return make_expr(COND, a, b); }

    inline Expr_ptr make_ite(Expr_ptr a, Expr_ptr b)
    { return make_expr(ITE, a, b); }

    inline Expr_ptr make_iconst(value_t value)
    {
        Expr tmp(ICONST, value); // we need a temp store
        return __make_expr(&tmp);
    }

    inline Expr_ptr make_hconst(value_t value)
    {
        Expr tmp(HCONST, value); // we need a temp store
        return __make_expr(&tmp);
    }

    inline Expr_ptr make_oconst(value_t value)
    {
        Expr tmp(OCONST, value); // we need a temp store
        return __make_expr(&tmp);
    }

    inline Expr_ptr make_dot(Expr_ptr a, Expr_ptr b)
    { return make_expr(DOT, a, b); }

    inline Expr_ptr make_params(Expr_ptr a, Expr_ptr b)
    { return make_expr(PARAMS, a, b); }

    /* type makers */
    inline Expr_ptr make_boolean_type() const
    { return bool_expr; }

    inline Expr_ptr make_integer_type() const
    { return integer_expr; }

    inline Expr_ptr make_range_type(Expr_ptr a, Expr_ptr b)
    {
        assert(is_numeric(a));
        assert(is_numeric(b));
        return make_expr(RANGE, a, b);
    }

    inline Expr_ptr make_unsigned_type(unsigned bits)
    { return make_params(unsigned_expr, make_iconst((value_t) bits)); }

    inline Expr_ptr make_signed_type(unsigned bits)
    { return make_params(signed_expr, make_iconst((value_t) bits)); }

    Expr_ptr make_enum_type(ExprSet_ptr literals);

    /* builtin identifiers */
    inline Expr_ptr make_main() const
    { return main_expr; }

    inline Expr_ptr make_false()
    { return false_expr; }

    inline Expr_ptr make_true()
    { return true_expr; }

    // Here a bit of magic occurs, so it's better to keep a note:
    // this method is used by the parser to build identifier
    // nodes.  The function is fed with a const char* coming from
    // the Lexer, an Atom object (which in current implementation
    // is in fact a std::string) is built on-the-fly and used to
    // search the atom pool. The atom resulting from the search is
    // always the one stored in the pool. The auto atom object,
    // however gets destroyed as it gets out of scope, so no leak
    // occurs.
    inline Expr_ptr make_identifier(Atom atom)
    {
        AtomPoolHit ah = f_atom_pool.insert(atom);
        const Atom& pooled_atom =  (* ah.first);
#if 0
        if (ah.second) {
            DRIVEL << "Added new atom to pool: '"
                   << pooled_atom << "'" << endl;
        }
#endif
        // no copy occurs here
        return make_expr(pooled_atom);
    }

    inline Expr_ptr make_dec_const(Atom atom)
    { return make_iconst( strtoll(atom.c_str(), NULL, 10)); }

    inline Expr_ptr make_hex_const(Atom atom)
    { return make_hconst( strtoll(atom.c_str(), NULL, 16)); }

    inline Expr_ptr make_oct_const(Atom atom)
    { return make_oconst( strtoll(atom.c_str(), NULL, 8)); }

    // -- is-a predicates -------------------------------------------------------
    inline bool is_identifier(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == IDENT;
    }

    inline bool is_numeric(const Expr_ptr expr) const {
        assert(expr);
        return (expr->f_symb == ICONST)
            || (expr->f_symb == HCONST)
            || (expr->f_symb == OCONST) ;
    }

    // singleton instance accessor
    static inline ExprMgr& INSTANCE() {
        if (! f_instance) {
            f_instance = new ExprMgr();
        }

        return (*f_instance);
    }

protected:
    ExprMgr();
    ~ExprMgr();

private:
    static ExprMgr_ptr f_instance;

    /* mid level services, inlined for performance */
    inline Expr_ptr make_expr(ExprType et, Expr_ptr a, Expr_ptr b)
    {
        Expr tmp(et, a, b); // we need a temp store
        return __make_expr(&tmp);
    }

    inline Expr_ptr make_expr(const Atom& atom)
    {
        Expr tmp(atom); // we need a temp store
        return __make_expr(&tmp);
    }

    // low-level, inlined for performance
    inline Expr_ptr __make_expr(Expr_ptr expr) {
        ExprPoolHit eh = f_expr_pool.insert(*expr);
        Expr_ptr pooled_expr = const_cast<Expr_ptr> (& (*eh.first));
#if 0
        if (eh.second) {
            DRIVEL << "Added new expr to pool: '"
                   << pooled_expr << "'" << endl;
        }
#endif
        return pooled_expr;
    }

    // utils
    value_t pow2(unsigned exp);

    /* -- data ------------------------------------------------------------- */

    // temporal exprs type
    Expr_ptr temporal_expr;

    // boolean exprs type and constants
    Expr_ptr bool_expr;
    Expr_ptr false_expr;
    Expr_ptr true_expr;

    // main module
    Expr_ptr main_expr;

    // base for (un-)signed integer
    Expr_ptr unsigned_expr;
    Expr_ptr signed_expr;
    Expr_ptr integer_expr; // reserved for abstract integer-type

    /* shared pools */
    ExprPool f_expr_pool;
    AtomPool f_atom_pool;
};

#endif

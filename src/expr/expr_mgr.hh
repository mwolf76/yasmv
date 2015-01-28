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

#include <boost/thread/mutex.hpp>

#include <expr/expr.hh>
#include <expr/pool.hh>

#include <opts.hh>

typedef class ExprMgr* ExprMgr_ptr;
class ExprMgr  {
public:

    inline ExprType symb(Expr_ptr expr) const {
        return expr->f_symb;
    }

    /* -- LTL expressions --------------------------------------------------- */
    inline Expr_ptr make_F(Expr_ptr expr)
    { return make_expr(F, expr, NULL); }

    inline bool is_F(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == F;
    }

    inline Expr_ptr make_G(Expr_ptr expr)
    { return make_expr(G, expr, NULL); }

    inline bool is_G(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == G;
    }

    inline Expr_ptr make_X(Expr_ptr expr)
    { return make_expr(X, expr, NULL); }

    inline bool is_X(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == X;
    }

    inline Expr_ptr make_U(Expr_ptr lhs, Expr_ptr rhs)
    { return make_expr(U, lhs, rhs); }

    inline bool is_U(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == U;
    }

    inline Expr_ptr make_R(Expr_ptr lhs, Expr_ptr rhs)
    { return make_expr(R, lhs, rhs); }

    inline bool is_R(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == R;
    }

    inline bool is_LTL(const Expr_ptr expr) const {
        assert(expr);
        return
            expr->f_symb == F ||
            expr->f_symb == G ||
            expr->f_symb == X ||
            expr->f_symb == U ||
            expr->f_symb == R ;
    }

    inline bool is_unary_ltl(const Expr_ptr expr) const {
        assert(expr);
        return
            expr->f_symb == F ||
            expr->f_symb == G ||
            expr->f_symb == X  ;
    }

    inline bool is_binary_ltl(const Expr_ptr expr) const {
        assert(expr);
        return
            expr->f_symb == U ||
            expr->f_symb == R ;
    }

    /* -- Temporal operators ------------------------------------------------ */
    inline Expr_ptr make_next(Expr_ptr expr)
    { return make_expr(NEXT, expr, NULL); }

    inline bool is_next(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == NEXT;
    }

    /* -- Arithmetical operators -------------------------------------------- */
    inline Expr_ptr make_neg(Expr_ptr expr)
    { return make_expr(NEG, expr, NULL); }

    inline bool is_neg(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == NEG;
    }

    inline Expr_ptr make_add(Expr_ptr a, Expr_ptr b)
    { return make_expr(PLUS, a, b); }

    inline bool is_add(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == PLUS;
    }

    inline Expr_ptr make_sub(Expr_ptr a, Expr_ptr b)
    { return make_expr(SUB, a, b); }

    inline bool is_sub(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == SUB;
    }

    inline Expr_ptr make_div(Expr_ptr a, Expr_ptr b)
    { return make_expr(DIV, a, b); }

    inline bool is_div(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == DIV;
    }

    inline Expr_ptr make_mul(Expr_ptr a, Expr_ptr b)
    { return make_expr(MUL, a, b); }

    inline bool is_mul(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == MUL;
    }

    inline Expr_ptr make_mod(Expr_ptr a, Expr_ptr b)
    { return make_expr(MOD, a, b); }

    inline bool is_mod(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == MOD;
    }

    /* -- Logical/Bitwise operators ----------------------------------------- */
    inline Expr_ptr make_not(Expr_ptr expr)
    { return make_expr(NOT, expr, NULL); }

    inline bool is_not(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == NOT;
    }

    inline Expr_ptr make_bw_not(Expr_ptr expr)
    { return make_expr(BW_NOT, expr, NULL); }

    inline bool is_bw_not(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == BW_NOT;
    }

    inline Expr_ptr make_and(Expr_ptr a, Expr_ptr b)
    { return make_expr(AND, a, b); }

    inline bool is_and(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == AND;
    }

    inline Expr_ptr make_bw_and(Expr_ptr a, Expr_ptr b)
    { return make_expr(BW_AND, a, b); }

    inline bool is_bw_and(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == BW_AND;
    }

    inline Expr_ptr make_or(Expr_ptr a, Expr_ptr b)
    { return make_expr(OR, a, b); }

    inline bool is_or(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == OR;
    }

    inline Expr_ptr make_xor(Expr_ptr a, Expr_ptr b)
    { return make_expr(XOR, a, b); }

    inline bool is_xor(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == XOR;
    }

    inline Expr_ptr make_bw_or(Expr_ptr a, Expr_ptr b)
    { return make_expr(BW_OR, a, b); }

    inline bool is_bw_or(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == BW_OR;
    }

    inline Expr_ptr make_lshift(Expr_ptr a, Expr_ptr b)
    { return make_expr(LSHIFT, a, b); }

    inline bool is_lshift(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == LSHIFT;
    }

    inline Expr_ptr make_rshift(Expr_ptr a, Expr_ptr b)
    { return make_expr(RSHIFT, a, b); }

    inline bool is_rshift(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == RSHIFT;
    }

    inline Expr_ptr make_bw_xor(Expr_ptr a, Expr_ptr b)
    { return make_expr(BW_XOR, a, b); }

    inline bool is_bw_xor(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == BW_XOR;
    }

    inline Expr_ptr make_bw_xnor(Expr_ptr a, Expr_ptr b)
    { return make_expr(BW_XNOR, a, b); }

    inline bool is_bw_xnor(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == BW_XNOR;
    }

    inline Expr_ptr make_implies(Expr_ptr a, Expr_ptr b)
    { return make_expr(IMPLIES, a, b); }

    inline bool is_implies(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == IMPLIES;
    }

    inline Expr_ptr make_iff(Expr_ptr a, Expr_ptr b)
    { return make_expr(IFF, a, b); }

    inline bool is_iff(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == IFF;
    }

    /* -- Relational operators ---------------------------------------------- */
    inline Expr_ptr make_eq(Expr_ptr a, Expr_ptr b)
    { return make_expr(EQ, a, b); }

    inline bool is_eq(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == EQ;
    }

    inline Expr_ptr make_ne(Expr_ptr a, Expr_ptr b)
    { return make_expr(NE, a, b); }

    inline bool is_ne(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == NE;
    }

    inline Expr_ptr make_ge(Expr_ptr a, Expr_ptr b)
    { return make_expr(GE, a, b); }

    inline bool is_ge(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == GE;
    }

    inline Expr_ptr make_gt(Expr_ptr a, Expr_ptr b)
    { return make_expr(GT, a, b); }

    inline bool is_gt(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == GT;
    }

    inline Expr_ptr make_le(Expr_ptr a, Expr_ptr b)
    { return make_expr(LE, a, b); }

    inline bool is_le(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == LE;
    }

    inline Expr_ptr make_lt(Expr_ptr a, Expr_ptr b)
    { return make_expr(LT, a, b); }

    inline bool is_lt(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == LT;
    }

    /* -- ITEs -------------------------------------------------------------- */
    inline Expr_ptr make_cond(Expr_ptr a, Expr_ptr b)
    { return make_expr(COND, a, b); }

    inline bool is_cond(const Expr_ptr expr) const {
        assert(expr);
        ExprType symb = expr->f_symb;

        return (COND == symb);
    }

    inline Expr_ptr make_ite(Expr_ptr a, Expr_ptr b)
    { return make_expr(ITE, a, b); }

    inline bool is_ite(const Expr_ptr expr) const {
        assert(expr);
        ExprType symb = expr->f_symb;

        return (ITE == symb);
    }

    /* -- constants --------------------------------------------------------- */
    inline value_t const_value(Expr_ptr expr)
    {
        assert( expr->f_symb == ICONST ||
                expr->f_symb == HCONST ||
                expr->f_symb == OCONST ||
                expr->f_symb == FCONST );
        return expr -> value();
    }

    inline Expr_ptr make_const(value_t value) // decimal
    {
        Expr tmp(ICONST, value); // we need a temp store
        return __make_expr(&tmp);
    }

    inline Expr_ptr make_hconst(value_t value) // hexadecimal
    {
        Expr tmp(HCONST, value); // we need a temp store
        return __make_expr(&tmp);
    }

    inline Expr_ptr make_oconst(value_t value) // octal
    {
        Expr tmp(OCONST, value); // we need a temp store
        return __make_expr(&tmp);
    }

    inline Expr_ptr make_fconst(value_t value)
    {
        Expr tmp(FCONST, value); // we need a temp store
        return __make_expr(&tmp);
    }

    /* canonical by construction */
    inline Expr_ptr make_dot(Expr_ptr a, Expr_ptr b)
    { return left_associate_dot( make_expr(DOT, a, b)); }

    inline Expr_ptr make_comma(Expr_ptr a, Expr_ptr b)
    { return make_expr(COMMA, a, b); }

    inline Expr_ptr make_subscript(Expr_ptr a, Expr_ptr b)
    { return make_expr(SUBSCRIPT, a, b); }

    inline Expr_ptr make_params(Expr_ptr a, Expr_ptr b)
    { return make_expr(PARAMS, a, b); }

    inline Expr_ptr make_set(Expr_ptr a)
    { return make_expr(SET, a, NULL); }

    /* -- Types & Casts ----------------------------------------------------- */
    inline Expr_ptr make_type(Expr_ptr a, Expr_ptr b)
    { return make_expr(TYPE, a, b); }
    inline Expr_ptr make_type(Expr_ptr a, Expr_ptr b, Expr_ptr c)
    { return make_expr(TYPE, a, make_expr(COMMA, b, c)); }

    inline bool is_type(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == TYPE;
    }

    inline Expr_ptr make_cast(Expr_ptr a, Expr_ptr b)
    { return make_expr(CAST, a, b); }

    inline bool is_cast(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == CAST;
    }

    inline Expr_ptr make_const_int_type(unsigned digits)
    {
        return make_type(const_int_expr,
                         make_const((value_t) digits));
    }

    inline bool is_const_int_type(const Expr_ptr expr) const {
        assert(expr);
        return expr == const_int_expr;
    }

    inline Expr_ptr make_const_fxd_type(unsigned width)
    {
        return make_type(const_fxd_expr,
                         make_const((value_t) width));

    }

    inline bool is_const_fxd_type(const Expr_ptr expr) const {
        assert(expr);
        return expr == const_fxd_expr;
    }


    inline Expr_ptr make_fixed_type(unsigned digits)
    {
        return make_type(const_int_expr,
                         make_const((value_t) digits));
    }

    inline bool is_fixed_type(const Expr_ptr expr) const {
        assert(expr);
        return expr == const_int_expr;
    }

    inline Expr_ptr make_unsigned_int_type(unsigned digits)
    {
        return make_type(unsigned_int_expr,
                         make_const((value_t) digits));
    }

    inline Expr_ptr make_unsigned_fxd_type(unsigned width)
    {
        return make_type(unsigned_fxd_expr,
                         make_const((value_t) width));
    }

    inline Expr_ptr make_signed_int_type(unsigned digits)
    {
        return make_type(signed_int_expr,
                         make_const((value_t) digits));
    }

    inline Expr_ptr make_signed_fxd_type(unsigned width)
    {
        return make_type(signed_fxd_expr,
                         make_const((value_t) width));
    }

    inline Expr_ptr make_abstract_array_type(Expr_ptr of)
    { return make_type( array_expr, of); }


    Expr_ptr make_enum_type(ExprSet& literals);

    /* -- Builtin types ----------------------------------------------------- */
    inline Expr_ptr make_boolean_type() const
    { return bool_expr; }

    inline bool is_boolean_type(const Expr_ptr expr) const {
        assert(expr);
        return expr == bool_expr;
    }

    /* -- Builtin identifiers and constants --------------------------------- */


    inline Expr_ptr make_temp() const
    { return temp_expr; }

    inline bool is_temp(const Expr_ptr expr) const {
        assert(expr);
        return expr == temp_expr;
    }

    inline Expr_ptr make_main() const
    { return main_expr; }

    inline bool is_main(const Expr_ptr expr) const {
        assert(expr);
        return expr == main_expr;
    }

    inline Expr_ptr make_empty() const
    { return empty_expr; }

    inline bool is_empty(const Expr_ptr expr) const {
        assert(expr);
        return expr == empty_expr;
    }

    inline Expr_ptr make_false() const
    { return false_expr; }

    inline bool is_false(const Expr_ptr expr) const {
        assert(expr);
        return expr == false_expr;
    }

    inline Expr_ptr make_true() const
    { return true_expr; }

    inline bool is_true(const Expr_ptr expr) const {
        assert(expr);
        return expr == true_expr;
    }

    inline Expr_ptr make_zero()
    {
        Expr tmp(ICONST, 0); // we need a temp store
        return __make_expr(&tmp);
    }

    inline bool is_zero(const Expr_ptr expr) const {
        assert(expr);
        return is_constant(expr) && (0 == expr->u.f_value);
    }

    inline Expr_ptr make_one()
    {
        Expr tmp(ICONST, 1); // we need a temp store
        return __make_expr(&tmp);
    }

    inline bool is_one(const Expr_ptr expr) const {
        assert(expr);
        return is_constant(expr) && (1 == expr->u.f_value);
    }

    inline Expr_ptr make_dec_const(Atom atom)
    { return make_const( strtoll(atom.c_str(), NULL, 10)); }

    inline Expr_ptr make_hex_const(Atom atom)
    { return make_hconst( strtoll(atom.c_str(), NULL, 0x10)); }

    inline Expr_ptr make_oct_const(Atom atom)
    { return make_oconst( strtoll(atom.c_str(), NULL, 010)); }

    inline Expr_ptr make_fxd_const(Atom integer, Atom precision)
    {
        value_t int_
            (strtoll(integer.c_str(), NULL, 10));
        value_t fract_
            (decimal_lookup(precision.c_str()));
        value_t value
            ((int_ << OptsMgr::INSTANCE().precision()) + fract_);
        return make_fconst( value );
    }

    inline Expr_ptr make_undef()
    {
        Expr tmp(UNDEF); // we need a temp store
        return __make_expr(&tmp);
    }

    inline bool is_undef(const Expr_ptr expr) const {
        assert(expr);
        ExprType symb = expr->f_symb;

        return (UNDEF == symb);
    }

    // -- broad is-a predicates ------------------------------------------------
    inline bool is_temporal(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == NEXT;
    }

    inline bool is_identifier(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == IDENT;
    }

    inline bool is_unsigned_int(const Expr_ptr expr) const {
        assert(expr);
        return expr == unsigned_int_expr;
    }

    inline bool is_signed_int(const Expr_ptr expr) const {
        assert(expr);
        return expr == signed_int_expr;
    }

    inline bool is_bool_const(const Expr_ptr expr) const {
        assert(expr);
        return is_false(expr) || is_true(expr) ;
    }

    inline bool is_constant(const Expr_ptr expr) const {
        assert(expr);
        return
            expr -> f_symb == ICONST ||
            expr -> f_symb == OCONST ||
            expr -> f_symb == HCONST  ;
    }

    inline bool is_params(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == PARAMS;
    }

    inline bool is_subscript(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == SUBSCRIPT;
    }

    inline bool is_dot(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == DOT;
    }

    inline bool is_comma(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == COMMA;
    }

    inline bool is_set(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == SET;
    }

    inline bool is_int_numeric(const Expr_ptr expr) const {
        assert(expr);
        return (expr->f_symb == ICONST)
            || (expr->f_symb == HCONST)
            || (expr->f_symb == OCONST) ;
    }

    inline bool is_fxd_numeric(const Expr_ptr expr) const {
        assert(expr);
        return (expr->f_symb == FCONST);
    }

    // expr inspectors, used by compiler as helpers to determine operands type
    inline bool is_unary_logical(const Expr_ptr expr) const {
        assert(expr);
        ExprType symb = expr->f_symb;
        return (NOT == symb);
    }
    inline bool is_binary_logical(const Expr_ptr expr) const {
        assert(expr);
        ExprType symb = expr->f_symb;

        return ((AND == symb)  ||
                (OR  == symb)  ||
                (XOR == symb)  ||
                (IFF == symb)  ||
                (EQ  == symb)  ||
                (NE  == symb)  ||
                (IMPLIES == symb));
    }

    inline bool is_unary_arithmetical(const Expr_ptr expr) const {
        assert(expr);
        ExprType symb = expr->f_symb;

        return ((NEG == symb) ||
                 (BW_NOT == symb));
    }

    inline bool is_binary_arithmetical(const Expr_ptr expr) const {
        assert(expr);
        ExprType symb = expr->f_symb;

        return ((PLUS == symb)   ||
                (SUB == symb)    ||
                (DIV == symb)    ||
                (MUL == symb)    ||
                (MOD == symb)    ||

                (BW_AND == symb) ||
                (BW_OR  == symb) ||
                (BW_XOR == symb) ||
                (BW_XNOR == symb)||

                (RSHIFT == symb) ||
                (LSHIFT == symb));
    }

    inline bool is_binary_enumerative(const Expr_ptr expr) const {
        assert(expr);
        ExprType symb = expr->f_symb;

        return ((EQ == symb) ||
                (NE == symb));
    }

    inline bool is_binary_relational(const Expr_ptr expr) const {
        assert(expr);
        ExprType symb = expr->f_symb;

        return ((EQ == symb) ||
                (NE == symb) ||
                (LT == symb) ||
                (LE == symb) ||
                (GT == symb) ||
                (GE == symb));
    }

    // singleton instance accessor
    static inline ExprMgr& INSTANCE() {
        if (! f_instance) {
            f_instance = new ExprMgr();
        }

        return (*f_instance);
    }

    Expr_ptr make_identifier(Atom atom);

protected:
    ExprMgr();
    ~ExprMgr();

private:
    static ExprMgr_ptr f_instance;

    /* mid level services */
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

    /* synchronized low-level service */
    Expr_ptr __make_expr(Expr_ptr expr);

    /* aux service of make_dot */
    Expr_ptr left_associate_dot(const Expr_ptr);

    value_t decimal_lookup(const char *decimal_repr);

    /* -- data ------------------------------------------------------------- */

    /* boolean exprs type and constants */
    Expr_ptr bool_expr;
    Expr_ptr false_expr;
    Expr_ptr true_expr;

    /* integers */
    Expr_ptr const_int_expr;
    Expr_ptr unsigned_int_expr;
    Expr_ptr signed_int_expr;

    /* fixed */
    Expr_ptr const_fxd_expr;
    Expr_ptr unsigned_fxd_expr;
    Expr_ptr signed_fxd_expr;

    /* reserved for abstract array types */
    Expr_ptr array_expr;

    /* reserved for temp symbols ctx */
    Expr_ptr temp_expr;

    /* main module */
    Expr_ptr main_expr;

    /* empty symbol */
    Expr_ptr empty_expr;

    /* synchronized shared pools */
    boost::mutex f_expr_mutex;
    ExprPool f_expr_pool;

    boost::mutex f_atom_mutex;
    AtomPool f_atom_pool;
};

// TODO: split this into multiple headers

#endif

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

typedef unordered_map<ExprType, string> exprTypeToStringMap;
typedef unordered_map<string, ExprType> exprTypeFromStringMap;

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
                expr->f_symb == OCONST );
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

    inline Expr_ptr make_dot(Expr_ptr a, Expr_ptr b)
    { return make_expr(DOT, a, b); }

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

    inline Expr_ptr make_unsigned_int_type(unsigned digits)
    {
        return make_type(unsigned_int_expr,
                         make_const((value_t) digits));
    }

    inline Expr_ptr make_unsigned_fxd_type(unsigned magnitude, unsigned fractional)
    {
        return make_type(unsigned_fxd_expr,
                         make_const((value_t) magnitude),
                         make_const((value_t) fractional));
    }

    inline Expr_ptr make_signed_int_type(unsigned digits)
    {
        return make_type(signed_int_expr,
                         make_const((value_t) digits));
    }

    inline Expr_ptr make_signed_fxd_type(unsigned magnitude, unsigned fractional)
    {
        return make_type(signed_fxd_expr,
                         make_const((value_t) magnitude),
                         make_const((value_t) fractional));
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

    inline Expr_ptr make_constant_type() const
    { return const_int_expr; }

    inline bool is_constant_type(const Expr_ptr expr) const {
        assert(expr);
        return expr == const_int_expr;
    }

    /* -- Builtin identifiers and constants --------------------------------- */
    inline Expr_ptr make_temp() const
    { return temp_expr; }

    inline bool is_temp(const Expr_ptr expr) const {
        assert(expr);
        return expr == temp_expr;
    }

    inline Expr_ptr make_default_ctx() const
    { return default_ctx_expr; }

    inline bool is_default_ctx(const Expr_ptr expr) const {
        assert(expr);
        return expr == default_ctx_expr;
    }

    inline Expr_ptr make_main() const
    { return main_expr; }

    inline bool is_main(const Expr_ptr expr) const {
        assert(expr);
        return expr == main_expr;
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
    { return make_const( strtoll(atom.c_str(), NULL, 10)); }

    inline Expr_ptr make_hex_const(Atom atom)
    { return make_hconst( strtoll(atom.c_str(), NULL, 0x10)); }

    inline Expr_ptr make_oct_const(Atom atom)
    { return make_oconst( strtoll(atom.c_str(), NULL, 010)); }

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

    inline bool is_numeric(const Expr_ptr expr) const {
        assert(expr);
        return (expr->f_symb == ICONST)
            || (expr->f_symb == HCONST)
            || (expr->f_symb == OCONST) ;
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
                (IFF == symb)  ||
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

    ExprType exprTypeFromString (string exprTypeString );
    string exprTypeToString(ExprType exprType);

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
    Expr_ptr unsigned_fxd_expr;
    Expr_ptr signed_fxd_expr;

    /* reserved for abstract array types */
    Expr_ptr array_expr;

    /* reserved for temp symbols ctx */
    Expr_ptr temp_expr;

    /* main module */
    Expr_ptr main_expr;

    /* toplevel default ctx (for command line exprs) */
    Expr_ptr default_ctx_expr;

    /* shared pools */
    ExprPool f_expr_pool;
    AtomPool f_atom_pool;

    exprTypeFromStringMap f_s2e;
};

#endif

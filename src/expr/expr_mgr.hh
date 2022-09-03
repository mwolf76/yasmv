/**
 * @file expr_mgr.hh
 * @brief Expression management. ExprMgr class
 *
 * This header file contains the declarations required by the
 * Expression Manager class.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA
 *
 **/

#ifndef EXPR_MGR_H
#define EXPR_MGR_H

#include <boost/thread/mutex.hpp>

#include <expr/expr.hh>

#include <opts/opts_mgr.hh>

namespace expr {

    typedef class ExprMgr* ExprMgr_ptr;
    class ExprMgr {
    public:
        inline ExprType symb(Expr_ptr expr) const
        {
            return expr->f_symb;
        }

        /* -- LTL expressions -------------------------------------------------- */
        inline Expr_ptr make_F(Expr_ptr expr)
        {
            return make_expr(F, expr, NULL);
        }

        inline bool is_F(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == F;
        }

        inline Expr_ptr make_G(Expr_ptr expr)
        {
            return make_expr(G, expr, NULL);
        }

        inline bool is_G(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == G;
        }

        inline Expr_ptr make_X(Expr_ptr expr)
        {
            return make_expr(X, expr, NULL);
        }

        inline bool is_X(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == X;
        }

        inline Expr_ptr make_U(Expr_ptr lhs, Expr_ptr rhs)
        {
            return make_expr(U, lhs, rhs);
        }

        inline bool is_U(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == U;
        }

        inline Expr_ptr make_R(Expr_ptr lhs, Expr_ptr rhs)
        {
            return make_expr(R, lhs, rhs);
        }

        inline bool is_R(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == R;
        }

        inline bool is_LTL(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == F ||
                   expr->f_symb == G ||
                   expr->f_symb == X ||
                   expr->f_symb == U ||
                   expr->f_symb == R;
        }

        inline bool is_unary_ltl(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == F ||
                   expr->f_symb == G ||
                   expr->f_symb == X;
        }

        inline bool is_binary_ltl(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == U ||
                   expr->f_symb == R;
        }

        /* -- Temporal operators ---------------------------------------------- */
        inline Expr_ptr make_at(Expr_ptr time, Expr_ptr expr)
        {
            assert(is_instant(time) || is_interval(time));
            return make_expr(AT, time, expr);
        }

        inline bool is_at(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == AT;
        }

        inline Expr_ptr make_next(Expr_ptr expr)
        {
            return make_expr(NEXT, expr, NULL);
        }

        inline bool is_next(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == NEXT;
        }

        /* -- Arithmetical operators ------------------------------------------- */
        inline Expr_ptr make_neg(Expr_ptr expr)
        {
            return make_expr(NEG, expr, NULL);
        }

        inline bool is_neg(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == NEG;
        }

        inline Expr_ptr make_add(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(PLUS, a, b);
        }

        inline bool is_add(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == PLUS;
        }

        inline Expr_ptr make_sub(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(SUB, a, b);
        }

        inline bool is_sub(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == SUB;
        }

        inline Expr_ptr make_div(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(DIV, a, b);
        }

        inline bool is_div(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == DIV;
        }

        inline Expr_ptr make_mul(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(MUL, a, b);
        }

        inline bool is_mul(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == MUL;
        }

        inline Expr_ptr make_mod(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(MOD, a, b);
        }

        inline bool is_mod(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == MOD;
        }

        /* -- Logical/Bitwise operators ---------------------------------------- */
        inline Expr_ptr make_not(Expr_ptr expr)
        {
            return make_expr(NOT, expr, NULL);
        }

        inline bool is_not(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == NOT;
        }

        inline Expr_ptr make_bw_not(Expr_ptr expr)
        {
            return make_expr(BW_NOT, expr, NULL);
        }

        inline bool is_bw_not(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == BW_NOT;
        }

        inline Expr_ptr make_and(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(AND, a, b);
        }

        inline bool is_and(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == AND;
        }

        inline Expr_ptr make_bw_and(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(BW_AND, a, b);
        }

        inline bool is_bw_and(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == BW_AND;
        }

        inline Expr_ptr make_or(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(OR, a, b);
        }

        inline bool is_or(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == OR;
        }

        inline Expr_ptr make_bw_or(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(BW_OR, a, b);
        }

        inline bool is_bw_or(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == BW_OR;
        }

        inline Expr_ptr make_lshift(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(LSHIFT, a, b);
        }

        inline bool is_lshift(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == LSHIFT;
        }

        inline Expr_ptr make_rshift(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(RSHIFT, a, b);
        }

        inline bool is_rshift(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == RSHIFT;
        }

        inline Expr_ptr make_bw_xor(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(BW_XOR, a, b);
        }

        inline bool is_bw_xor(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == BW_XOR;
        }

        inline Expr_ptr make_bw_xnor(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(BW_XNOR, a, b);
        }

        inline bool is_bw_xnor(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == BW_XNOR;
        }

        inline Expr_ptr make_guard(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(GUARD, a, b);
        }

        inline bool is_guard(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == GUARD;
        }

        inline Expr_ptr make_implies(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(IMPLIES, a, b);
        }

        inline bool is_implies(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == IMPLIES;
        }

        /* -- Assignment operator ---------------------------------------------- */
        inline Expr_ptr make_assignment(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(ASSIGNMENT, a, b);
        }

        inline bool is_assignment(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == ASSIGNMENT;
        }

        /* -- Relational operators --------------------------------------------- */
        inline Expr_ptr make_eq(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(EQ, a, b);
        }

        inline bool is_eq(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == EQ;
        }

        inline Expr_ptr make_ne(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(NE, a, b);
        }

        inline bool is_ne(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == NE;
        }

        inline Expr_ptr make_ge(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(GE, a, b);
        }

        inline bool is_ge(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == GE;
        }

        inline Expr_ptr make_gt(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(GT, a, b);
        }

        inline bool is_gt(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == GT;
        }

        inline Expr_ptr make_le(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(LE, a, b);
        }

        inline bool is_le(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == LE;
        }

        inline Expr_ptr make_lt(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(LT, a, b);
        }

        inline bool is_lt(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == LT;
        }

        /* -- ITEs ------------------------------------------------------------- */
        inline Expr_ptr make_cond(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(COND, a, b);
        }

        inline bool is_cond(const Expr_ptr expr) const
        {
            assert(expr);
            ExprType symb = expr->f_symb;

            return (COND == symb);
        }

        inline Expr_ptr make_ite(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(ITE, a, b);
        }

        inline bool is_ite(const Expr_ptr expr) const
        {
            assert(expr);
            ExprType symb = expr->f_symb;

            return (ITE == symb);
        }

        /* -- constants -------------------------------------------------------- */
        inline value_t const_value(Expr_ptr expr)
        {
            return expr->value();
        }

        inline Expr_ptr make_const(value_t value) // decimal
        {
            Expr tmp(ICONST, value); // we need a temp store
            return __make_expr(&tmp);
        }

        inline Expr_ptr make_instant(value_t value)
        {
            Expr tmp(INSTANT, value); // we need a temp store
            return __make_expr(&tmp);
        }

        inline Expr_ptr make_interval(Expr_ptr begin, Expr_ptr end)
        {
            return make_expr(INTERVAL, begin, end);
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

        inline Expr_ptr make_bconst(value_t value) // octal
        {
            Expr tmp(BCONST, value); // we need a temp store
            return __make_expr(&tmp);
        }

        /* canonical by construction */
        inline Expr_ptr make_dot(Expr_ptr a, Expr_ptr b)
        {
            return left_associate_dot(make_expr(DOT, a, b));
        }

        inline Expr_ptr make_subscript(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(SUBSCRIPT, a, b);
        }

        inline Expr_ptr make_array(Expr_ptr a)
        {
            return make_expr(ARRAY, a, NULL);
        }

        inline Expr_ptr make_array_comma(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(ARRAY_COMMA, a, b);
        }

        inline Expr_ptr make_params(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(PARAMS, a, b);
        }

        inline Expr_ptr make_params_comma(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(PARAMS_COMMA, a, b);
        }

        inline Expr_ptr make_set(Expr_ptr a)
        {
            return make_expr(SET, a, NULL);
        }

        inline Expr_ptr make_set_comma(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(SET_COMMA, a, b);
        }

        /* -- Types & Casts ---------------------------------------------------- */
        inline Expr_ptr make_type(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(TYPE, a, b);
        }
        inline Expr_ptr make_type(Expr_ptr a, Expr_ptr b, Expr_ptr c)
        {
            return make_expr(TYPE, a, make_expr(DOT, b, c));
        }

        inline bool is_type(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == TYPE;
        }

        inline Expr_ptr make_cast(Expr_ptr a, Expr_ptr b)
        {
            return make_expr(CAST, a, b);
        }

        inline bool is_cast(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == CAST;
        }

        inline Expr_ptr make_const_int_type(unsigned digits)
        {
            return make_type(const_int_expr,
                             make_const((value_t) digits));
        }

        inline bool is_const_int_type(const Expr_ptr expr) const
        {
            assert(expr);
            return expr == const_int_expr;
        }

        inline Expr_ptr make_unsigned_int_type(unsigned digits)
        {
            return make_type(unsigned_int_expr,
                             make_const((value_t) digits));
        }

        inline Expr_ptr make_signed_int_type(unsigned digits)
        {
            return make_type(signed_int_expr,
                             make_const((value_t) digits));
        }

        inline Expr_ptr make_array_type(Expr_ptr of, unsigned width)
        {
            return make_type(array_expr, of,
                             make_const((value_t) width));
        }


        Expr_ptr make_enum_type(ExprSet& literals);

        /* -- Builtin types ---------------------------------------------------- */
        inline Expr_ptr make_time_type() const
        {
            return time_expr;
        }

        inline Expr_ptr make_boolean_type() const
        {
            return bool_expr;
        }

        inline bool is_boolean_type(const Expr_ptr expr) const
        {
            assert(expr);
            return expr == bool_expr;
        }

        inline Expr_ptr make_string_type() const
        {
            return string_expr;
        }

        inline bool is_string_type(const Expr_ptr expr) const
        {
            assert(expr);
            return expr == string_expr;
        }

        /* -- Builtin identifiers, constants and qstrings ---------------------- */
        inline Expr_ptr make_temp() const
        {
            return temp_expr;
        }

        inline bool is_temp(const Expr_ptr expr) const
        {
            assert(expr);
            return expr == temp_expr;
        }

        inline Expr_ptr make_empty() const
        {
            return empty_expr;
        }

        inline bool is_empty(const Expr_ptr expr) const
        {
            assert(expr);
            return expr == empty_expr;
        }

        inline Expr_ptr make_false() const
        {
            return false_expr;
        }

        inline bool is_false(const Expr_ptr expr) const
        {
            assert(expr);
            return expr == false_expr;
        }

        inline Expr_ptr make_true() const
        {
            return true_expr;
        }

        inline bool is_true(const Expr_ptr expr) const
        {
            assert(expr);
            return expr == true_expr;
        }

        inline Expr_ptr make_zero()
        {
            Expr tmp(ICONST, 0); // we need a temp store
            return __make_expr(&tmp);
        }

        inline bool is_zero(const Expr_ptr expr) const
        {
            assert(expr);
            return is_constant(expr) && (0 == expr->u.f_value);
        }

        inline Expr_ptr make_one()
        {
            Expr tmp(ICONST, 1); // we need a temp store
            return __make_expr(&tmp);
        }

        inline bool is_one(const Expr_ptr expr) const
        {
            assert(expr);
            return is_constant(expr) && (1 == expr->u.f_value);
        }

        inline Expr_ptr make_dec_const(Atom atom)
        {
            return make_const(strtoll(atom.c_str(), NULL, 10));
        }

        inline Expr_ptr make_hex_const(Atom atom)
        {
            const char* p(atom.c_str() + 2);

            return make_hconst(strtoll(p, NULL, 0x10));
        }

        inline Expr_ptr make_oct_const(Atom atom)
        {
            const char* p(atom.c_str() + 1);

            return make_oconst(strtoll(p, NULL, 010));
        }

        inline Expr_ptr make_bin_const(Atom atom)
        {
            const char* p(atom.c_str() + 2);

            return make_bconst(strtoll(p, NULL, 2));
        }

        inline Expr_ptr make_undef()
        {
            Expr tmp(UNDEF); // we need a temp store
            return __make_expr(&tmp);
        }

        inline bool is_undef(const Expr_ptr expr) const
        {
            assert(expr);
            ExprType symb = expr->f_symb;

            return (UNDEF == symb);
        }

        inline bool is_identifier(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == IDENT;
        }

        Expr_ptr make_identifier(Atom atom);

        inline bool is_qstring(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == QSTRING;
        }

        Expr_ptr make_qstring(Atom atom);

        const Atom& internalize(Atom atom);

        /* -- broad is-a predicates -------------------------------------------- */
        inline bool is_temporal(const Expr_ptr expr) const
        {
            assert(expr);
            return is_next(expr) || is_at(expr);
        }

        inline bool is_lvalue(const Expr_ptr expr) const
        {
            return is_identifier(expr) ||
                   is_subscript(expr);
        }

        inline bool is_subscript(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == SUBSCRIPT;
        }

        inline bool is_unsigned_int(const Expr_ptr expr) const
        {
            assert(expr);
            return expr == unsigned_int_expr;
        }

        inline bool is_signed_int(const Expr_ptr expr) const
        {
            assert(expr);
            return expr == signed_int_expr;
        }

        inline bool is_bool_const(const Expr_ptr expr) const
        {
            assert(expr);
            return is_false(expr) || is_true(expr);
        }

        inline bool is_constant(const Expr_ptr expr) const
        {
            return is_bool_const(expr) ||
                   is_int_const(expr);
        }

        inline bool is_instant(const Expr_ptr expr) const
        {
            assert(expr);
            return (expr->f_symb == INSTANT);
        }

        inline bool is_interval(const Expr_ptr expr) const
        {
            assert(expr);
            return (expr->f_symb == INTERVAL);
        }

        inline bool is_params(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == PARAMS;
        }
        inline bool is_params_comma(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == PARAMS_COMMA;
        }

        inline bool is_dot(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == DOT;
        }

        inline bool is_array(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == ARRAY;
        }

        inline bool is_array_comma(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == ARRAY_COMMA;
        }

        ExprVector array_literals(const Expr_ptr expr) const;

        inline bool is_set(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == SET;
        }

        inline bool is_set_comma(const Expr_ptr expr) const
        {
            assert(expr);
            return expr->f_symb == SET_COMMA;
        }

        inline bool is_int_const(const Expr_ptr expr) const
        {
            assert(expr);
            return (expr->f_symb == ICONST) ||
                   (expr->f_symb == BCONST) ||
                   (expr->f_symb == HCONST) ||
                   (expr->f_symb == OCONST);
        }

        /* -- expr inspectors -------------------------------------------------- */
        inline bool is_unary_logical(const Expr_ptr expr) const
        {
            assert(expr);
            ExprType symb = expr->f_symb;
            return (NOT == symb);
        }
        inline bool is_binary_logical(const Expr_ptr expr) const
        {
            assert(expr);
            ExprType symb = expr->f_symb;

            return ((AND == symb) ||
                    (OR == symb) ||
                    (EQ == symb) ||
                    (NE == symb) ||
                    (IMPLIES == symb) ||
                    (GUARD == symb));
        }

        inline bool is_unary_arithmetical(const Expr_ptr expr) const
        {
            assert(expr);
            ExprType symb = expr->f_symb;

            return ((NEG == symb) ||
                    (BW_NOT == symb));
        }

        inline bool is_binary_arithmetical(const Expr_ptr expr) const
        {
            assert(expr);
            ExprType symb = expr->f_symb;

            return ((PLUS == symb) ||
                    (SUB == symb) ||
                    (DIV == symb) ||
                    (MUL == symb) ||
                    (MOD == symb) ||

                    (BW_AND == symb) ||
                    (BW_OR == symb) ||
                    (BW_XOR == symb) ||
                    (BW_XNOR == symb) ||

                    (RSHIFT == symb) ||
                    (LSHIFT == symb));
        }

        inline bool is_binary_enumerative(const Expr_ptr expr) const
        {
            assert(expr);
            ExprType symb = expr->f_symb;

            return ((EQ == symb) ||
                    (NE == symb));
        }

        inline bool is_binary_equality(const Expr_ptr expr) const
        {
            assert(expr);
            ExprType symb = expr->f_symb;

            return ((EQ == symb) ||
                    (NE == symb));
        }

        inline bool is_binary_relational(const Expr_ptr expr) const
        {
            assert(expr);
            ExprType symb = expr->f_symb;

            return ((EQ == symb) ||
                    (NE == symb) ||
                    (LT == symb) ||
                    (LE == symb) ||
                    (GT == symb) ||
                    (GE == symb));
        }

        static inline ExprMgr& INSTANCE()
        {
            if (!f_instance) {
                f_instance = new ExprMgr();
            }

            return (*f_instance);
        }

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

        /* identifiers & strings */
        inline Expr_ptr make_expr(ExprType et, const Atom& atom)
        {
            Expr tmp(et, atom); // we need a temp store
            return __make_expr(&tmp);
        }

        /* synchronized low-level service */
        Expr_ptr __make_expr(Expr_ptr expr);

        /* aux service of make_dot */
        Expr_ptr left_associate_dot(const Expr_ptr);

        value_t decimal_lookup(const char* decimal_repr);

        /* -- data ------------------------------------------------------------- */
        Expr_ptr time_expr;
        Expr_ptr bool_expr;
        Expr_ptr string_expr;
        Expr_ptr false_expr;
        Expr_ptr true_expr;

        /* integers */
        Expr_ptr const_int_expr;
        Expr_ptr unsigned_int_expr;
        Expr_ptr signed_int_expr;

        /* reserved for abstract array types */
        Expr_ptr array_expr;

        /* reserved for temp symbols ctx */
        Expr_ptr temp_expr;

        /* empty symbol */
        Expr_ptr empty_expr;

        /* synchronized shared pools */
        boost::mutex f_expr_mutex;
        ExprPool f_expr_pool;

        boost::mutex f_atom_mutex;
        AtomPool f_atom_pool;
    };

}; // namespace expr

#endif /* EXPR_MGR_H */

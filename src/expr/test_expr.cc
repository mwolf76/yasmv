/**
 * @file test_expr.cc
 * @brief Expressions subsystem unit tests.
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

#define BOOST_TEST_DYN_LINK
#include <boost/test/unit_test.hpp>

#include <expr.hh>
#include <expr_mgr.hh>
#include <printer.hh>

BOOST_AUTO_TEST_SUITE(tests)
BOOST_AUTO_TEST_CASE(expr)
{
    ExprMgr& em(ExprMgr::INSTANCE());

    Atom a_x("x");
    Atom a_y("y");

    Expr_ptr x = em.make_identifier(a_x);
    BOOST_CHECK( x == em.make_identifier(a_x));

    Expr_ptr y = em.make_identifier(a_y);
    BOOST_CHECK( y == em.make_identifier(a_y));

    // LTL makers and is-a predicates
    Expr_ptr Fx = em.make_F(x);
    BOOST_CHECK (Fx->f_symb == F && Fx->lhs() == x && Fx->rhs() == NULL);
    BOOST_CHECK (em.is_F(Fx));
    BOOST_CHECK (em.is_LTL(Fx));


    Expr_ptr Gx = em.make_G(x);
    BOOST_CHECK (Gx->f_symb == G && Gx->lhs() == x && Gx->rhs() == NULL);
    BOOST_CHECK (em.is_G(Gx));
    BOOST_CHECK (em.is_LTL(Gx));

    Expr_ptr Xx = em.make_X(x);
    BOOST_CHECK (Xx->f_symb == X && Xx->lhs() == x && Xx->rhs() == NULL);
    BOOST_CHECK (em.is_X(Xx));
    BOOST_CHECK (em.is_LTL(Xx));

    Expr_ptr xUy = em.make_U(x, y);
    BOOST_CHECK (xUy->f_symb == U && xUy->lhs() == x && xUy->rhs() == y);
    BOOST_CHECK (em.is_U(xUy));
    BOOST_CHECK (em.is_LTL(xUy));

    Expr_ptr xRy = em.make_R(x, y);
    BOOST_CHECK (xRy->f_symb == R && xRy->lhs() == x && xRy->rhs() == y);
    BOOST_CHECK (em.is_R(xRy));
    BOOST_CHECK (em.is_LTL(xRy));

    BOOST_CHECK (em.make_F(x) == Fx);
    BOOST_CHECK (em.make_G(x) == Gx);
    BOOST_CHECK (em.make_X(x) == Xx);
    BOOST_CHECK (em.make_U(x, y) == xUy);
    BOOST_CHECK (em.make_R(x, y) == xRy);

    // primary makers and is-a predicates
    Expr_ptr next_x = em.make_next(x);
    BOOST_CHECK (next_x->f_symb == NEXT && next_x->lhs() == x && next_x->rhs() == NULL);
    BOOST_CHECK (em.is_next(next_x));
    BOOST_CHECK (em.is_temporal(next_x));

    Expr_ptr neg_x = em.make_neg(x);
    BOOST_CHECK (neg_x->f_symb == NEG && neg_x->lhs() == x && neg_x->rhs() == NULL);
    BOOST_CHECK (em.is_neg(neg_x));
    BOOST_CHECK (em.is_unary_arithmetical(neg_x));

    Expr_ptr x_add_y = em.make_add(x, y);
    BOOST_CHECK (x_add_y->f_symb == PLUS && x_add_y->lhs() == x && x_add_y->rhs() == y);
    BOOST_CHECK (em.is_add(x_add_y));
    BOOST_CHECK (em.is_binary_arithmetical(x_add_y));

    Expr_ptr x_sub_y = em.make_sub(x, y);
    BOOST_CHECK (x_sub_y->f_symb == SUB && x_sub_y->lhs() == x && x_sub_y->rhs() == y);
    BOOST_CHECK (em.is_sub(x_sub_y));
    BOOST_CHECK (em.is_binary_arithmetical(x_sub_y));

    Expr_ptr x_div_y = em.make_div(x, y);
    BOOST_CHECK (x_div_y->f_symb == DIV && x_div_y->lhs() == x && x_div_y->rhs() == y);
    BOOST_CHECK (em.is_div(x_div_y));
    BOOST_CHECK (em.is_binary_arithmetical(x_div_y));

    Expr_ptr x_mul_y = em.make_mul(x, y);
    BOOST_CHECK (x_mul_y->f_symb == MUL && x_mul_y->lhs() == x && x_mul_y->rhs() == y);
    BOOST_CHECK (em.is_mul(x_mul_y));
    BOOST_CHECK (em.is_binary_arithmetical(x_mul_y));

    Expr_ptr x_mod_y = em.make_mod(x, y);
    BOOST_CHECK (x_mod_y->f_symb == MOD && x_mod_y->lhs() == x && x_mod_y->rhs() == y);
    BOOST_CHECK (em.is_mod(x_mod_y));
    BOOST_CHECK (em.is_binary_arithmetical(x_mod_y));

    Expr_ptr not_x = em.make_not(x);
    BOOST_CHECK (not_x->f_symb == NOT && not_x->lhs() == x && not_x->rhs() == NULL);
    BOOST_CHECK (em.is_not(not_x));
    BOOST_CHECK (em.is_unary_logical(not_x));

    Expr_ptr x_and_y = em.make_and(x, y);
    BOOST_CHECK (x_and_y->f_symb == AND && x_and_y->lhs() == x && x_and_y->rhs() == y);
    BOOST_CHECK (em.is_and(x_and_y));
    BOOST_CHECK (em.is_binary_logical(x_and_y));

    Expr_ptr x_or_y = em.make_or(x, y);
    BOOST_CHECK (x_or_y->f_symb == OR && x_or_y->lhs() == x && x_or_y->rhs() == y);
    BOOST_CHECK (em.is_or(x_or_y));
    BOOST_CHECK (em.is_binary_logical(x_or_y));

    Expr_ptr x_lshift_y = em.make_lshift(x, y);
    BOOST_CHECK (x_lshift_y->f_symb == LSHIFT &&
                 x_lshift_y->lhs() == x && x_lshift_y->rhs() == y);
    BOOST_CHECK (em.is_lshift(x_lshift_y));
    BOOST_CHECK (em.is_binary_arithmetical(x_lshift_y));

    Expr_ptr x_rshift_y = em.make_rshift(x, y);
    BOOST_CHECK (x_rshift_y->f_symb == RSHIFT &&
                 x_rshift_y->lhs() == x && x_rshift_y->rhs() == y);
    BOOST_CHECK (em.is_rshift(x_rshift_y));
    BOOST_CHECK (em.is_binary_arithmetical(x_rshift_y));

    Expr_ptr x_xor_y = em.make_bw_xor(x, y);
    BOOST_CHECK (x_xor_y->f_symb == BW_XOR && x_xor_y->lhs() == x && x_xor_y->rhs() == y);
    BOOST_CHECK (em.is_bw_xor(x_xor_y));
    BOOST_CHECK (em.is_binary_arithmetical(x_xor_y));

    Expr_ptr x_xnor_y = em.make_bw_xnor(x, y);
    BOOST_CHECK (x_xnor_y->f_symb == BW_XNOR && x_xnor_y->lhs() == x && x_xnor_y->rhs() == y);
    BOOST_CHECK (em.is_bw_xnor(x_xnor_y));
    BOOST_CHECK (em.is_binary_arithmetical(x_xnor_y));

    Expr_ptr x_implies_y = em.make_implies(x, y);
    BOOST_CHECK (x_implies_y->f_symb == IMPLIES &&
                 x_implies_y->lhs() == x && x_implies_y->rhs() == y);
    BOOST_CHECK (em.is_implies(x_implies_y));
    BOOST_CHECK (em.is_binary_logical(x_implies_y));

    Expr_ptr x_eq_y = em.make_eq(x, y);
    BOOST_CHECK (x_eq_y->f_symb == EQ && x_eq_y->lhs() == x && x_eq_y->rhs() == y);
    BOOST_CHECK (em.is_eq(x_eq_y));
    BOOST_CHECK (em.is_binary_relational(x_eq_y));

    Expr_ptr x_ne_y = em.make_ne(x, y);
    BOOST_CHECK (x_ne_y->f_symb == NE && x_ne_y->lhs() == x && x_ne_y->rhs() == y);
    BOOST_CHECK (em.is_ne(x_ne_y));
    BOOST_CHECK (em.is_binary_relational(x_ne_y));

    Expr_ptr x_ge_y = em.make_ge(x, y);
    BOOST_CHECK (x_ge_y->f_symb == GE && x_ge_y->lhs() == x && x_ge_y->rhs() == y);
    BOOST_CHECK (em.is_ge(x_ge_y));
    BOOST_CHECK (em.is_binary_relational(x_ge_y));

    Expr_ptr x_gt_y = em.make_gt(x, y);
    BOOST_CHECK (x_gt_y->f_symb == GT && x_gt_y->lhs() == x && x_gt_y->rhs() == y);
    BOOST_CHECK (em.is_gt(x_gt_y));
    BOOST_CHECK (em.is_binary_relational(x_gt_y));

    Expr_ptr x_le_y = em.make_le(x, y);
    BOOST_CHECK (x_le_y->f_symb == LE && x_le_y->lhs() == x && x_le_y->rhs() == y);
    BOOST_CHECK (em.is_le(x_le_y));
    BOOST_CHECK (em.is_binary_relational(x_le_y));

    Expr_ptr x_lt_y = em.make_lt(x, y);
    BOOST_CHECK (x_lt_y->f_symb == LT && x_lt_y->lhs() == x && x_lt_y->rhs() == y);
    BOOST_CHECK (em.is_lt(x_lt_y));
    BOOST_CHECK (em.is_binary_relational(x_lt_y));

    Expr_ptr x_cond_y = em.make_cond(x, y);
    BOOST_CHECK (x_cond_y->f_symb == COND && x_cond_y->lhs() == x && x_cond_y->rhs() == y);
    BOOST_CHECK (em.is_cond(x_cond_y));

    Expr_ptr x_ite_y = em.make_ite(x, y);
    BOOST_CHECK (x_ite_y->f_symb == ITE && x_ite_y->lhs() == x && x_ite_y->rhs() == y);
    BOOST_CHECK (em.is_ite(x_ite_y));

    Expr_ptr iconst_42 = em.make_const(42);
    BOOST_CHECK (em.is_int_const(iconst_42) && iconst_42->value() == 42);
    BOOST_CHECK (em.is_constant(iconst_42));
    BOOST_CHECK (42 == em.const_value(iconst_42));

    Expr_ptr hconst_42 = em.make_hconst(0x2a);
    BOOST_CHECK (em.is_int_const(hconst_42) && hconst_42->value() == 42);
    BOOST_CHECK (em.is_constant(hconst_42));
    BOOST_CHECK (42 == em.const_value(hconst_42));

    Expr_ptr oconst_42 = em.make_oconst(052);
    BOOST_CHECK (em.is_int_const(oconst_42) && oconst_42->value() == 42);
    BOOST_CHECK (em.is_constant(oconst_42));
    BOOST_CHECK (42 == em.const_value(oconst_42));

    Expr_ptr x_dot_y = em.make_dot(x, y);
    BOOST_CHECK (x_dot_y->f_symb == DOT && x_dot_y->lhs() == x && x_dot_y->rhs() == y);
    BOOST_CHECK (em.is_dot(x_dot_y));

    Expr_ptr x_params_y = em.make_params(x, y);
    BOOST_CHECK (x_params_y->f_symb == PARAMS &&
                 x_params_y->lhs() == x && x_params_y->rhs() == y);
    BOOST_CHECK (em.is_params(x_params_y));

    BOOST_CHECK( em.make_dot(x, y) == x_dot_y);
}

BOOST_AUTO_TEST_CASE(builtin)
{
    ExprMgr& em(ExprMgr::INSTANCE());

    Expr_ptr empty = em.make_empty();
    BOOST_CHECK (em.is_identifier(empty) && empty->atom() == Atom( EMPTY_TOKEN ));
    BOOST_CHECK (em.is_empty(empty));

    Expr_ptr false_ = em.make_false();
    BOOST_CHECK (em.is_identifier(false_) && false_->atom() == Atom( FALSE_TOKEN ));
    BOOST_CHECK (em.is_false(false_));

    Expr_ptr true_ = em.make_true();
    BOOST_CHECK (em.is_identifier(true_) && true_->atom() == Atom( TRUE_TOKEN ));
    BOOST_CHECK (em.is_true(true_));

    Expr_ptr zero = em.make_zero();
    BOOST_CHECK( em.is_constant(zero));
    BOOST_CHECK( em.is_zero( zero));

    Expr_ptr one = em.make_one();
    BOOST_CHECK( em.is_constant(one));
    BOOST_CHECK( em.is_one( one));
}

BOOST_AUTO_TEST_CASE(printer)
{
    ExprMgr& em(ExprMgr::INSTANCE());

    Atom a_x("x");
    Atom a_y("y");

    Expr_ptr x = em.make_identifier(a_x);
    {
        std::ostringstream oss;
        Printer printer(oss);
        printer << x; BOOST_CHECK (oss.str() == std::string("x"));
    }

    Expr_ptr y = em.make_identifier(a_y);
    {
        std::ostringstream oss;
        Printer printer(oss);
        printer << y; BOOST_CHECK (oss.str() == std::string("y"));
    }

    // primary printers
    {
        Expr_ptr next_x = em.make_next(x);
        std::ostringstream oss;
        Printer printer(oss);
        printer << next_x; BOOST_CHECK (oss.str() == std::string("next(x)"));
    }

    {
        Expr_ptr neg_x = em.make_neg(x);
        std::ostringstream oss;
        Printer printer(oss);
        printer << neg_x; BOOST_CHECK (oss.str() == std::string("-x"));
    }

    {
        Expr_ptr not_x = em.make_not(x);
        std::ostringstream oss;
        Printer printer(oss);
        printer << not_x; BOOST_CHECK (oss.str() == std::string("! x"));
    }

    {
        Expr_ptr not_x = em.make_bw_not(x);
        std::ostringstream oss;
        Printer printer(oss);
        printer << not_x; BOOST_CHECK (oss.str() == std::string("~ x"));
    }

    {
        Expr_ptr x_add_y = em.make_add(x, y);
        std::ostringstream oss;
        Printer printer(oss);
        printer << x_add_y; BOOST_CHECK (oss.str() == std::string("(x + y)"));
    }

    {
        Expr_ptr x_sub_y = em.make_sub(x, y);
        std::ostringstream oss;
        Printer printer(oss);
        printer << x_sub_y; BOOST_CHECK (oss.str() == std::string("(x - y)"));
    }

    {
        Expr_ptr x_div_y = em.make_div(x, y);
        std::ostringstream oss;
        Printer printer(oss);
        printer << x_div_y; BOOST_CHECK (oss.str() == std::string("(x / y)"));
    }

    {
        Expr_ptr x_mod_y = em.make_mod(x, y);
        std::ostringstream oss;
        Printer printer(oss);
        printer << x_mod_y; BOOST_CHECK (oss.str() == std::string("(x % y)"));
    }

    {
        Expr_ptr x_mul_y = em.make_mul(x, y);
        std::ostringstream oss;
        Printer printer(oss);
        printer << x_mul_y; BOOST_CHECK (oss.str() == std::string("(x * y)"));
    }

    {
        Expr_ptr x_and_y = em.make_and(x, y);
        std::ostringstream oss;
        Printer printer(oss);
        printer << x_and_y; BOOST_CHECK (oss.str() == std::string("(x && y)"));
    }

    {
        Expr_ptr x_or_y = em.make_or(x, y);
        std::ostringstream oss;
        Printer printer(oss);
        printer << x_or_y; BOOST_CHECK (oss.str() == std::string("(x || y)"));
    }

    {
        Expr_ptr x_lshift_y = em.make_lshift(x, y);
        std::ostringstream oss;
        Printer printer(oss);
        printer << x_lshift_y; BOOST_CHECK (oss.str() == std::string("(x << y)"));
    }

    {
        Expr_ptr x_rshift_y = em.make_rshift(x, y);
        std::ostringstream oss;
        Printer printer(oss);
        printer << x_rshift_y; BOOST_CHECK (oss.str() == std::string("(x >> y)"));
    }

    {
        Expr_ptr x_xor_y = em.make_bw_xor(x, y);
        std::ostringstream oss;
        Printer printer(oss);
        printer << x_xor_y; BOOST_CHECK (oss.str() == std::string("(x ^ y)"));
    }

    {
        Expr_ptr x_xnor_y = em.make_bw_xnor(x, y);
        std::ostringstream oss;
        Printer printer(oss);
        printer << x_xnor_y; BOOST_CHECK (oss.str() == std::string("(x !^ y)"));
    }

    {
        Expr_ptr x_implies_y = em.make_implies(x, y);
        std::ostringstream oss;
        Printer printer(oss);
        printer << x_implies_y; BOOST_CHECK (oss.str() == std::string("(x -> y)"));
    }

    {
        Expr_ptr x_eq_y = em.make_eq(x, y);
        std::ostringstream oss;
        Printer printer(oss);
        printer << x_eq_y; BOOST_CHECK (oss.str() == std::string("(x = y)"));
    }

    {
        Expr_ptr x_ne_y = em.make_ne(x, y);
        std::ostringstream oss;
        Printer printer(oss);
        printer << x_ne_y; BOOST_CHECK (oss.str() == std::string("(x != y)"));
    }

    {
        Expr_ptr x_ge_y = em.make_ge(x, y);
        std::ostringstream oss;
        Printer printer(oss);
        printer << x_ge_y; BOOST_CHECK (oss.str() == std::string("(x >= y)"));
    }

    {
        Expr_ptr x_gt_y = em.make_gt(x, y);
        std::ostringstream oss;
        Printer printer(oss);
        printer << x_gt_y; BOOST_CHECK (oss.str() == std::string("(x > y)"));
    }

    {
        Expr_ptr x_le_y = em.make_le(x, y);
        std::ostringstream oss;
        Printer printer(oss);
        printer << x_le_y; BOOST_CHECK (oss.str() == std::string("(x <= y)"));
    }

    {
        Expr_ptr x_lt_y = em.make_lt(x, y);
        std::ostringstream oss;
        Printer printer(oss);
        printer << x_lt_y; BOOST_CHECK (oss.str() == std::string("(x < y)"));
    }

    {
        Expr_ptr x_cond_y = em.make_cond(x, y);
        std::ostringstream oss;
        Printer printer(oss);
        printer << x_cond_y; BOOST_CHECK (oss.str() == std::string("(x ? y)"));
    }

    {
        Expr_ptr x_ite_y = em.make_ite(x, y);
        std::ostringstream oss;
        Printer printer(oss);
        printer << x_ite_y; BOOST_CHECK (oss.str() == std::string("(x : y)"));
    }

    {
        Expr_ptr iconst_42 = em.make_const(42);
        std::ostringstream oss;
        Printer printer(oss);
        printer << iconst_42; BOOST_CHECK (oss.str() == std::string("42"));
    }

    {
        Expr_ptr hconst_42 = em.make_hconst(0x2a);
        std::ostringstream oss;
        Printer printer(oss);
        printer << hconst_42; BOOST_CHECK (oss.str() == std::string("0x2a"));
    }

    {
        Expr_ptr oconst_42 = em.make_oconst(052);
        std::ostringstream oss;
        Printer printer(oss);
        printer << oconst_42; BOOST_CHECK (oss.str() == std::string("052"));
    }

    {
        Expr_ptr x_dot_y = em.make_dot(x, y);
        std::ostringstream oss;
        Printer printer(oss);
        printer << x_dot_y; BOOST_CHECK (oss.str() == std::string("x.y"));
    }

    {
        Expr_ptr x_params_y = em.make_params(x, y);
        std::ostringstream oss;
        Printer printer(oss);
        printer << x_params_y; BOOST_CHECK (oss.str() == std::string("x(y)"));
    }

    // LTL
    {
        Expr_ptr Fx = em.make_F(x);
        std::ostringstream oss;
        Printer printer(oss);
        printer << Fx; BOOST_CHECK (oss.str() == std::string("F (x)"));
    }

    {
        Expr_ptr Gx = em.make_G(x);
        std::ostringstream oss;
        Printer printer(oss);
        printer << Gx; BOOST_CHECK (oss.str() == std::string("G (x)"));
    }

    {
        Expr_ptr Xx = em.make_X(x);
        std::ostringstream oss;
        Printer printer(oss);
        printer << Xx; BOOST_CHECK (oss.str() == std::string("X (x)"));
    }

    {
        Expr_ptr xUy = em.make_U(x, y);
        std::ostringstream oss;
        Printer printer(oss);
        printer << xUy; BOOST_CHECK (oss.str() == std::string("(x U y)"));
    }

    {
        Expr_ptr xRy = em.make_R(x, y);
        std::ostringstream oss;
        Printer printer(oss);
        printer << xRy; BOOST_CHECK (oss.str() == std::string("(x R y)"));
    }

    {
        Expr_ptr false_ = em.make_false();
        std::ostringstream oss;
        Printer printer(oss);
        printer << false_; BOOST_CHECK (oss.str() == std::string("FALSE"));
    }

    {
        Expr_ptr true_ = em.make_true();
        std::ostringstream oss;
        Printer printer(oss);
        printer << true_; BOOST_CHECK (oss.str() == std::string("TRUE"));
    }

}

// BOOST_AUTO_TEST_CASE(fqexpr)
// {
//     ExprMgr& em = ExprMgr::INSTANCE();
//     Atom a_x("x");

//     Expr_ptr x = em.make_identifier(a_x);
//     Expr_ptr main_ = em.make_main();

//     {

//         const FQExpr& fqexpr = FQExpr(main_, x, 7);

//         std::ostringstream oss;
//         oss << fqexpr; BOOST_CHECK (oss.str() == std::string("@7{main::x}"));
//     }

//     {

//         const FQExpr& fqexpr = FQExpr(main_, x, 0);

//         std::ostringstream oss;
//         oss << fqexpr; BOOST_CHECK (oss.str() == std::string("@0{main::x}"));
//     }
// }

BOOST_AUTO_TEST_SUITE_END()

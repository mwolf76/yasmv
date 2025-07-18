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

#include <expr/expr.hh>
#include <expr/expr_mgr.hh>

#include <expr/time/analyzer/analyzer.hh>
#include <expr/time/expander/expander.hh>

#include <expr/printer/printer.hh>

BOOST_AUTO_TEST_SUITE(tests)
BOOST_AUTO_TEST_CASE(expressions)
{
    expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };

    expr::Atom a_x { "x" };
    expr::Atom a_y { "y" };

    expr::Expr_ptr x { em.make_identifier(a_x) };
    BOOST_CHECK(x == em.make_identifier(a_x));

    expr::Expr_ptr y { em.make_identifier(a_y) };
    BOOST_CHECK(y == em.make_identifier(a_y));


    // primary makers and is-a predicates
    expr::Expr_ptr next_x { em.make_next(x) };
    BOOST_CHECK(next_x->f_symb == expr::NEXT && next_x->lhs() == x && next_x->rhs() == NULL);
    BOOST_CHECK(em.is_next(next_x));
    BOOST_CHECK(em.is_temporal(next_x));

    expr::Expr_ptr at_42_x { em.make_at(em.make_instant(42), x) };
    BOOST_CHECK(at_42_x->f_symb == expr::AT && at_42_x->lhs()->f_symb == expr::INSTANT &&
                at_42_x->lhs()->value() == 42 && at_42_x->rhs() == x);
    BOOST_CHECK(em.is_at(at_42_x));
    BOOST_CHECK(em.is_temporal(at_42_x));

    expr::Expr_ptr neg_x { em.make_neg(x) };
    BOOST_CHECK(neg_x->f_symb == expr::NEG && neg_x->lhs() == x && neg_x->rhs() == NULL);
    BOOST_CHECK(em.is_neg(neg_x));
    BOOST_CHECK(em.is_unary_arithmetical(neg_x));

    expr::Expr_ptr x_add_y { em.make_add(x, y) };
    BOOST_CHECK(x_add_y->f_symb == expr::PLUS && x_add_y->lhs() == x && x_add_y->rhs() == y);
    BOOST_CHECK(em.is_add(x_add_y));
    BOOST_CHECK(em.is_binary_arithmetical(x_add_y));

    expr::Expr_ptr x_sub_y { em.make_sub(x, y) };
    BOOST_CHECK(x_sub_y->f_symb == expr::SUB && x_sub_y->lhs() == x && x_sub_y->rhs() == y);
    BOOST_CHECK(em.is_sub(x_sub_y));
    BOOST_CHECK(em.is_binary_arithmetical(x_sub_y));

    expr::Expr_ptr x_div_y { em.make_div(x, y) };
    BOOST_CHECK(x_div_y->f_symb == expr::DIV && x_div_y->lhs() == x && x_div_y->rhs() == y);
    BOOST_CHECK(em.is_div(x_div_y));
    BOOST_CHECK(em.is_binary_arithmetical(x_div_y));

    expr::Expr_ptr x_mul_y { em.make_mul(x, y) };
    BOOST_CHECK(x_mul_y->f_symb == expr::MUL && x_mul_y->lhs() == x && x_mul_y->rhs() == y);
    BOOST_CHECK(em.is_mul(x_mul_y));
    BOOST_CHECK(em.is_binary_arithmetical(x_mul_y));

    expr::Expr_ptr x_mod_y { em.make_mod(x, y) };
    BOOST_CHECK(x_mod_y->f_symb == expr::MOD && x_mod_y->lhs() == x && x_mod_y->rhs() == y);
    BOOST_CHECK(em.is_mod(x_mod_y));
    BOOST_CHECK(em.is_binary_arithmetical(x_mod_y));

    expr::Expr_ptr not_x { em.make_not(x) };
    BOOST_CHECK(not_x->f_symb == expr::NOT && not_x->lhs() == x && not_x->rhs() == NULL);
    BOOST_CHECK(em.is_not(not_x));
    BOOST_CHECK(em.is_unary_logical(not_x));

    expr::Expr_ptr x_and_y { em.make_and(x, y) };
    BOOST_CHECK(x_and_y->f_symb == expr::AND && x_and_y->lhs() == x && x_and_y->rhs() == y);
    BOOST_CHECK(em.is_and(x_and_y));
    BOOST_CHECK(em.is_binary_logical(x_and_y));

    expr::Expr_ptr x_or_y { em.make_or(x, y) };
    BOOST_CHECK(x_or_y->f_symb == expr::OR && x_or_y->lhs() == x && x_or_y->rhs() == y);
    BOOST_CHECK(em.is_or(x_or_y));
    BOOST_CHECK(em.is_binary_logical(x_or_y));

    expr::Expr_ptr x_lshift_y { em.make_lshift(x, y) };
    BOOST_CHECK(x_lshift_y->f_symb == expr::LSHIFT &&
                x_lshift_y->lhs() == x &&
                x_lshift_y->rhs() == y);
    BOOST_CHECK(em.is_lshift(x_lshift_y));
    BOOST_CHECK(em.is_binary_arithmetical(x_lshift_y));

    expr::Expr_ptr x_rshift_y { em.make_rshift(x, y) };
    BOOST_CHECK(x_rshift_y->f_symb == expr::RSHIFT &&
                x_rshift_y->lhs() == x && x_rshift_y->rhs() == y);
    BOOST_CHECK(em.is_rshift(x_rshift_y));
    BOOST_CHECK(em.is_binary_arithmetical(x_rshift_y));

    expr::Expr_ptr x_xor_y { em.make_bw_xor(x, y) };
    BOOST_CHECK(x_xor_y->f_symb == expr::BW_XOR && x_xor_y->lhs() == x && x_xor_y->rhs() == y);
    BOOST_CHECK(em.is_bw_xor(x_xor_y));
    BOOST_CHECK(em.is_binary_arithmetical(x_xor_y));

    expr::Expr_ptr x_xnor_y { em.make_bw_xnor(x, y) };
    BOOST_CHECK(x_xnor_y->f_symb == expr::BW_XNOR && x_xnor_y->lhs() == x && x_xnor_y->rhs() == y);
    BOOST_CHECK(em.is_bw_xnor(x_xnor_y));
    BOOST_CHECK(em.is_binary_arithmetical(x_xnor_y));

    expr::Expr_ptr x_implies_y { em.make_implies(x, y) };
    BOOST_CHECK(x_implies_y->f_symb == expr::IMPLIES &&
                x_implies_y->lhs() == x && x_implies_y->rhs() == y);
    BOOST_CHECK(em.is_implies(x_implies_y));
    BOOST_CHECK(em.is_binary_logical(x_implies_y));

    expr::Expr_ptr x_eq_y { em.make_eq(x, y) };
    BOOST_CHECK(x_eq_y->f_symb == expr::EQ && x_eq_y->lhs() == x && x_eq_y->rhs() == y);
    BOOST_CHECK(em.is_eq(x_eq_y));
    BOOST_CHECK(em.is_binary_relational(x_eq_y));

    expr::Expr_ptr x_ne_y { em.make_ne(x, y) };
    BOOST_CHECK(x_ne_y->f_symb == expr::NE && x_ne_y->lhs() == x && x_ne_y->rhs() == y);
    BOOST_CHECK(em.is_ne(x_ne_y));
    BOOST_CHECK(em.is_binary_relational(x_ne_y));

    expr::Expr_ptr x_ge_y { em.make_ge(x, y) };
    BOOST_CHECK(x_ge_y->f_symb == expr::GE && x_ge_y->lhs() == x && x_ge_y->rhs() == y);
    BOOST_CHECK(em.is_ge(x_ge_y));
    BOOST_CHECK(em.is_binary_relational(x_ge_y));

    expr::Expr_ptr x_gt_y { em.make_gt(x, y) };
    BOOST_CHECK(x_gt_y->f_symb == expr::GT && x_gt_y->lhs() == x && x_gt_y->rhs() == y);
    BOOST_CHECK(em.is_gt(x_gt_y));
    BOOST_CHECK(em.is_binary_relational(x_gt_y));

    expr::Expr_ptr x_le_y { em.make_le(x, y) };
    BOOST_CHECK(x_le_y->f_symb == expr::LE && x_le_y->lhs() == x && x_le_y->rhs() == y);
    BOOST_CHECK(em.is_le(x_le_y));
    BOOST_CHECK(em.is_binary_relational(x_le_y));

    expr::Expr_ptr x_lt_y { em.make_lt(x, y) };
    BOOST_CHECK(x_lt_y->f_symb == expr::LT && x_lt_y->lhs() == x && x_lt_y->rhs() == y);
    BOOST_CHECK(em.is_lt(x_lt_y));
    BOOST_CHECK(em.is_binary_relational(x_lt_y));

    expr::Expr_ptr x_cond_y { em.make_cond(x, y) };
    BOOST_CHECK(x_cond_y->f_symb == expr::COND && x_cond_y->lhs() == x && x_cond_y->rhs() == y);
    BOOST_CHECK(em.is_cond(x_cond_y));

    expr::Expr_ptr x_ite_y { em.make_ite(x, y) };
    BOOST_CHECK(x_ite_y->f_symb == expr::ITE && x_ite_y->lhs() == x && x_ite_y->rhs() == y);
    BOOST_CHECK(em.is_ite(x_ite_y));

    expr::Expr_ptr iconst_42 { em.make_const(42) };
    BOOST_CHECK(em.is_int_const(iconst_42) && iconst_42->value() == 42);
    BOOST_CHECK(em.is_constant(iconst_42));
    BOOST_CHECK(42 == em.const_value(iconst_42));

    expr::Expr_ptr hconst_42 { em.make_hconst(0x2a) };
    BOOST_CHECK(em.is_int_const(hconst_42) && hconst_42->value() == 42);
    BOOST_CHECK(em.is_constant(hconst_42));
    BOOST_CHECK(42 == em.const_value(hconst_42));

    expr::Expr_ptr oconst_42 { em.make_oconst(052) };
    BOOST_CHECK(em.is_int_const(oconst_42) && oconst_42->value() == 42);
    BOOST_CHECK(em.is_constant(oconst_42));
    BOOST_CHECK(42 == em.const_value(oconst_42));

    expr::Expr_ptr x_dot_y { em.make_dot(x, y) };
    BOOST_CHECK(x_dot_y->f_symb == expr::DOT && x_dot_y->lhs() == x && x_dot_y->rhs() == y);
    BOOST_CHECK(em.is_dot(x_dot_y));

    expr::Expr_ptr x_params_y { em.make_params(x, y) };
    BOOST_CHECK(x_params_y->f_symb == expr::PARAMS &&
                x_params_y->lhs() == x && x_params_y->rhs() == y);
    BOOST_CHECK(em.is_params(x_params_y));

    BOOST_CHECK(em.make_dot(x, y) == x_dot_y);
}

BOOST_AUTO_TEST_CASE(builtin)
{
    expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };
    expr::Expr_ptr empty { em.make_empty() };

    BOOST_CHECK(em.is_identifier(empty) && empty->atom() == expr::Atom(EMPTY_TOKEN));
    BOOST_CHECK(em.is_empty(empty));

    expr::Expr_ptr false_ { em.make_false() };
    BOOST_CHECK(em.is_identifier(false_) && false_->atom() == expr::Atom(FALSE_TOKEN));
    BOOST_CHECK(em.is_false(false_));

    expr::Expr_ptr true_ { em.make_true() };
    BOOST_CHECK(em.is_identifier(true_) && true_->atom() == expr::Atom(TRUE_TOKEN));
    BOOST_CHECK(em.is_true(true_));

    expr::Expr_ptr zero { em.make_zero() };
    BOOST_CHECK(em.is_constant(zero));
    BOOST_CHECK(em.is_zero(zero));

    expr::Expr_ptr one { em.make_one() };
    BOOST_CHECK(em.is_constant(one));
    BOOST_CHECK(em.is_one(one));
}

BOOST_AUTO_TEST_CASE(printer)
{
    expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };

    expr::Atom a_x { "x" };
    expr::Atom a_y { "y" };

    expr::Expr_ptr x { em.make_identifier(a_x) };
    {
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << x;
        BOOST_CHECK(oss.str() == std::string("x"));
    }

    expr::Expr_ptr y { em.make_identifier(a_y) };
    {
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << y;
        BOOST_CHECK(oss.str() == std::string("y"));
    }


    // primary printers
    {
        expr::Expr_ptr next_x { em.make_next(x) };

        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << next_x;
        BOOST_CHECK(oss.str() == std::string("next(x)"));
    }

    {
        expr::Expr_ptr neg_x { em.make_neg(x) };

        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << neg_x;
        BOOST_CHECK(oss.str() == std::string("-x"));
    }

    {
        expr::Expr_ptr not_x { em.make_not(x) };

        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << not_x;
        BOOST_CHECK(oss.str() == std::string("! x"));
    }

    {
        expr::Expr_ptr not_x { em.make_bw_not(x) };

        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << not_x;
        BOOST_CHECK(oss.str() == std::string("~ x"));
    }

    {
        expr::Expr_ptr x_add_y { em.make_add(x, y) };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << x_add_y;
        BOOST_CHECK(oss.str() == std::string("(x + y)"));
    }

    {
        expr::Expr_ptr x_sub_y { em.make_sub(x, y) };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << x_sub_y;
        BOOST_CHECK(oss.str() == std::string("(x - y)"));
    }

    {
        expr::Expr_ptr x_div_y { em.make_div(x, y) };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << x_div_y;
        BOOST_CHECK(oss.str() == std::string("(x / y)"));
    }

    {
        expr::Expr_ptr x_mod_y { em.make_mod(x, y) };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << x_mod_y;
        BOOST_CHECK(oss.str() == std::string("(x % y)"));
    }

    {
        expr::Expr_ptr x_mul_y { em.make_mul(x, y) };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << x_mul_y;
        BOOST_CHECK(oss.str() == std::string("(x * y)"));
    }

    {
        expr::Expr_ptr x_and_y { em.make_and(x, y) };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << x_and_y;
        BOOST_CHECK(oss.str() == std::string("(x && y)"));
    }

    {
        expr::Expr_ptr x_or_y { em.make_or(x, y) };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << x_or_y;
        BOOST_CHECK(oss.str() == std::string("(x || y)"));
    }

    {
        expr::Expr_ptr x_lshift_y { em.make_lshift(x, y) };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << x_lshift_y;
        BOOST_CHECK(oss.str() == std::string("(x << y)"));
    }

    {
        expr::Expr_ptr x_rshift_y { em.make_rshift(x, y) };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << x_rshift_y;
        BOOST_CHECK(oss.str() == std::string("(x >> y)"));
    }

    {
        expr::Expr_ptr x_xor_y { em.make_bw_xor(x, y) };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << x_xor_y;
        BOOST_CHECK(oss.str() == std::string("(x ^ y)"));
    }

    {
        expr::Expr_ptr x_xnor_y { em.make_bw_xnor(x, y) };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << x_xnor_y;
        BOOST_CHECK(oss.str() == std::string("(x ~^ y)"));
    }

    {
        expr::Expr_ptr x_implies_y { em.make_implies(x, y) };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << x_implies_y;
        BOOST_CHECK(oss.str() == std::string("(x -> y)"));
    }

    {
        expr::Expr_ptr x_eq_y { em.make_eq(x, y) };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << x_eq_y;
        BOOST_CHECK(oss.str() == std::string("(x = y)"));
    }

    {
        expr::Expr_ptr x_ne_y { em.make_ne(x, y) };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << x_ne_y;
        BOOST_CHECK(oss.str() == std::string("(x != y)"));
    }

    {
        expr::Expr_ptr x_ge_y { em.make_ge(x, y) };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << x_ge_y;
        BOOST_CHECK(oss.str() == std::string("(x >= y)"));
    }

    {
        expr::Expr_ptr x_gt_y { em.make_gt(x, y) };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << x_gt_y;
        BOOST_CHECK(oss.str() == std::string("(x > y)"));
    }

    {
        expr::Expr_ptr x_le_y { em.make_le(x, y) };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << x_le_y;
        BOOST_CHECK(oss.str() == std::string("(x <= y)"));
    }

    {
        expr::Expr_ptr x_lt_y { em.make_lt(x, y) };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << x_lt_y;
        BOOST_CHECK(oss.str() == std::string("(x < y)"));
    }

    {
        expr::Expr_ptr x_cond_y { em.make_cond(x, y) };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << x_cond_y;
        BOOST_CHECK(oss.str() == std::string("(x ? y)"));
    }

    {
        expr::Expr_ptr x_ite_y { em.make_ite(x, y) };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << x_ite_y;
        BOOST_CHECK(oss.str() == std::string("(x : y)"));
    }

    {
        expr::Expr_ptr iconst_42 { em.make_const(42) };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << iconst_42;
        BOOST_CHECK(oss.str() == std::string("42"));
    }

    {
        expr::Expr_ptr hconst_42 { em.make_hconst(0x2a) };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << hconst_42;
        BOOST_CHECK(oss.str() == std::string("0x2a"));
    }

    {
        expr::Expr_ptr oconst_42 { em.make_oconst(052) };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << oconst_42;
        BOOST_CHECK(oss.str() == std::string("052"));
    }

    {
        expr::Expr_ptr x_dot_y { em.make_dot(x, y) };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << x_dot_y;
        BOOST_CHECK(oss.str() == std::string("x.y"));
    }

    {
        expr::Expr_ptr x_params_y { em.make_params(x, y) };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << x_params_y;
        BOOST_CHECK(oss.str() == std::string("x(y)"));
    }


    {
        expr::Expr_ptr false_ { em.make_false() };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << false_;
        BOOST_CHECK(oss.str() == std::string("FALSE"));
    }

    {
        expr::Expr_ptr true_ { em.make_true() };
        std::ostringstream oss;
        expr::Printer printer(oss);
        printer << true_;
        BOOST_CHECK(oss.str() == std::string("TRUE"));
    }
}

BOOST_AUTO_TEST_CASE(analyzer)
{
    expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };
    expr::time::Analyzer eta { em };

    expr::Atom a_x { "x" };
    expr::Expr_ptr x { em.make_identifier(a_x) };

    expr::Expr_ptr pos_instant { em.make_instant(5) };
    expr::Expr_ptr neg_instant { em.make_instant(-3) };

    // Test basic expression without time references
    eta.process(x);
    BOOST_CHECK(!eta.has_forward_time());
    BOOST_CHECK(!eta.has_backward_time());
    BOOST_CHECK(!eta.has_intervals());

    // Test forward time reference
    expr::Expr_ptr forward_at { em.make_at(pos_instant, x) };
    eta.process(forward_at);
    BOOST_CHECK(eta.has_forward_time());
    BOOST_CHECK(!eta.has_backward_time());
    BOOST_CHECK(!eta.has_intervals());

    // Test backward time reference
    expr::Expr_ptr backward_at { em.make_at(neg_instant, x) };
    eta.process(backward_at);
    BOOST_CHECK(!eta.has_forward_time());
    BOOST_CHECK(eta.has_backward_time());
    BOOST_CHECK(!eta.has_intervals());

    // Test interval (contains both forward and backward time since it spans from -3 to 5)
    expr::Expr_ptr interval { em.make_interval(neg_instant, pos_instant) };
    expr::Expr_ptr interval_at { em.make_at(interval, x) };
    eta.process(interval_at);
    BOOST_CHECK(eta.has_forward_time());
    BOOST_CHECK(eta.has_backward_time());
    BOOST_CHECK(eta.has_intervals());

    // Test complex expression with multiple time features
    expr::Expr_ptr complex_expr { em.make_and(forward_at, backward_at) };
    eta.process(complex_expr);
    BOOST_CHECK(eta.has_forward_time());
    BOOST_CHECK(eta.has_backward_time());
    BOOST_CHECK(!eta.has_intervals());

    // Test expression with all time features
    expr::Expr_ptr all_features { em.make_and(complex_expr, interval_at) };
    eta.process(all_features);
    BOOST_CHECK(eta.has_forward_time());
    BOOST_CHECK(eta.has_backward_time());
    BOOST_CHECK(eta.has_intervals());
}


BOOST_AUTO_TEST_CASE(expander)
{
    expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };

    expr::Atom a_x { "x" };
    expr::Expr_ptr x { em.make_identifier(a_x) };
    expr::Expr_ptr _0 { em.make_instant(0) };
    expr::Expr_ptr _3 { em.make_instant(3) };

    expr::time::Expander expander { em };

    BOOST_CHECK(x == expander.process(x));
    BOOST_CHECK(em.make_at(_0, x) == expander.process(em.make_at(_0, x)));
    BOOST_CHECK(em.make_at(_3, x) == expander.process(em.make_at(_3, x)));

    BOOST_CHECK(em.make_and(em.make_and(em.make_and(em.make_at(em.make_instant(0), x),
                                                    em.make_at(em.make_instant(1), x)),
                                        em.make_at(em.make_instant(2), x)),
                            em.make_at(em.make_instant(3), x)) ==
                expander.process(em.make_at(em.make_interval(_0, _3), x)));

    BOOST_CHECK(em.make_and(em.make_and(em.make_and(em.make_at(em.make_instant(0), x),
                                                    em.make_at(em.make_instant(1), x)),
                                        em.make_at(em.make_instant(2), x)),
                            em.make_at(em.make_instant(3), x)) ==
                expander.process(em.make_at(em.make_interval(_3, _0), x)));
}

BOOST_AUTO_TEST_SUITE_END()

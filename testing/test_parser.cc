/**
 * @file test_parser.cc
 * @brief Parser unit tests
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
#include <parse.hh>
#include <printer.hh>

#include <type.hh>

BOOST_AUTO_TEST_SUITE(tests)
BOOST_AUTO_TEST_CASE(parsing_identifiers)
{
    expr::ExprMgr& em
        (expr::ExprMgr::INSTANCE());

    expr::Atom a_x
        ("x");
    expr::Atom a_y
        ("y");

    expr::Expr_ptr x
        (em.make_identifier(a_x));
    expr::Expr_ptr y
        (em.make_identifier(a_y));

    BOOST_CHECK (x != y);

    /* test identifiers canonicity */
    BOOST_CHECK(x == em.make_identifier(a_x));
    BOOST_CHECK(x == em.make_identifier("x"));

    BOOST_CHECK(y == em.make_identifier(a_y));
    BOOST_CHECK(y == em.make_identifier("y"));
}

BOOST_AUTO_TEST_CASE(temporal_expressions)
{
    expr::ExprMgr& em
        (expr::ExprMgr::INSTANCE());

    expr::Atom a_x
        ("x");
    expr::Atom a_y
        ("y");

    expr::Expr_ptr x
        (em.make_identifier(a_x));
    expr::Expr_ptr y
        (em.make_identifier(a_y));

    BOOST_CHECK (em.make_F(x) == parse::parseExpression("F x"));
    BOOST_CHECK (em.make_F(x) == parse::parseExpression("F(x)"));

    BOOST_CHECK (em.make_G(x) == parse::parseExpression("G x"));
    BOOST_CHECK (em.make_G(x) == parse::parseExpression("G(x)"));

    BOOST_CHECK (em.make_X(x) == parse::parseExpression("X x"));
    BOOST_CHECK (em.make_X(x) == parse::parseExpression("X(x)"));

    BOOST_CHECK (em.make_G(em.make_F(x)) == parse::parseExpression("G F x"));
    BOOST_CHECK (em.make_G(em.make_F(x)) == parse::parseExpression("G(F x)"));
    BOOST_CHECK (em.make_G(em.make_F(x)) == parse::parseExpression("G(F(x))"));

    BOOST_CHECK (em.make_F(em.make_G(x)) == parse::parseExpression("F G x"));
    BOOST_CHECK (em.make_F(em.make_G(x)) == parse::parseExpression("F(G x)"));
    BOOST_CHECK (em.make_F(em.make_G(x)) == parse::parseExpression("F(G(x))"));

    BOOST_CHECK(em.make_U(x, y) == parse::parseExpression("x U y"));
    BOOST_CHECK(em.make_U(x, y) == parse::parseExpression("(x) U (y)"));

    BOOST_CHECK(em.make_R(x, y) == parse::parseExpression("x R y"));
    BOOST_CHECK(em.make_R(x, y) == parse::parseExpression("(x) R (y)"));
}

BOOST_AUTO_TEST_CASE(unary_expressions)
{
    expr::ExprMgr& em
        (expr::ExprMgr::INSTANCE());

    expr::Atom a_x
        ("x");

    expr::Expr_ptr x
        (em.make_identifier(a_x));

    BOOST_CHECK (em.make_next(x) == parse::parseExpression("next(x)"));
    BOOST_CHECK (em.make_neg(x) == parse::parseExpression("- x"));
    BOOST_CHECK (em.make_not(x) == parse::parseExpression("! x"));
    BOOST_CHECK (em.make_bw_not(x) == parse::parseExpression("~ x"));
}


BOOST_AUTO_TEST_CASE(binary_arithmetic_expressions)
{
    expr::ExprMgr& em
        (expr::ExprMgr::INSTANCE());

    expr::Atom a_x
        ("x");
    expr::Atom a_y
        ("y");

    expr::Expr_ptr x
        (em.make_identifier(a_x));
    expr::Expr_ptr y
        (em.make_identifier(a_y));

    BOOST_CHECK(em.make_add(x, y) == parse::parseExpression("x + y"));
    BOOST_CHECK(em.make_mul(x, y) == parse::parseExpression("x * y"));
    BOOST_CHECK(em.make_sub(x, y) == parse::parseExpression("x - y"));
    BOOST_CHECK(em.make_div(x, y) == parse::parseExpression("x / y"));
    BOOST_CHECK(em.make_mod(x, y) == parse::parseExpression("x % y"));
    BOOST_CHECK(em.make_lshift(x, y) == parse::parseExpression("x << y"));
    BOOST_CHECK(em.make_rshift(x, y) == parse::parseExpression("x >> y"));
    BOOST_CHECK(em.make_bw_and(x, y) == parse::parseExpression("x & y"));
    BOOST_CHECK(em.make_bw_or(x, y) == parse::parseExpression("x | y"));
    BOOST_CHECK(em.make_bw_xor(x, y) == parse::parseExpression("x ^ y"));
    BOOST_CHECK(em.make_bw_xnor(x, y) == parse::parseExpression("x <-> y"));
}


BOOST_AUTO_TEST_CASE(binary_boolean_expressions)
{
    expr::ExprMgr& em
        (expr::ExprMgr::INSTANCE());

    expr::Atom a_x
        ("x");
    expr::Atom a_y
        ("y");
    expr::Atom a_w
        ("w");

    expr::Expr_ptr x
        (em.make_identifier(a_x));
    expr::Expr_ptr y
        (em.make_identifier(a_y));
    expr::Expr_ptr w
        (em.make_identifier(a_w));

    BOOST_CHECK(em.make_and(x, y) ==
                parse::parseExpression("x && y"));

    BOOST_CHECK(em.make_and(em.make_and(x, y), w) ==
                parse::parseExpression("x && y && w"));

    BOOST_CHECK(em.make_or(x, y) ==
                parse::parseExpression("x || y"));

    BOOST_CHECK(em.make_or(em.make_or(x, y), w) ==
                parse::parseExpression("x || y || w"));

    BOOST_CHECK(em.make_implies(x, y) ==
                parse::parseExpression("x -> y"));

    BOOST_CHECK(em.make_implies(em.make_implies(x, y), w) ==
                parse::parseExpression("x -> y -> w"));
}

BOOST_AUTO_TEST_CASE(binary_arithmetic_predicates)
{
    expr::ExprMgr& em
        (expr::ExprMgr::INSTANCE());

    expr::Atom a_x
        ("x");
    expr::Atom a_y
        ("y");

    expr::Expr_ptr x
        (em.make_identifier(a_x));
    expr::Expr_ptr y
        (em.make_identifier(a_y));

    BOOST_CHECK(em.make_eq(x, y) == parse::parseExpression("x = y"));
    BOOST_CHECK(em.make_ne(x, y) == parse::parseExpression("x != y"));
    BOOST_CHECK(em.make_le(x, y) == parse::parseExpression("x <= y"));
    BOOST_CHECK(em.make_lt(x, y) == parse::parseExpression("x < y"));
    BOOST_CHECK(em.make_ge(x, y) == parse::parseExpression("x >= y"));
    BOOST_CHECK(em.make_gt(x, y) == parse::parseExpression("x > y"));
}

BOOST_AUTO_TEST_CASE(ternary_operator)
{
    expr::ExprMgr& em
        (expr::ExprMgr::INSTANCE());

    expr::Atom a_x
        ("x");
    expr::Atom a_y
        ("y");
    expr::Atom a_w
        ("w");

    expr::Expr_ptr x
        (em.make_identifier(a_x));
    expr::Expr_ptr y
        (em.make_identifier(a_y));
    expr::Expr_ptr w
        (em.make_identifier(a_w));

    BOOST_CHECK(em.make_ite(em.make_cond(x, y), w) ==
                parse::parseExpression("x ? y : w"));
}

BOOST_AUTO_TEST_CASE(subscript_operator)
{
    expr::ExprMgr& em
        (expr::ExprMgr::INSTANCE());

    expr::Atom a_x
        ("x");
    expr::Expr_ptr x
        (em.make_identifier(a_x));

    BOOST_CHECK(em.make_subscript(x, em.make_const(42)) ==
                parse::parseExpression("x[42]"));
}

BOOST_AUTO_TEST_CASE(operators_precedence)
{
    expr::ExprMgr& em
        (expr::ExprMgr::INSTANCE());

    expr::Atom a_x
        ("x");
    expr::Atom a_y
        ("y");
    expr::Atom a_w
        ("w");

    expr::Expr_ptr x
        (em.make_identifier(a_x));
    expr::Expr_ptr y
        (em.make_identifier(a_y));
    expr::Expr_ptr w
        (em.make_identifier(a_w));

    BOOST_CHECK (em.make_add(x, em.make_mul(y, em.make_const(42))) ==
                 parse::parseExpression("x + y * 42"));

    BOOST_CHECK (em.make_add(x, em.make_neg(y)) ==
                 parse::parseExpression("x + - y"));

    BOOST_CHECK (em.make_bw_or(x, em.make_bw_and(y, em.make_const(42))) ==
                 parse::parseExpression("x | y & 42"));

    BOOST_CHECK (em.make_add(x, em.make_div(y, em.make_const(42))) ==
                 parse::parseExpression("x + y / 42"));

    BOOST_CHECK (em.make_add(x, em.make_mod(y, em.make_const(42))) ==
                 parse::parseExpression("x + y % 42"));

    BOOST_CHECK (em.make_and(em.make_eq( x, em.make_const(0)),
                             em.make_eq( y, em.make_const(1))) ==
                 parse::parseExpression("x = 0 && y = 1"));

    BOOST_CHECK (em.make_or(em.make_eq( x, em.make_const(0)),
                            em.make_eq( y, em.make_const(1))) ==
                 parse::parseExpression("x = 0 || y = 1"));

    BOOST_CHECK (em.make_or( em.make_or( em.make_eq( x, em.make_const(0)),
                                         em.make_and( em.make_eq( y, em.make_const(1)),
                                                      em.make_eq( x, em.make_const(0)))),
                             em.make_eq( y, em.make_const(1))) ==
                 parse::parseExpression("x = 0 || y = 1 && x = 0 || y = 1"));

    BOOST_CHECK (em.make_implies( em.make_eq(x, em.make_const(0)),
                                  em.make_eq(em.make_next(x),
                                              em.make_const(1))) ==
                 parse::parseExpression("x = 0 -> next(x) = 1"));

    BOOST_CHECK (em.make_gt(x, em.make_lshift(y, em.make_const(2))) ==
                 parse::parseExpression("x > y << 2"));

    BOOST_CHECK (em.make_add( em.make_subscript(x, em.make_const(42)),
                                    em.make_subscript(y, em.make_const(0))) ==
                 parse::parseExpression("x[42] + y[0]"));

    BOOST_CHECK (em.make_subscript(x, em.make_sub (y, em.make_const(1))) ==
                 parse::parseExpression("x[y - 1]"));

    BOOST_CHECK (em.make_dot(x, y) ==
                 parse::parseExpression("x.y"));

    BOOST_CHECK (em.make_dot(em.make_dot(x, y), w) ==
                 parse::parseExpression("x.y.w"));

    /* left associativity */
    BOOST_CHECK (em.make_add(em.make_add(x, y), em.make_const(42)) ==
                 parse::parseExpression("x + y + 42"));

    BOOST_CHECK (em.make_mul(em.make_mul(x, y), em.make_const(42)) ==
                 parse::parseExpression("x * y * 42"));

    /* casts */
    BOOST_CHECK (em.make_cast(em.make_unsigned_int_type(16), em.make_add(x, y)) ==
                 parse::parseExpression("(uint16) (x + y)"));

    /* misc */
    BOOST_CHECK (em.make_next(em.make_add(x, y)) ==
                 parse::parseExpression("next(x + y)"));
}

BOOST_AUTO_TEST_CASE(at_expressions)
{
    expr::ExprMgr& em
        (expr::ExprMgr::INSTANCE());

    expr::Atom a_x
        ("x");
    expr::Atom a_y
        ("y");

    expr::Expr_ptr x
        (em.make_identifier(a_x));
    expr::Expr_ptr y
        (em.make_identifier(a_y));

    BOOST_CHECK (em.make_at(em.make_instant(0), x) ==
                 parse::parseExpression("@0{x}"));

    BOOST_CHECK (em.make_at(em.make_instant(UINT_MAX), x) ==
                 parse::parseExpression("$0{x}"));

    BOOST_CHECK (em.make_at(em.make_instant(0), em.make_add(x, y)) ==
                 parse::parseExpression("@0{x + y}"));

    BOOST_CHECK (em.make_at(em.make_instant(UINT_MAX), em.make_add(x, y)) ==
                 parse::parseExpression("$0{x + y}"));

    BOOST_CHECK (em.make_at(em.make_instant(0), em.make_next(x)) ==
                 parse::parseExpression("@0{next(x)}"));

    BOOST_CHECK (em.make_at(em.make_instant(0), em.make_at(em.make_instant(2), x)) ==
                 parse::parseExpression("@0{(@2{x})}"));

    BOOST_CHECK (em.make_at(em.make_interval(em.make_instant(1), em.make_instant(5)), x) ==
                 parse::parseExpression("@1..5{x}"));

    BOOST_CHECK (em.make_at(em.make_interval(em.make_instant(UINT_MAX), em.make_instant(UINT_MAX - 12)), x) ==
                 parse::parseExpression("$0..12{x}"));
}

BOOST_AUTO_TEST_CASE(complex_expressions)
{
    expr::ExprMgr& em
        (expr::ExprMgr::INSTANCE());

    expr::Atom a_x
        ("x");
    expr::Atom a_y
        ("y");

    expr::Expr_ptr x
        (em.make_identifier(a_x));
    expr::Expr_ptr y
        (em.make_identifier(a_y));

    BOOST_CHECK (em.make_implies( em.make_and( em.make_eq(x, em.make_const(0)),
                                               em.make_eq(y, em.make_const(0))),
                                  em.make_or( em.make_ne(em.make_next(x),
                                                         em.make_const(0)),
                                              em.make_ne(em.make_next(y),
                                                         em.make_const(0)))) ==
                 parse::parseExpression("(((x = 0) && (y = 0)) -> ((next(x) != 0) || (next(y) != 0)))"));
}

BOOST_AUTO_TEST_CASE(typedefs)
{
    expr::ExprMgr& em
        (expr::ExprMgr::INSTANCE());

    /* boolean */
    BOOST_CHECK ((em.make_boolean_type()) ==
                 parse::parseTypedef("boolean")->repr());

    /* boolean array */
    BOOST_CHECK (em.make_subscript(em.make_boolean_type(), em.make_const(10)) ==
                 parse::parseTypedef("boolean[10]")->repr());

    /* int */
    BOOST_CHECK(em.make_signed_int_type(8) ==
                parse::parseTypedef("int8")->repr());

    BOOST_CHECK(em.make_signed_int_type(16) ==
                parse::parseTypedef("int16")->repr());

    BOOST_CHECK(em.make_signed_int_type(32) ==
                parse::parseTypedef("int32")->repr());

    BOOST_CHECK(em.make_signed_int_type(64) ==
                parse::parseTypedef("int64")->repr());

    /* int array */
    BOOST_CHECK (em.make_subscript(em.make_signed_int_type(8), em.make_const(10)) ==
                 parse::parseTypedef("int8[10]")->repr());

    BOOST_CHECK (em.make_subscript(em.make_signed_int_type(16), em.make_const(10)) ==
                 parse::parseTypedef("int16[10]")->repr());

    BOOST_CHECK (em.make_subscript(em.make_signed_int_type(32), em.make_const(10)) ==
                 parse::parseTypedef("int32[10]")->repr());

    BOOST_CHECK (em.make_subscript(em.make_signed_int_type(64), em.make_const(10)) ==
                 parse::parseTypedef("int64[10]")->repr());

    /* unsigned int */
    BOOST_CHECK(em.make_unsigned_int_type(8) ==
                parse::parseTypedef("uint8")->repr());

    BOOST_CHECK(em.make_unsigned_int_type(16) ==
                parse::parseTypedef("uint16")->repr());

    BOOST_CHECK(em.make_unsigned_int_type(32) ==
                parse::parseTypedef("uint32")->repr());

    BOOST_CHECK(em.make_unsigned_int_type(64) ==
                parse::parseTypedef("uint64")->repr());

    /* unsigned int array */
    BOOST_CHECK(em.make_subscript(em.make_unsigned_int_type(8),
                                  em.make_const(10)) ==
                parse::parseTypedef("uint8[10]")->repr());

    BOOST_CHECK(em.make_subscript(em.make_unsigned_int_type(16),
                                  em.make_const(10)) ==
                parse::parseTypedef("uint16[10]")->repr());

    BOOST_CHECK(em.make_subscript(em.make_unsigned_int_type(32),
                                  em.make_const(10)) ==
                parse::parseTypedef("uint32[10]")->repr());

    BOOST_CHECK(em.make_subscript(em.make_unsigned_int_type(64),
                                  em.make_const(10)) ==
                parse::parseTypedef("uint64[10]")->repr());
}

BOOST_AUTO_TEST_SUITE_END()

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
#include <printer.hh>

#include <type.hh>

/* from src/parse.cc */
extern Expr_ptr parseExpression(const char *string);
extern Type_ptr parseTypedef(const char *string);

BOOST_AUTO_TEST_SUITE(tests)
BOOST_AUTO_TEST_CASE(parsing_identifiers)
{
    ExprMgr& em
        (ExprMgr::INSTANCE());

    Atom a_x
        ("x");
    Atom a_y
        ("y");

    Expr_ptr x
        (em.make_identifier(a_x));
    Expr_ptr y
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
    ExprMgr& em
        (ExprMgr::INSTANCE());

    Atom a_x
        ("x");
    Atom a_y
        ("y");

    Expr_ptr x
        (em.make_identifier(a_x));
    Expr_ptr y
        (em.make_identifier(a_y));

    BOOST_CHECK (em.make_F(x) == parseExpression("F x"));
    BOOST_CHECK (em.make_F(x) == parseExpression("F(x)"));

    BOOST_CHECK (em.make_G(x) == parseExpression("G x"));
    BOOST_CHECK (em.make_G(x) == parseExpression("G(x)"));

    BOOST_CHECK (em.make_X(x) == parseExpression("X x"));
    BOOST_CHECK (em.make_X(x) == parseExpression("X(x)"));

    BOOST_CHECK (em.make_G(em.make_F(x)) == parseExpression("G F x"));
    BOOST_CHECK (em.make_G(em.make_F(x)) == parseExpression("G(F x)"));
    BOOST_CHECK (em.make_G(em.make_F(x)) == parseExpression("G(F(x))"));

    BOOST_CHECK (em.make_F(em.make_G(x)) == parseExpression("F G x"));
    BOOST_CHECK (em.make_F(em.make_G(x)) == parseExpression("F(G x)"));
    BOOST_CHECK (em.make_F(em.make_G(x)) == parseExpression("F(G(x))"));

    BOOST_CHECK(em.make_U(x, y) == parseExpression("x U y"));
    BOOST_CHECK(em.make_U(x, y) == parseExpression("(x) U (y)"));

    BOOST_CHECK(em.make_R(x, y) == parseExpression("x R y"));
    BOOST_CHECK(em.make_R(x, y) == parseExpression("(x) R (y)"));
}

BOOST_AUTO_TEST_CASE(unary_expressions)
{
    ExprMgr& em
        (ExprMgr::INSTANCE());

    Atom a_x
        ("x");

    Expr_ptr x
        (em.make_identifier(a_x));

    BOOST_CHECK (em.make_next(x) == parseExpression("next(x)"));
    BOOST_CHECK (em.make_neg(x) == parseExpression("- x"));
    BOOST_CHECK (em.make_not(x) == parseExpression("! x"));
    BOOST_CHECK (em.make_bw_not(x) == parseExpression("~ x"));
}


BOOST_AUTO_TEST_CASE(binary_arithmetic_expressions)
{
    ExprMgr& em
        (ExprMgr::INSTANCE());

    Atom a_x
        ("x");
    Atom a_y
        ("y");

    Expr_ptr x
        (em.make_identifier(a_x));
    Expr_ptr y
        (em.make_identifier(a_y));

    BOOST_CHECK(em.make_add(x, y) == parseExpression("x + y"));
    BOOST_CHECK(em.make_mul(x, y) == parseExpression("x * y"));
    BOOST_CHECK(em.make_sub(x, y) == parseExpression("x - y"));
    BOOST_CHECK(em.make_div(x, y) == parseExpression("x / y"));
    BOOST_CHECK(em.make_mod(x, y) == parseExpression("x % y"));
    BOOST_CHECK(em.make_lshift(x, y) == parseExpression("x << y"));
    BOOST_CHECK(em.make_rshift(x, y) == parseExpression("x >> y"));
    BOOST_CHECK(em.make_bw_and(x, y) == parseExpression("x & y"));
    BOOST_CHECK(em.make_bw_or(x, y) == parseExpression("x | y"));
    BOOST_CHECK(em.make_bw_xor(x, y) == parseExpression("x ^ y"));
    BOOST_CHECK(em.make_bw_xnor(x, y) == parseExpression("x <-> y"));
}


BOOST_AUTO_TEST_CASE(binary_boolean_expressions)
{
    ExprMgr& em
        (ExprMgr::INSTANCE());

    Atom a_x
        ("x");
    Atom a_y
        ("y");
    Atom a_w
        ("w");

    Expr_ptr x
        (em.make_identifier(a_x));
    Expr_ptr y
        (em.make_identifier(a_y));
    Expr_ptr w
        (em.make_identifier(a_w));

    BOOST_CHECK(em.make_and(x, y) ==
                parseExpression("x && y"));

    BOOST_CHECK(em.make_and(em.make_and(x, y), w) ==
                parseExpression("x && y && w"));

    BOOST_CHECK(em.make_or(x, y) ==
                parseExpression("x || y"));

    BOOST_CHECK(em.make_or(em.make_or(x, y), w) ==
                parseExpression("x || y || w"));

    BOOST_CHECK(em.make_implies(x, y) ==
                parseExpression("x -> y"));

    BOOST_CHECK(em.make_implies(em.make_implies(x, y), w) ==
                parseExpression("x -> y -> w"));
}

BOOST_AUTO_TEST_CASE(binary_arithmetic_predicates)
{
    ExprMgr& em
        (ExprMgr::INSTANCE());

    Atom a_x
        ("x");
    Atom a_y
        ("y");

    Expr_ptr x
        (em.make_identifier(a_x));
    Expr_ptr y
        (em.make_identifier(a_y));

    BOOST_CHECK(em.make_eq(x, y) == parseExpression("x = y"));
    BOOST_CHECK(em.make_ne(x, y) == parseExpression("x != y"));
    BOOST_CHECK(em.make_le(x, y) == parseExpression("x <= y"));
    BOOST_CHECK(em.make_lt(x, y) == parseExpression("x < y"));
    BOOST_CHECK(em.make_ge(x, y) == parseExpression("x >= y"));
    BOOST_CHECK(em.make_gt(x, y) == parseExpression("x > y"));
}

BOOST_AUTO_TEST_CASE(ternary_operator)
{
    ExprMgr& em
        (ExprMgr::INSTANCE());

    Atom a_x
        ("x");
    Atom a_y
        ("y");
    Atom a_w
        ("w");

    Expr_ptr x
        (em.make_identifier(a_x));
    Expr_ptr y
        (em.make_identifier(a_y));
    Expr_ptr w
        (em.make_identifier(a_w));

    BOOST_CHECK(em.make_ite(em.make_cond(x, y), w) ==
                parseExpression("x ? y : w"));
}

BOOST_AUTO_TEST_CASE(subscript_operator)
{
    ExprMgr& em
        (ExprMgr::INSTANCE());

    Atom a_x
        ("x");
    Expr_ptr x
        (em.make_identifier(a_x));

    BOOST_CHECK(em.make_subscript(x, em.make_const(42)) ==
                parseExpression("x[42]"));
}

BOOST_AUTO_TEST_CASE(operators_precedence)
{
    ExprMgr& em
        (ExprMgr::INSTANCE());

    Atom a_x
        ("x");
    Atom a_y
        ("y");
    Atom a_w
        ("w");

    Expr_ptr x
        (em.make_identifier(a_x));
    Expr_ptr y
        (em.make_identifier(a_y));
    Expr_ptr w
        (em.make_identifier(a_w));

    BOOST_CHECK (em.make_add(x, em.make_mul(y, em.make_const(42))) ==
                 parseExpression("x + y * 42"));

    BOOST_CHECK (em.make_add(x, em.make_neg(y)) ==
                 parseExpression("x + - y"));

    BOOST_CHECK (em.make_bw_or(x, em.make_bw_and(y, em.make_const(42))) ==
                 parseExpression("x | y & 42"));

    BOOST_CHECK (em.make_add(x, em.make_div(y, em.make_const(42))) ==
                 parseExpression("x + y / 42"));

    BOOST_CHECK (em.make_add(x, em.make_mod(y, em.make_const(42))) ==
                 parseExpression("x + y % 42"));

    BOOST_CHECK (em.make_and(em.make_eq( x, em.make_const(0)),
                             em.make_eq( y, em.make_const(1))) ==
                 parseExpression("x = 0 && y = 1"));

    BOOST_CHECK (em.make_or(em.make_eq( x, em.make_const(0)),
                            em.make_eq( y, em.make_const(1))) ==
                 parseExpression("x = 0 || y = 1"));

    BOOST_CHECK (em.make_or( em.make_or( em.make_eq( x, em.make_const(0)),
                                         em.make_and( em.make_eq( y, em.make_const(1)),
                                                      em.make_eq( x, em.make_const(0)))),
                             em.make_eq( y, em.make_const(1))) ==
                 parseExpression("x = 0 || y = 1 && x = 0 || y = 1"));

    BOOST_CHECK (em.make_implies( em.make_eq(x, em.make_const(0)),
                                  em.make_eq(em.make_next(x),
                                              em.make_const(1))) ==
                 parseExpression("x = 0 -> next(x) = 1"));

    BOOST_CHECK (em.make_gt(x, em.make_lshift(y, em.make_const(2))) ==
                 parseExpression("x > y << 2"));

    BOOST_CHECK (em.make_add( em.make_subscript(x, em.make_const(42)),
                                    em.make_subscript(y, em.make_const(0))) ==
                 parseExpression("x[42] + y[0]"));

    BOOST_CHECK (em.make_subscript(x, em.make_sub (y, em.make_const(1))) ==
                 parseExpression("x[y - 1]"));

    BOOST_CHECK (em.make_dot(x, y) ==
                 parseExpression("x.y"));

    BOOST_CHECK (em.make_dot(em.make_dot(x, y), w) ==
                 parseExpression("x.y.w"));

    /* left associativity */
    BOOST_CHECK (em.make_add(em.make_add(x, y), em.make_const(42)) ==
                 parseExpression("x + y + 42"));

    BOOST_CHECK (em.make_mul(em.make_mul(x, y), em.make_const(42)) ==
                 parseExpression("x * y * 42"));

    /* casts */
    BOOST_CHECK (em.make_cast(em.make_unsigned_int_type(16), em.make_add(x, y)) ==
                 parseExpression("(uint16) (x + y)"));

    /* misc */
    BOOST_CHECK (em.make_next(em.make_add(x, y)) ==
                 parseExpression("next(x + y)"));
}

BOOST_AUTO_TEST_CASE(at_expressions)
{
    ExprMgr& em
        (ExprMgr::INSTANCE());

    Atom a_x
        ("x");
    Atom a_y
        ("y");

    Expr_ptr x
        (em.make_identifier(a_x));
    Expr_ptr y
        (em.make_identifier(a_y));

    BOOST_CHECK (em.make_at(em.make_instant(0), x) ==
                 parseExpression("@0{x}"));

    BOOST_CHECK (em.make_at(em.make_instant(0), em.make_add(x, y)) ==
                 parseExpression("@0{x + y}"));

    BOOST_CHECK (em.make_at(em.make_instant(0), em.make_next(x)) ==
                 parseExpression("@0{next(x)}"));

    BOOST_CHECK (em.make_at(em.make_instant(0), em.make_at(em.make_instant(2), x)) ==
                 parseExpression("@0{(@2{x})}"));
}

BOOST_AUTO_TEST_CASE(complex_expressions)
{
    ExprMgr& em
        (ExprMgr::INSTANCE());

    Atom a_x
        ("x");
    Atom a_y
        ("y");

    Expr_ptr x
        (em.make_identifier(a_x));
    Expr_ptr y
        (em.make_identifier(a_y));

    BOOST_CHECK (em.make_implies( em.make_and( em.make_eq(x, em.make_const(0)),
                                               em.make_eq(y, em.make_const(0))),
                                  em.make_or( em.make_ne(em.make_next(x),
                                                         em.make_const(0)),
                                              em.make_ne(em.make_next(y),
                                                         em.make_const(0)))) ==
                 parseExpression("(((x = 0) && (y = 0)) -> ((next(x) != 0) || (next(y) != 0)))"));
}

BOOST_AUTO_TEST_CASE(typedefs)
{
    ExprMgr& em
        (ExprMgr::INSTANCE());

    /* boolean */
    BOOST_CHECK ((em.make_boolean_type()) ==
                 parseTypedef("boolean")->repr());

    /* boolean array */
    BOOST_CHECK (em.make_subscript(em.make_boolean_type(), em.make_const(10)) ==
                 parseTypedef("boolean[10]")->repr());

    /* int */
    BOOST_CHECK(em.make_signed_int_type(8) ==
                parseTypedef("int8")->repr());

    BOOST_CHECK(em.make_signed_int_type(16) ==
                parseTypedef("int16")->repr());

    BOOST_CHECK(em.make_signed_int_type(32) ==
                parseTypedef("int32")->repr());

    BOOST_CHECK(em.make_signed_int_type(64) ==
                parseTypedef("int64")->repr());

    /* int array */
    BOOST_CHECK (em.make_subscript(em.make_signed_int_type(8), em.make_const(10)) ==
                 parseTypedef("int8[10]")->repr());

    BOOST_CHECK (em.make_subscript(em.make_signed_int_type(16), em.make_const(10)) ==
                 parseTypedef("int16[10]")->repr());

    BOOST_CHECK (em.make_subscript(em.make_signed_int_type(32), em.make_const(10)) ==
                 parseTypedef("int32[10]")->repr());

    BOOST_CHECK (em.make_subscript(em.make_signed_int_type(64), em.make_const(10)) ==
                 parseTypedef("int64[10]")->repr());

    /* unsigned int */
    BOOST_CHECK(em.make_unsigned_int_type(8) ==
                parseTypedef("uint8")->repr());

    BOOST_CHECK(em.make_unsigned_int_type(16) ==
                parseTypedef("uint16")->repr());

    BOOST_CHECK(em.make_unsigned_int_type(32) ==
                parseTypedef("uint32")->repr());

    BOOST_CHECK(em.make_unsigned_int_type(64) ==
                parseTypedef("uint64")->repr());

    /* unsigned int array */
    BOOST_CHECK(em.make_subscript(em.make_unsigned_int_type(8),
                                  em.make_const(10)) ==
                parseTypedef("uint8[10]")->repr());

    BOOST_CHECK(em.make_subscript(em.make_unsigned_int_type(16),
                                  em.make_const(10)) ==
                parseTypedef("uint16[10]")->repr());

    BOOST_CHECK(em.make_subscript(em.make_unsigned_int_type(32),
                                  em.make_const(10)) ==
                parseTypedef("uint32[10]")->repr());

    BOOST_CHECK(em.make_subscript(em.make_unsigned_int_type(64),
                                  em.make_const(10)) ==
                parseTypedef("uint64[10]")->repr());
}

BOOST_AUTO_TEST_SUITE_END()

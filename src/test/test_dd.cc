/**
 * @file test_dd.cc
 * @brief DD subsystem unit tests.
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
#include <expr/printer/printer.hh>

#include <type/type.hh>
#include <type/type_mgr.hh>

#include <cuddObj.hh>

BOOST_AUTO_TEST_SUITE(tests)

BOOST_AUTO_TEST_CASE(dd_boolean)
{
    Cudd dd;

    ADD lhs { dd.addVar() };
    ADD rhs { dd.addVar() };
    ADD zero { dd.addZero() };
    ADD one { dd.addOne() };

    /* ! 0 == 1 */
    BOOST_CHECK(zero.Cmpl() == one);

    /* ! 1 == 0 */
    BOOST_CHECK(one.Cmpl() == zero);

    /* !! x == x */
    BOOST_CHECK(lhs.Cmpl().Cmpl() == lhs);

    /* x && 0 == 0 */
    BOOST_CHECK(lhs.Times(zero) == zero);

    /* x && 1 == x */
    BOOST_CHECK(lhs.Times(one) == lhs);

    /* 0 && y == 0 */
    BOOST_CHECK(zero.Times(rhs) == zero);

    /* 1 && y == y */
    BOOST_CHECK(one.Times(rhs) == rhs);

    /* x || y == y || x */
    BOOST_CHECK(lhs.Or(rhs) == rhs.Or(lhs));

    /* x ^ x == 0 */
    BOOST_CHECK(lhs.Xor(lhs) == zero);

    /* x ^ (! x) == 1 */
    BOOST_CHECK(lhs.Xor(lhs.Cmpl()) == one);

    /* x ^ y == y ^ x */
    BOOST_CHECK(lhs.Xor(rhs) == rhs.Xor(lhs));

    /* x <-> x == 1 */
    BOOST_CHECK(lhs.Xnor(lhs) == one);

    /* x <-> (! x) == 0 */
    BOOST_CHECK(lhs.Xnor(lhs.Cmpl()) == zero);

    /* x = y <-> (! x || y) && (! y || x) */
    BOOST_CHECK(lhs.Equals(rhs) ==
                lhs.Cmpl().Or(rhs).Times(rhs.Cmpl().Or(lhs)));
}

// duplicate code... :-/
ADD make_integer_encoding(Cudd& mgr, unsigned nbits, bool is_signed)
{
    bool msb { true };
    ADD res { mgr.addOne() };

    assert(0 < nbits);
    unsigned i;

    i = 0;
    while (i < nbits) {
        ADD two { mgr.constant(2) };
        if (msb && is_signed) {
            msb = false;
            two = two.Negate(); // MSB is -2^N in 2's complement
        }
        res *= two;

        // create var and book it
        ADD add_var = mgr.addVar();

        // add it to the encoding
        res += add_var;

        ++i;
    }

    return res;
}


BOOST_AUTO_TEST_CASE(dd_arithmetic)
{
    Cudd dd;

    ADD lhs { make_integer_encoding(dd, 4, false) };
    ADD rhs { make_integer_encoding(dd, 4, false) };

    BOOST_CHECK(lhs == lhs.Negate().Negate());

    {
        ADD x_plus_y = lhs.Plus(rhs);
        ADD y_plus_x = rhs.Plus(lhs);
        BOOST_CHECK(x_plus_y == y_plus_x);
    }

    {
        ADD x_times_y = lhs.Times(rhs);
        ADD y_times_x = rhs.Times(lhs);
        BOOST_CHECK(x_times_y == y_times_x);
    }

    {
        ADD x_minus_y = lhs.Minus(rhs);
        ADD y_minus_x = rhs.Minus(lhs);
        BOOST_CHECK(x_minus_y != y_minus_x);
    }

    {
        ADD x_divide_y = lhs.Divide(rhs);
        ADD y_divide_x = rhs.Divide(lhs);
        BOOST_CHECK(x_divide_y != y_divide_x);
    }

    {
        ADD x_mod_y = lhs.Modulus(rhs);
        ADD y_mod_x = rhs.Modulus(lhs);
        BOOST_CHECK(x_mod_y != y_mod_x);
    }
}

BOOST_AUTO_TEST_CASE(dd_bitwise)
{
    Cudd dd;
    ADD lhs { dd.addVar() };
    ADD rhs { dd.addVar() };

    {
        ADD neg_neg = lhs.Cmpl().Cmpl();
        BOOST_CHECK(lhs == neg_neg);
    }

    {
        ADD x_and_y = lhs.BWTimes(rhs);
        ADD y_and_x = rhs.BWTimes(lhs);
        BOOST_CHECK(x_and_y == y_and_x);
    }

    {
        ADD x_or_y = lhs.BWOr(rhs);
        ADD y_or_x = rhs.BWOr(lhs);
        BOOST_CHECK(x_or_y == y_or_x);
    }

    {
        ADD x_xor_y = lhs.BWXor(rhs);
        ADD y_xor_x = rhs.BWXor(lhs);
        BOOST_CHECK(x_xor_y == y_xor_x);
    }

    {
        ADD x_xnor_y = lhs.BWXnor(rhs);
        ADD y_xnor_x = rhs.BWXnor(lhs);
        BOOST_CHECK(x_xnor_y == y_xnor_x);
    }

    {
        ADD x_xnor_y = lhs.BWXnor(rhs);
        ADD y_xnor_x = rhs.BWXnor(lhs);
        BOOST_CHECK(x_xnor_y == y_xnor_x);
    }
}

BOOST_AUTO_TEST_CASE(dd_relational)
{
    Cudd dd;

    ADD lhs { make_integer_encoding(dd, 4, false) };
    ADD rhs { make_integer_encoding(dd, 4, false) };

    ADD x_equals_y { lhs.Equals(rhs) };
    ADD y_equals_x { rhs.Equals(lhs) };
    BOOST_CHECK(x_equals_y == y_equals_x);

    ADD x_lt_y { lhs.LT(rhs) };
    ADD y_lt_x { rhs.LT(lhs) };
    BOOST_CHECK(x_lt_y != y_lt_x);

    BOOST_CHECK(x_equals_y.Or(x_lt_y) == lhs.LEQ(rhs));
}

BOOST_AUTO_TEST_SUITE_END()

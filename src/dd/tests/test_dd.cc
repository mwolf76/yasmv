#define BOOST_TEST_DYN_LINK
#include <boost/test/unit_test.hpp>

#include <expr.hh>
#include <expr_mgr.hh>
#include <expr_printer.hh>

#include <type.hh>
#include <type_mgr.hh>

#include <cuddObj.hh>

BOOST_AUTO_TEST_SUITE(tests)

BOOST_AUTO_TEST_CASE(dd_boolean)
{
    Cudd dd;
    ADD lhs = dd.addVar();
    ADD rhs = dd.addVar();

    {
        ADD neg_neg = lhs.Cmpl().Cmpl();
        BOOST_CHECK(lhs == neg_neg);
    }

    {
        ADD x_and_y = lhs.Times(rhs);
        ADD y_and_x = rhs.Times(lhs);
        BOOST_CHECK(x_and_y == y_and_x);
    }

    {
        ADD x_or_y = lhs.Or(rhs);
        ADD y_or_x = rhs.Or(lhs);
        BOOST_CHECK(x_or_y == y_or_x);
    }

    {
        ADD x_xor_y = lhs.Xor(rhs);
        ADD y_xor_x = rhs.Xor(lhs);
        BOOST_CHECK(x_xor_y == y_xor_x);
    }

    {
        ADD x_xnor_y = lhs.Xnor(rhs);
        ADD y_xnor_x = rhs.Xnor(lhs);
        BOOST_CHECK(x_xnor_y == y_xnor_x);
    }

    {
        ADD x_xnor_y = lhs.Xnor(rhs);
        ADD y_xnor_x = rhs.Xnor(lhs);
        BOOST_CHECK(x_xnor_y == y_xnor_x);
    }

    {
        ADD x_xnor_y = lhs.Xnor(rhs);
        ADD y_xnor_x = rhs.Xor(lhs).Cmpl();
        BOOST_CHECK(x_xnor_y == y_xnor_x);
    }
}

// duplicate code... :-/
ADD make_integer_encoding(Cudd& mgr, unsigned nbits, bool is_signed)
{
    bool msb = true;

    ADD res = mgr.addOne();

    assert(0 < nbits);
    unsigned i = 0;

    while (i < nbits) {
        ADD two = mgr.constant(2);
        if (msb && is_signed) {
            msb = false;
            two = two.Negate(); // MSB is -2^N in 2's complement
        }
        res *= two;

        // create var and book it
        ADD add_var = mgr.addVar();

        // add it to the encoding
        res += add_var;

        ++ i;
    }

    return res;
}


BOOST_AUTO_TEST_CASE(dd_arithmetic)
{
    Cudd dd;

    ADD lhs = make_integer_encoding(dd, 4, false);
    ADD rhs = make_integer_encoding(dd, 4, false);

    {
        ADD neg_neg = lhs.Negate().Negate();
        BOOST_CHECK(lhs == neg_neg);
    }

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
        ADD x_times_y = lhs.Times(rhs);
        ADD y_times_x = rhs.Times(lhs);
        BOOST_CHECK(x_times_y == y_times_x);
    }


}


BOOST_AUTO_TEST_SUITE_END()

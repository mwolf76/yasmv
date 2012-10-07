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

BOOST_AUTO_TEST_SUITE_END()

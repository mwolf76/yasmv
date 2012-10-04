#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE ExprSuite
#include <boost/test/unit_test.hpp>

#include <expr.hh>
#include <expr_mgr.hh>

BOOST_AUTO_TEST_SUITE(makers)

BOOST_AUTO_TEST_CASE(leaves)
{
    Atom x("x");
    Expr expr(x);

    BOOST_CHECK(expr.is_atom());
    BOOST_CHECK(expr.atom() == &x);
}
BOOST_AUTO_TEST_SUITE_END()

// BOOST_AUTO_TEST_SUITE(Physics)

// BOOST_AUTO_TEST_CASE(specialTheory)
// {
//     int e = 32;
//     int m = 2;
//     int c = 4;

//     BOOST_CHECK(e == m * c * c);
// }

// BOOST_AUTO_TEST_SUITE_END()

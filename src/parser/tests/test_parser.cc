#define BOOST_TEST_DYN_LINK
#include <boost/test/unit_test.hpp>

#include <expr.hh>
#include <expr_mgr.hh>
#include <expr_printer.hh>

/* from src/parse.cc */
extern Expr_ptr parseString(const char *string);

BOOST_AUTO_TEST_SUITE(tests)
BOOST_AUTO_TEST_CASE(grammar)
{
    ExprMgr& em(ExprMgr::INSTANCE());

    Atom a_x("x");
    Atom a_y("y");

    Expr_ptr x = em.make_identifier(a_x);
    Expr_ptr y = em.make_identifier(a_y);

    // primary makers
    {
        Expr_ptr phi = em.make_add(x, y);
        Expr_ptr psi = parseString("x + y");

        BOOST_CHECK (phi == psi);
    }
}

BOOST_AUTO_TEST_SUITE_END()

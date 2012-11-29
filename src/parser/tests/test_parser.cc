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
    BOOST_CHECK ( x != y );

    // test identifiers canonicity
    BOOST_CHECK( x == em.make_identifier(a_x));
    BOOST_CHECK( y == em.make_identifier(a_y));

    // test basic exprs

    {
        Expr_ptr phi = em.make_next(x);
        Expr_ptr psi = parseString("next(x)");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_neg(x);
        Expr_ptr psi = parseString("- x");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_not(x);
        Expr_ptr psi = parseString("! x");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_add(x, y);
        Expr_ptr psi = parseString("x + y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_mul(x, y);
        Expr_ptr psi = parseString("x * y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_sub(x, y);
        Expr_ptr psi = parseString("x - y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_div(x, y);
        Expr_ptr psi = parseString("x / y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_and(x, y);
        Expr_ptr psi = parseString("x & y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_or(x, y);
        Expr_ptr psi = parseString("x | y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_xor(x, y);
        Expr_ptr psi = parseString("x xor y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_xnor(x, y);
        Expr_ptr psi = parseString("x xnor y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_implies(x, y);
        Expr_ptr psi = parseString("x -> y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_iff(x, y);
        Expr_ptr psi = parseString("x <-> y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_lshift(x, y);
        Expr_ptr psi = parseString("x << y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_rshift(x, y);
        Expr_ptr psi = parseString("x >> y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_le(x, y);
        Expr_ptr psi = parseString("x <= y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_eq(x, y);
        Expr_ptr psi = parseString("x = y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_ne(x, y);
        Expr_ptr psi = parseString("x != y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_lt(x, y);
        Expr_ptr psi = parseString("x < y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_ge(x, y);
        Expr_ptr psi = parseString("x >= y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_gt(x, y);
        Expr_ptr psi = parseString("x > y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_ite(em.make_cond(x, y), em.make_iconst(42));
        Expr_ptr psi = parseString("x ? y : 42");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_ite(em.make_cond(x, y), em.make_iconst(42));
        Expr_ptr psi = parseString("x ? y : 42");
        BOOST_CHECK (phi == psi);
    }

}

BOOST_AUTO_TEST_SUITE_END()

#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE test_expr
#include <boost/test/unit_test.hpp>

#include <expr.hh>
#include <expr_mgr.hh>
#include <expr_printer.hh>

BOOST_AUTO_TEST_SUITE(expr)

BOOST_AUTO_TEST_CASE(atoms)
{
    Atom x("x");
    Expr expr(x);

    BOOST_CHECK(expr.is_atom());
    BOOST_CHECK(expr.atom() == &x);
}

BOOST_AUTO_TEST_CASE(consts)
{
    // TODO: think about size
}

BOOST_AUTO_TEST_CASE(makers)
{
    ExprMgr& em(ExprMgr::INSTANCE());
    Atom x("x");

    Expr_ptr id = em.make_identifier(x);

    // LTL
    Expr_ptr Fid = em.make_F(id);
}

/* printer */
BOOST_AUTO_TEST_CASE(atoms_printer)
{
    Atom x("x");
    Expr expr(x);

    ostringstream oss;
    Printer printer(oss);

    printer << expr;
    BOOST_CHECK(oss.str() == "x");
}

BOOST_AUTO_TEST_CASE(consts_printer)
{
    ExprMgr& em = ExprMgr::INSTANCE();
    Expr_ptr k = em.make_iconst(42);

    ostringstream oss;
    Printer printer(oss);

    printer << k;
    BOOST_CHECK(oss.str() == "42");
}

BOOST_AUTO_TEST_SUITE_END()

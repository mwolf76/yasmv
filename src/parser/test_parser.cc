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
BOOST_AUTO_TEST_CASE(basic_parsing)
{
    ExprMgr& em(ExprMgr::INSTANCE());

    Atom a_x("x");
    Atom a_y("y");
    Atom a_w("w");

    Expr_ptr x = em.make_identifier(a_x);
    Expr_ptr y = em.make_identifier(a_y);
    Expr_ptr w = em.make_identifier(a_w);
    BOOST_CHECK ( x != y );

    // test identifiers canonicity
    BOOST_CHECK( x == em.make_identifier(a_x));
    BOOST_CHECK( y == em.make_identifier(a_y));

    // test LTL basic exprs
    {
        Expr_ptr phi = em.make_F(x);
        Expr_ptr psi = parseExpression("F x");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_G(x);
        Expr_ptr psi = parseExpression("G x");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_X(x);
        Expr_ptr psi = parseExpression("X x");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_U(x, y);
        Expr_ptr psi = parseExpression("x U y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_R(x, y);
        Expr_ptr psi = parseExpression("x R y");
        BOOST_CHECK (phi == psi);
    }

    // a few more LTL tests
    {
        Expr_ptr phi = em.make_G( em.make_F(x));
        Expr_ptr psi = parseExpression("G F x");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_G( em.make_F(x));
        Expr_ptr psi = parseExpression("G (F x)");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_G( em.make_F(x));
        Expr_ptr psi = parseExpression("G (F (x))");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_F( em.make_G(x));
        Expr_ptr psi = parseExpression("F G x");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_F( em.make_G(x));
        Expr_ptr psi = parseExpression("F (G x)");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_F( em.make_G(x));
        Expr_ptr psi = parseExpression("F G (x)");
        BOOST_CHECK (phi == psi);
    }

    // test basic exprs
    {
        Expr_ptr phi = em.make_next(x);
        Expr_ptr psi = parseExpression("next(x)");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_neg(x);
        Expr_ptr psi = parseExpression("- x");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_not(x);
        Expr_ptr psi = parseExpression("! x");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_bw_not(x);
        Expr_ptr psi = parseExpression("~ x");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_add(x, y);
        Expr_ptr psi = parseExpression("x + y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_mul(x, y);
        Expr_ptr psi = parseExpression("x * y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_sub(x, y);
        Expr_ptr psi = parseExpression("x - y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_div(x, y);
        Expr_ptr psi = parseExpression("x / y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_and(x, y);
        Expr_ptr psi = parseExpression("x && y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_bw_and(x, y);
        Expr_ptr psi = parseExpression("x & y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_or(x, y);
        Expr_ptr psi = parseExpression("x || y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_bw_or(x, y);
        Expr_ptr psi = parseExpression("x | y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_bw_xor(x, y);
        Expr_ptr psi = parseExpression("x ^ y");
        BOOST_CHECK (phi == psi);
    }

    // {
    //     Expr_ptr phi = em.make_bw_xnor(x, y);
    //     Expr_ptr psi = parseExpression("x !^ y");
    //     BOOST_CHECK (phi == psi);
    // }

    {
        Expr_ptr phi = em.make_implies(x, y);
        Expr_ptr psi = parseExpression("x -> y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_lshift(x, y);
        Expr_ptr psi = parseExpression("x << y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_rshift(x, y);
        Expr_ptr psi = parseExpression("x >> y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_le(x, y);
        Expr_ptr psi = parseExpression("x <= y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_eq(x, y);
        Expr_ptr psi = parseExpression("x = y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_ne(x, y);
        Expr_ptr psi = parseExpression("x != y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_lt(x, y);
        Expr_ptr psi = parseExpression("x < y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_ge(x, y);
        Expr_ptr psi = parseExpression("x >= y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_gt(x, y);
        Expr_ptr psi = parseExpression("x > y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_ite(em.make_cond(x, y), em.make_const(42));
        Expr_ptr psi = parseExpression("x ? y : 42");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_ite(em.make_cond(x, y), em.make_const(42));
        Expr_ptr psi = parseExpression("x ? y : 42");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_subscript(x, em.make_const(42));
        Expr_ptr psi = parseExpression("x[42]");
        BOOST_CHECK (phi == psi);
    }

    /* operators precedence */
    {
        Expr_ptr phi = em.make_add(x, em.make_mul(y, em.make_const(42)));
        Expr_ptr psi = parseExpression("x + y * 42");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_add(x, em.make_neg(y));
        Expr_ptr psi = parseExpression("x + - y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_bw_or(x, em.make_bw_and(y, em.make_const(42)));
        Expr_ptr psi = parseExpression("x | y & 42");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_add(x, em.make_div(y, em.make_const(42)));
        Expr_ptr psi = parseExpression("x + y / 42");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_add(x, em.make_mod(y, em.make_const(42)));
        Expr_ptr psi = parseExpression("x + y % 42");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_and(em.make_eq( x, em.make_const(0)),
                                   em.make_eq( y, em.make_const(1)));
        Expr_ptr psi = parseExpression("x = 0 && y = 1");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_or(em.make_eq( x, em.make_const(0)),
                                  em.make_eq( y, em.make_const(1)));
        Expr_ptr psi = parseExpression("x = 0 || y = 1");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr psi = parseExpression("x = 0 || y = 1 && x = 0 || y = 1");
        (void) psi;
        // std::cerr << psi << std::endl;
        // BOOST_CHECK (phi == psi);
    }


    {
        Expr_ptr phi = em.make_implies(em.make_eq( x, em.make_const(0)),
                                       em.make_eq( em.make_next(x),
                                                   em.make_const(1)));
        Expr_ptr psi = parseExpression("x = 0 -> next(x) = 1");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_gt(x, em.make_lshift(y,
                                                    em.make_const(2)));
        Expr_ptr psi = parseExpression("x > y << 2");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_add( em.make_subscript(x, em.make_const(42)),
                                    em.make_subscript(y, em.make_const(0)));
        Expr_ptr psi = parseExpression("x[42] + y[0]");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_subscript(x, em.make_sub (y,
                                                         em.make_const(1)));

        Expr_ptr psi = parseExpression("x[y - 1]");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_dot(x, y);
        Expr_ptr psi = parseExpression("x.y");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_dot(em.make_dot(x, y), w);
        Expr_ptr psi = parseExpression("x.y.w");
        BOOST_CHECK (phi == psi);
    }

    /* left associativity */
    {
        Expr_ptr phi = em.make_add(em.make_add(x, y),
                                   em.make_const(42));
        Expr_ptr psi = parseExpression("x + y + 42");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_mul(em.make_mul(x, y), em.make_const(42));
        Expr_ptr psi = parseExpression("x * y * 42");
        BOOST_CHECK (phi == psi);
    }

    /* casts */
    {
        Expr_ptr phi = em.make_cast(em.make_unsigned_int_type(16),
                                    em.make_add(x, y));
        Expr_ptr psi = parseExpression("(uint16) (x + y)");
        BOOST_CHECK (phi == psi);
    }

    /* misc */
    {
        Expr_ptr phi = em.make_next(em.make_add(x, y));
        Expr_ptr psi = parseExpression("next(x + y)");
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_implies( em.make_and( em.make_eq(x, em.make_const(0)),
                                                     em.make_eq(y, em.make_const(0))),
                                        em.make_or( em.make_ne(em.make_next(x),
                                                               em.make_const(0)),
                                                    em.make_ne(em.make_next(y),
                                                               em.make_const(0))));
        Expr_ptr psi =
            parseExpression("(((x = 0) && (y = 0)) -> ((next(x) != 0) || (next(y) != 0)))");
        BOOST_CHECK (phi == psi);
    }
}

BOOST_AUTO_TEST_CASE(typedefs)
{
    ExprMgr& em(ExprMgr::INSTANCE());

    {
       Expr_ptr phi = em.make_boolean_type();

        Type_ptr tp = parseTypedef("boolean");
        BOOST_CHECK(tp);

        Expr_ptr psi (tp -> repr());
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_subscript(em.make_boolean_type(),
                                         em.make_const(10));

        Type_ptr tp = parseTypedef("boolean[10]");
        BOOST_CHECK(tp);

        Expr_ptr psi (tp -> repr());
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_signed_int_type(8);

        Type_ptr tp = parseTypedef("int8");
        BOOST_CHECK(tp);

        Expr_ptr psi (tp -> repr());
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_subscript(em.make_signed_int_type(8),
                                         em.make_const(10));

        Type_ptr tp = parseTypedef("int8[10]");
        BOOST_CHECK(tp);

        Expr_ptr psi (tp -> repr());
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_unsigned_int_type(8);

        Type_ptr tp = parseTypedef("uint8");
        BOOST_CHECK(tp);

        Expr_ptr psi = (tp -> repr());
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_subscript(em.make_unsigned_int_type(8),
                                         em.make_const(10));

        Type_ptr tp = parseTypedef("uint8[10]");
        BOOST_CHECK(tp);

        Expr_ptr psi = (tp -> repr());
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_signed_int_type(16);

        Type_ptr tp = parseTypedef("int16");
        BOOST_CHECK(tp);

        Expr_ptr psi = (tp -> repr());
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_subscript(em.make_signed_int_type(16),
                                         em.make_const(10));

        Type_ptr tp = parseTypedef("int16[10]");
        BOOST_CHECK(tp);

        Expr_ptr psi = (tp -> repr());
        BOOST_CHECK (phi == psi);
    }


    {
        Expr_ptr phi = em.make_unsigned_int_type(16);

        Type_ptr tp = parseTypedef("uint16");
        BOOST_CHECK(tp);

        Expr_ptr psi = (tp -> repr());
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_subscript(em.make_unsigned_int_type(16),
                                         em.make_const(10));

        Type_ptr tp = parseTypedef("uint16[10]");
        BOOST_CHECK(tp);

        Expr_ptr psi = (tp -> repr());
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_signed_int_type(32);

        Type_ptr tp = parseTypedef("int32");
        BOOST_CHECK(tp);

        Expr_ptr psi = (tp -> repr());
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_subscript(em.make_signed_int_type(32),
                                         em.make_const(10));

        Type_ptr tp = parseTypedef("int32[10]");
        BOOST_CHECK(tp);

        Expr_ptr psi = (tp -> repr());
        BOOST_CHECK (phi == psi);
    }


    {
        Expr_ptr phi = em.make_unsigned_int_type(32);

        Type_ptr tp = parseTypedef("uint32");
        BOOST_CHECK(tp);

        Expr_ptr psi = (tp -> repr());
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_subscript(em.make_unsigned_int_type(32),
                                         em.make_const(10));

        Type_ptr tp = parseTypedef("uint32[10]");
        BOOST_CHECK(tp);

        Expr_ptr psi = (tp -> repr());
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_signed_int_type(32);

        Type_ptr tp = parseTypedef("int32");
        BOOST_CHECK(tp);

        Expr_ptr psi = (tp -> repr());
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_subscript(em.make_signed_int_type(32),
                                         em.make_const(10));

        Type_ptr tp = parseTypedef("int32[10]");
        BOOST_CHECK(tp);

        Expr_ptr psi = (tp -> repr());
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_signed_int_type(64);

        Type_ptr tp = parseTypedef("int64");
        BOOST_CHECK(tp);

        Expr_ptr psi = (tp -> repr());
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_subscript(em.make_signed_int_type(64),
                                         em.make_const(10));

        Type_ptr tp = parseTypedef("int64[10]");
        BOOST_CHECK(tp);

        Expr_ptr psi = (tp -> repr());
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_unsigned_int_type(64);

        Type_ptr tp = parseTypedef("uint64");
        BOOST_CHECK(tp);

        Expr_ptr psi = (tp -> repr());
        BOOST_CHECK (phi == psi);
    }

    {
        Expr_ptr phi = em.make_subscript(em.make_unsigned_int_type(64),
                                         em.make_const(10));

        Type_ptr tp = parseTypedef("uint64[10]");
        BOOST_CHECK(tp);

        Expr_ptr psi = (tp -> repr());
        BOOST_CHECK (phi == psi);
    }

}

BOOST_AUTO_TEST_SUITE_END()

#define BOOST_TEST_DYN_LINK
#include <boost/test/unit_test.hpp>

#include <expr.hh>
#include <expr_mgr.hh>
#include <expr_printer.hh>

#include <type.hh>
#include <type_mgr.hh>

BOOST_AUTO_TEST_SUITE(tests)

BOOST_AUTO_TEST_CASE(types)
{
    TypeMgr& tm = TypeMgr::INSTANCE();
    ExprMgr& em = ExprMgr::INSTANCE();

    {
        Type_ptr bt = tm.find_boolean();
        BOOST_CHECK(  tm.is_boolean(bt));

        BOOST_CHECK(! tm.is_integer(bt));
        BOOST_CHECK(! tm.is_int_finite(bt));
        BOOST_CHECK(! tm.is_int_range(bt));
        BOOST_CHECK(! tm.is_int_enum(bt));
        BOOST_CHECK(! tm.is_enum(bt));
        BOOST_CHECK(! tm.is_instance(bt));
    }

    {
        Type_ptr in = tm.find_integer();
        BOOST_CHECK(! tm.is_boolean(in));

        BOOST_CHECK(  tm.is_integer(in));
        BOOST_CHECK(! tm.is_int_finite(in));
        BOOST_CHECK(! tm.is_int_range(in));
        BOOST_CHECK(! tm.is_int_enum(in));
        BOOST_CHECK(! tm.is_enum(in));
        BOOST_CHECK(! tm.is_instance(in));
    }

    {
        Expr_ptr a = em.make_iconst(7);
        Expr_ptr b = em.make_iconst(42);

        Type_ptr in = tm.find_range(a, b);
        BOOST_CHECK(! tm.is_boolean(in));

        BOOST_CHECK(  tm.is_integer(in));
        BOOST_CHECK(! tm.is_int_finite(in));
        BOOST_CHECK(  tm.is_int_range(in));
        BOOST_CHECK(! tm.is_int_enum(in));
        BOOST_CHECK(! tm.is_enum(in));
        BOOST_CHECK(! tm.is_instance(in));

        // additional checks
        IntRangeType_ptr irt = dynamic_cast<IntRangeType_ptr>(in);
        BOOST_REQUIRE( NULL != irt );
        BOOST_CHECK( 7 == irt->min() );
        BOOST_CHECK( 42 == irt->max() );
    }

    {
        Type_ptr in = tm.find_unsigned(8);
        BOOST_CHECK(! tm.is_boolean(in));

        BOOST_CHECK(  tm.is_integer(in));
        BOOST_CHECK(  tm.is_int_finite(in));
        BOOST_CHECK(! tm.is_int_range(in));
        BOOST_CHECK(! tm.is_int_enum(in));

        BOOST_CHECK(! tm.is_instance(in));

        // additional checks
        FiniteIntegerType_ptr fit = dynamic_cast<FiniteIntegerType_ptr>(in);
        BOOST_REQUIRE( NULL != fit );
        BOOST_CHECK( ! fit->is_signed() );
    }

    {
        Type_ptr in = tm.find_signed(16);
        BOOST_CHECK(! tm.is_boolean(in));

        BOOST_CHECK(  tm.is_integer(in));
        BOOST_CHECK(  tm.is_int_finite(in));
        BOOST_CHECK(! tm.is_int_range(in));
        BOOST_CHECK(! tm.is_int_enum(in));

        BOOST_CHECK(! tm.is_instance(in));

        // additional checks
        FiniteIntegerType_ptr fit = dynamic_cast<FiniteIntegerType_ptr>(in);
        BOOST_REQUIRE( NULL != fit );
        BOOST_CHECK(   fit->is_signed() );
    }

    {
        Expr_ptr h = em.make_identifier("huey");
        Expr_ptr l = em.make_identifier("louie");
        Expr_ptr d = em.make_identifier("dewey");
        Expr_ptr ctx = em.make_main(); // default ctx

        ExprSet ev;
        ev.insert(h);
        ev.insert(l);
        ev.insert(d);

        Type_ptr in = tm.find_enum(ctx, ev);
        BOOST_CHECK(! tm.is_boolean(in));

        BOOST_CHECK(! tm.is_integer(in));
        BOOST_CHECK(! tm.is_int_finite(in));
        BOOST_CHECK(! tm.is_int_range(in));
        BOOST_CHECK(! tm.is_int_enum(in));
        BOOST_CHECK(  tm.is_enum(in));

        BOOST_CHECK(! tm.is_instance(in));

        // additional checks
        EnumType_ptr et = dynamic_cast<EnumType_ptr>(in);
        BOOST_REQUIRE( NULL != et );

        BOOST_CHECK( 3 == et->literals().size() );

        // try all possible different orderings (3! = 6)
        { // #1
            ExprSet lhd;
            lhd.insert(l); lhd.insert(h); lhd.insert(d);
            BOOST_CHECK(in == tm.find_enum(ctx, lhd));
        }

        { // #2
            ExprSet ldh;
            ldh.insert(l); ldh.insert(d); ldh.insert(h);
            BOOST_CHECK(in == tm.find_enum(ctx, ldh));
        }

        { // #3
            ExprSet hld;
            hld.insert(h); hld.insert(l); hld.insert(d);
            BOOST_CHECK(in == tm.find_enum(ctx, hld));
        }

        { // #4
            ExprSet hdl;
            hdl.insert(h); hdl.insert(d); hdl.insert(l);
            BOOST_CHECK(in == tm.find_enum(ctx, hdl));
        }

        { // #5
            ExprSet dlh;
            dlh.insert(d); dlh.insert(l); dlh.insert(h);
            BOOST_CHECK(in == tm.find_enum(ctx, dlh));
        }

        { // #6
            ExprSet dhl;
            dhl.insert(d); dhl.insert(h); dhl.insert(l);
            BOOST_CHECK(in == tm.find_enum(ctx, dhl));
        }
    }
}

BOOST_AUTO_TEST_SUITE_END()

#define BOOST_TEST_DYN_LINK
#include <boost/test/unit_test.hpp>

#include <expr.hh>
#include <expr_mgr.hh>
#include <expr_printer.hh>

#include <type.hh>
#include <type_mgr.hh>

BOOST_AUTO_TEST_SUITE(tests)

BOOST_AUTO_TEST_CASE(boolean_type)
{
    TypeMgr& tm = TypeMgr::INSTANCE();

    Type_ptr bt = tm.find_boolean();
    BOOST_CHECK(  tm.is_boolean(bt));

    BOOST_CHECK(! tm.is_integer(bt));
    // BOOST_CHECK(! tm.is_int_finite(bt));o
    // BOOST_CHECK(! tm.is_int_range(bt));
    // BOOST_CHECK(! tm.is_int_enum(bt));
    BOOST_CHECK(! tm.is_enum(bt));
    BOOST_CHECK(! tm.is_instance(bt));
}

BOOST_AUTO_TEST_CASE(integer_type)
{
    TypeMgr& tm = TypeMgr::INSTANCE();

    Type_ptr in = tm.find_integer();
    BOOST_CHECK(! tm.is_boolean(in));

    BOOST_CHECK(  tm.is_integer(in));
    // BOOST_CHECK(! tm.is_int_finite(in));
    // BOOST_CHECK(! tm.is_int_range(in));
    // BOOST_CHECK(! tm.is_int_enum(in));
    BOOST_CHECK(! tm.is_enum(in));
    BOOST_CHECK(! tm.is_instance(in));
}

// BOOST_AUTO_TEST_CASE(range_type)
// {
//     TypeMgr& tm = TypeMgr::INSTANCE();
//     ExprMgr& em = ExprMgr::INSTANCE();

//     Expr_ptr a = em.make_iconst(7);
//     Expr_ptr a_ = em.make_oconst(0x07);
//     BOOST_REQUIRE( a->value() == a_->value());

//     Expr_ptr b = em.make_iconst(42);
//     Expr_ptr b_ = em.make_hconst(0x2a);
//     BOOST_REQUIRE( b->value() == b_->value());

//     Type_ptr in = tm.find_range(a, b);
//     BOOST_CHECK(! tm.is_boolean(in));

//     BOOST_CHECK(  tm.is_integer(in));
//     // BOOST_CHECK(! tm.is_int_finite(in));
//     BOOST_CHECK(  tm.is_int_range(in));
//     BOOST_CHECK(! tm.is_int_enum(in));
//     BOOST_CHECK(! tm.is_enum(in));
//     BOOST_CHECK(! tm.is_instance(in));

//     // additional checks
//     IntRangeType_ptr irt = dynamic_cast<IntRangeType_ptr>(in);
//     BOOST_REQUIRE( NULL != irt );
//     BOOST_CHECK( 7 == irt->min() );
//     BOOST_CHECK( 42 == irt->max() );

//     // test range normalization
//     BOOST_CHECK(in == tm.find_range(a, b));
//     BOOST_CHECK(in == tm.find_range(b, a));
//     BOOST_CHECK(in == tm.find_range(a_, b));
//     BOOST_CHECK(in == tm.find_range(a, b_));
//     BOOST_CHECK(in == tm.find_range(a_, b_));
//     BOOST_CHECK(in == tm.find_range(b_, a_));
// }

BOOST_AUTO_TEST_CASE(unsigned_type)
{
    TypeMgr& tm = TypeMgr::INSTANCE();

    Type_ptr in = tm.find_unsigned(8);
    BOOST_CHECK(! tm.is_boolean(in));

    BOOST_CHECK(  tm.is_integer(in));
    // BOOST_CHECK(  tm.is_int_finite(in));
    // BOOST_CHECK(! tm.is_int_range(in));
    // BOOST_CHECK(! tm.is_int_enum(in));

    BOOST_CHECK(! tm.is_instance(in));

    // // additional checks
    // FiniteIntegerType_ptr fit = dynamic_cast<FiniteIntegerType_ptr>(in);
    // BOOST_REQUIRE( NULL != fit );
    // BOOST_CHECK( ! fit->is_signed() );
}

BOOST_AUTO_TEST_CASE(signed_type)
{
    TypeMgr& tm = TypeMgr::INSTANCE();

    Type_ptr in = tm.find_signed(16);
    BOOST_CHECK(! tm.is_boolean(in));

    BOOST_CHECK(  tm.is_integer(in));
    // BOOST_CHECK(  tm.is_int_finite(in));
    // BOOST_CHECK(! tm.is_int_range(in));
    // BOOST_CHECK(! tm.is_int_enum(in));

    BOOST_CHECK(! tm.is_instance(in));

    // // additional checks
    // FiniteIntegerType_ptr fit = dynamic_cast<FiniteIntegerType_ptr>(in);
    // BOOST_REQUIRE( NULL != fit );
    // BOOST_CHECK(   fit->is_signed() );
}

BOOST_AUTO_TEST_CASE(enum_type_symbolic)
{
    TypeMgr& tm = TypeMgr::INSTANCE();
    ExprMgr& em = ExprMgr::INSTANCE();

    Expr_ptr h = em.make_identifier("huey");
    Expr_ptr l = em.make_identifier("louie");
    Expr_ptr d = em.make_identifier("dewey");

    ExprSet ev;
    ev.insert(h);
    ev.insert(l);
    ev.insert(d);

    Type_ptr in = tm.find_enum(ev);
    BOOST_CHECK(! tm.is_boolean(in));

    BOOST_CHECK(! tm.is_integer(in));
    // BOOST_CHECK(! tm.is_int_finite(in));
    // BOOST_CHECK(! tm.is_int_range(in));
    // BOOST_CHECK(! tm.is_int_enum(in));
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
        BOOST_CHECK(in == tm.find_enum(lhd));
    }

    { // #2
        ExprSet ldh;
        ldh.insert(l); ldh.insert(d); ldh.insert(h);
        BOOST_CHECK(in == tm.find_enum(ldh));
    }

    { // #3
        ExprSet hld;
        hld.insert(h); hld.insert(l); hld.insert(d);
        BOOST_CHECK(in == tm.find_enum(hld));
    }

    { // #4
        ExprSet hdl;
        hdl.insert(h); hdl.insert(d); hdl.insert(l);
        BOOST_CHECK(in == tm.find_enum(hdl));
    }

    { // #5
        ExprSet dlh;
        dlh.insert(d); dlh.insert(l); dlh.insert(h);
        BOOST_CHECK(in == tm.find_enum(dlh));
    }

    { // #6
        ExprSet dhl;
        dhl.insert(d); dhl.insert(h); dhl.insert(l);
        BOOST_CHECK(in == tm.find_enum(dhl));
    }
}

// BOOST_AUTO_TEST_CASE(enum_type_numeric)
// {
//     TypeMgr& tm = TypeMgr::INSTANCE();
//     ExprMgr& em = ExprMgr::INSTANCE();

//     Expr_ptr h = em.make_iconst(13);
//     Expr_ptr l = em.make_iconst(17);
//     Expr_ptr d = em.make_iconst(42);

//     ExprSet ev;
//     ev.insert(h);
//     ev.insert(l);
//     ev.insert(d);

//     Type_ptr in = tm.find_enum(ev);
//     BOOST_CHECK(! tm.is_boolean(in));

//     BOOST_CHECK(  tm.is_integer(in));
//     // BOOST_CHECK(! tm.is_int_finite(in));
//     BOOST_CHECK(! tm.is_int_range(in));
//     BOOST_CHECK(  tm.is_int_enum(in));
//     BOOST_CHECK(  tm.is_enum(in));

//     BOOST_CHECK(! tm.is_instance(in));

//     // additional checks
//     EnumType_ptr et = dynamic_cast<EnumType_ptr>(in);
//     BOOST_REQUIRE( NULL != et );

//     BOOST_CHECK( 3 == et->literals().size() );

//     // try all possible different orderings (3! = 6)
//     { // #1
//         ExprSet lhd;
//         lhd.insert(l); lhd.insert(h); lhd.insert(d);
//         BOOST_CHECK(in == tm.find_enum(lhd));
//     }

//     { // #2
//         ExprSet ldh;
//         ldh.insert(l); ldh.insert(d); ldh.insert(h);
//         BOOST_CHECK(in == tm.find_enum(ldh));
//     }

//     { // #3
//         ExprSet hld;
//         hld.insert(h); hld.insert(l); hld.insert(d);
//         BOOST_CHECK(in == tm.find_enum(hld));
//     }

//     { // #4
//         ExprSet hdl;
//         hdl.insert(h); hdl.insert(d); hdl.insert(l);
//         BOOST_CHECK(in == tm.find_enum(hdl));
//     }

//     { // #5
//         ExprSet dlh;
//         dlh.insert(d); dlh.insert(l); dlh.insert(h);
//         BOOST_CHECK(in == tm.find_enum(dlh));
//     }

//     { // #6
//         ExprSet dhl;
//         dhl.insert(d); dhl.insert(h); dhl.insert(l);
//         BOOST_CHECK(in == tm.find_enum(dhl));
//     }
// }

// BOOST_AUTO_TEST_CASE(enum_type_mixed)
// {
//     TypeMgr& tm = TypeMgr::INSTANCE();
//     ExprMgr& em = ExprMgr::INSTANCE();

//     Expr_ptr h = em.make_iconst(13);
//     Expr_ptr l = em.make_identifier("donald");
//     Expr_ptr d = em.make_iconst(42);

//     ExprSet ev;
//     ev.insert(h);
//     ev.insert(l);
//     ev.insert(d);

//     Type_ptr in = tm.find_enum(ev);
//     BOOST_CHECK(! tm.is_boolean(in));

//     BOOST_CHECK(! tm.is_integer(in));
//     // BOOST_CHECK(! tm.is_int_finite(in));
//     BOOST_CHECK(! tm.is_int_range(in));
//     BOOST_CHECK(! tm.is_int_enum(in));
//     BOOST_CHECK(  tm.is_enum(in));

//     BOOST_CHECK(! tm.is_instance(in));

//     // additional checks
//     EnumType_ptr et = dynamic_cast<EnumType_ptr>(in);
//     BOOST_REQUIRE( NULL != et );

//     BOOST_CHECK( 3 == et->literals().size() );

//     // try all possible different orderings (3! = 6)
//     { // #1
//         ExprSet lhd;
//         lhd.insert(l); lhd.insert(h); lhd.insert(d);
//         BOOST_CHECK(in == tm.find_enum(lhd));
//     }

//     { // #2
//         ExprSet ldh;
//         ldh.insert(l); ldh.insert(d); ldh.insert(h);
//         BOOST_CHECK(in == tm.find_enum(ldh));
//     }

//     { // #3
//         ExprSet hld;
//         hld.insert(h); hld.insert(l); hld.insert(d);
//         BOOST_CHECK(in == tm.find_enum(hld));
//     }

//     { // #4
//         ExprSet hdl;
//         hdl.insert(h); hdl.insert(d); hdl.insert(l);
//         BOOST_CHECK(in == tm.find_enum(hdl));
//     }

//     { // #5
//         ExprSet dlh;
//         dlh.insert(d); dlh.insert(l); dlh.insert(h);
//         BOOST_CHECK(in == tm.find_enum(dlh));
//     }

//     { // #6
//         ExprSet dhl;
//         dhl.insert(d); dhl.insert(h); dhl.insert(l);
//         BOOST_CHECK(in == tm.find_enum(dhl));
//     }
// }

BOOST_AUTO_TEST_SUITE_END()

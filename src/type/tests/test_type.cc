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
    Type_ptr type = tm.find_boolean();

    BOOST_CHECK(  tm.is_boolean(type));
    BOOST_CHECK(! tm.is_int_const(type));
    BOOST_CHECK(! tm.is_algebraic(type));
    BOOST_CHECK(! tm.is_signed_algebraic(type));
    BOOST_CHECK(! tm.is_unsigned_algebraic(type));
    BOOST_CHECK(! tm.is_enum(type));
}

BOOST_AUTO_TEST_CASE(int_const_type)
{
    TypeMgr& tm = TypeMgr::INSTANCE();
    Type_ptr type = tm.find_int_const();

    BOOST_CHECK(! tm.is_boolean(type));
    BOOST_CHECK(  tm.is_int_const(type));
    BOOST_CHECK(! tm.is_algebraic(type));
    BOOST_CHECK(! tm.is_signed_algebraic(type));
    BOOST_CHECK(! tm.is_unsigned_algebraic(type));
    BOOST_CHECK(! tm.is_enum(type));
}

BOOST_AUTO_TEST_CASE(unsigned_int_type)
{
    TypeMgr& tm = TypeMgr::INSTANCE();
    Type_ptr type = tm.find_unsigned(8);

    BOOST_CHECK(! tm.is_boolean(type));
    BOOST_CHECK(! tm.is_int_const(type));
    BOOST_CHECK(  tm.is_algebraic(type));
    BOOST_CHECK(! tm.is_signed_algebraic(type));
    BOOST_CHECK(  tm.is_unsigned_algebraic(type));
    BOOST_CHECK(! tm.is_enum(type));
}

BOOST_AUTO_TEST_CASE(signed_int_type)
{
    TypeMgr& tm = TypeMgr::INSTANCE();
    Type_ptr type = tm.find_signed(8);

    BOOST_CHECK(! tm.is_boolean(type));
    BOOST_CHECK(! tm.is_int_const(type));
    BOOST_CHECK(  tm.is_algebraic(type));
    BOOST_CHECK(  tm.is_signed_algebraic(type));
    BOOST_CHECK(! tm.is_unsigned_algebraic(type));
    BOOST_CHECK(! tm.is_enum(type));
}

BOOST_AUTO_TEST_CASE(enum_type_symbolic)
{
    #if 0
    TypeMgr& tm = TypeMgr::INSTANCE();
    ExprMgr& em = ExprMgr::INSTANCE();

    Expr_ptr h = em.make_identifier("huey");
    Expr_ptr l = em.make_identifier("louie");
    Expr_ptr d = em.make_identifier("dewey");

    ExprSet ev;
    ev.insert(h);
    ev.insert(l);
    ev.insert(d);

    Type_ptr type = tm.find_enum(ev);
    BOOST_CHECK(! tm.is_boolean(type));
    BOOST_CHECK(! tm.is_int_const(type));
    BOOST_CHECK(! tm.is_algebraic(type));
    BOOST_CHECK(! tm.is_signed_algebraic(type));
    BOOST_CHECK(! tm.is_unsigned_algebraic(type));
    BOOST_CHECK(  tm.is_enum(type));

    // additional checks
    EnumType_ptr et = dynamic_cast<EnumType_ptr>(type);
    BOOST_REQUIRE( NULL != et );

    BOOST_CHECK( 3 == et->literals().size() );

    // try all possible different orderings (3! = 6)
    { // #1
        ExprSet lhd;
        lhd.insert(l); lhd.insert(h); lhd.insert(d);
        BOOST_CHECK(type == tm.find_enum(lhd));
    }

    { // #2
        ExprSet ldh;
        ldh.insert(l); ldh.insert(d); ldh.insert(h);
        BOOST_CHECK(type == tm.find_enum(ldh));
    }

    { // #3
        ExprSet hld;
        hld.insert(h); hld.insert(l); hld.insert(d);
        BOOST_CHECK(type == tm.find_enum(hld));
    }

    { // #4
        ExprSet hdl;
        hdl.insert(h); hdl.insert(d); hdl.insert(l);
        BOOST_CHECK(type == tm.find_enum(hdl));
    }

    { // #5
        ExprSet dlh;
        dlh.insert(d); dlh.insert(l); dlh.insert(h);
        BOOST_CHECK(type == tm.find_enum(dlh));
    }

    { // #6
        ExprSet dhl;
        dhl.insert(d); dhl.insert(h); dhl.insert(l);
        BOOST_CHECK(type == tm.find_enum(dhl));
    }
    #endif
}

BOOST_AUTO_TEST_SUITE_END()

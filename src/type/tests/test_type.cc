#define BOOST_TEST_DYN_LINK
#include <boost/test/unit_test.hpp>

#include <model.hh>
#include <model_mgr.hh>

#include <expr.hh>
#include <expr_mgr.hh>
#include <printer.hh>

#include <type.hh>
#include <type_mgr.hh>

BOOST_AUTO_TEST_SUITE(tests)

BOOST_AUTO_TEST_CASE(boolean_type)
{
    TypeMgr& tm = TypeMgr::INSTANCE();
    Type_ptr type = tm.find_boolean();

    BOOST_CHECK(  type->is_boolean());
    BOOST_CHECK(! type->is_constant());
    BOOST_CHECK(! type->is_algebraic());
    BOOST_CHECK(! type->is_signed_algebraic());
    BOOST_CHECK(! type->is_unsigned_algebraic());
    BOOST_CHECK(! type->is_enum());
}

BOOST_AUTO_TEST_CASE(constant_type)
{
    TypeMgr& tm = TypeMgr::INSTANCE();
    Type_ptr type = tm.find_constant();

    BOOST_CHECK(! type->is_boolean());
    BOOST_CHECK(  type->is_constant());
    BOOST_CHECK(  type->is_algebraic());
    BOOST_CHECK(! type->is_signed_algebraic());
    BOOST_CHECK(! type->is_unsigned_algebraic());
    BOOST_CHECK(! type->is_enum());
}

BOOST_AUTO_TEST_CASE(unsigned_int_type)
{
    TypeMgr& tm = TypeMgr::INSTANCE();
    Type_ptr type = tm.find_unsigned(8);

    BOOST_CHECK(! type->is_boolean());
    BOOST_CHECK(! type->is_constant());
    BOOST_CHECK(  type->is_algebraic());
    BOOST_CHECK(! type->is_signed_algebraic());
    BOOST_CHECK(  type->is_unsigned_algebraic());
    BOOST_CHECK(! type->is_enum());
}

BOOST_AUTO_TEST_CASE(signed_int_type)
{
    TypeMgr& tm = TypeMgr::INSTANCE();
    Type_ptr type = tm.find_signed(8);

    BOOST_CHECK(! type->is_boolean());
    BOOST_CHECK(! type->is_constant());
    BOOST_CHECK(  type->is_algebraic());
    BOOST_CHECK(  type->is_signed_algebraic());
    BOOST_CHECK(! type->is_unsigned_algebraic());
    BOOST_CHECK(! type->is_enum());
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
    BOOST_CHECK(! type->is_boolean());
    BOOST_CHECK(! type->is_constant());
    BOOST_CHECK(! type->is_algebraic());
    BOOST_CHECK(! type->is_signed_algebraic());
    BOOST_CHECK(! type->is_unsigned_algebraic());
    BOOST_CHECK(  type->is_enum());

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

BOOST_AUTO_TEST_CASE(type_inference)
{
    /* a rather rough setup ... */
    ModelMgr& mm (ModelMgr::INSTANCE());
    ExprMgr& em (ExprMgr::INSTANCE());
    TypeMgr& tm (TypeMgr::INSTANCE());
    Model& model (reinterpret_cast<Model&> (*mm.model()));
    Module& main (* new Module(em.make_main()));

    /* done with setup, now on with the actual tests :-) */

    { /* booleans */
        Type_ptr boolean = tm.find_boolean();

        Atom a_x("x"); Expr_ptr x = em.make_identifier(a_x);
        main.add_var(x, new Variable(main.expr(), x, boolean));
        Atom a_y("y"); Expr_ptr y = em.make_identifier(a_y);
        main.add_var(y, new Variable(main.expr(), y, boolean));
        model.add_module( em.make_main(), &main);

        BOOST_CHECK( boolean ==
                     mm.type( em.make_F( x ),
                              em.make_main()));

        BOOST_CHECK( boolean ==
                     mm.type( em.make_G( x ),
                              em.make_main()));

        BOOST_CHECK( boolean ==
                     mm.type( em.make_X( x ),
                              em.make_main()));

        BOOST_CHECK( boolean ==
                     mm.type( em.make_U( x, y ),
                              em.make_main()));

        BOOST_CHECK( boolean ==
                     mm.type( em.make_R( x, y ),
                              em.make_main()));

        BOOST_CHECK( boolean ==
                     mm.type( em.make_next( x ),
                              em.make_main()));

        BOOST_CHECK( boolean ==
                     mm.type( em.make_prev( x ),
                              em.make_main()));

        BOOST_CHECK( boolean ==
                     mm.type( em.make_not( x ),
                              em.make_main()));

        BOOST_CHECK( boolean ==
                     mm.type( em.make_and( x, y ),
                              em.make_main()));

        BOOST_CHECK( boolean ==
                     mm.type( em.make_or( x, y ),
                              em.make_main()));

        BOOST_CHECK( boolean ==
                     mm.type( em.make_xor( x, y ),
                              em.make_main()));

        BOOST_CHECK( boolean ==
                     mm.type( em.make_xnor( x, y ),
                              em.make_main()));

        BOOST_CHECK( boolean ==
                     mm.type( em.make_implies( x, y ),
                              em.make_main()));

        BOOST_CHECK( boolean ==
                     mm.type( em.make_iff( x, y ),
                              em.make_main()));
    }

    { /* uint16_t */
        Type_ptr uint16 = tm.find_unsigned(16);

        Atom a_x("x2"); Expr_ptr x = em.make_identifier(a_x);
        main.add_var(x, new Variable(main.expr(), x, uint16));
        Atom a_y("y2"); Expr_ptr y = em.make_identifier(a_y);
        main.add_var(y, new Variable(main.expr(), y, uint16));
        model.add_module( em.make_main(), &main);

        // relationals
        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_eq( x, y ),
                              em.make_main()));

        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_ne( x, y ),
                              em.make_main()));

        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_ge( x, y ),
                              em.make_main()));

        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_gt( x, y ),
                              em.make_main()));

        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_le( x, y ),
                              em.make_main()));

        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_lt( x, y),
                              em.make_main()));

        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_eq( x, y ),
                              em.make_main()));

        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_ne( x, y ),
                              em.make_main()));

        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_ge( x, y ),
                              em.make_main()));

        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_gt( x, y ),
                              em.make_main()));

        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_le( x, y ),
                              em.make_main()));

        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_lt( x, y),
                              em.make_main()));

        // y == x op k
        Expr_ptr k = em.make_const(42);
        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_eq( x, k),
                              em.make_main()));

        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_eq(y,
                                         em.make_add( x, k)),
                              em.make_main()));

        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_eq(y,
                                         em.make_sub( x, k)),
                              em.make_main()));

        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_eq(y,
                                         em.make_div( x, k)),
                              em.make_main()));

        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_eq(y,
                                         em.make_mul( x, k)),
                              em.make_main()));

        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_eq(y,
                                         em.make_mod( x, k)),
                              em.make_main()));

        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_eq(y,
                                         em.make_and( x, k)),
                              em.make_main()));

        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_eq(y,
                                         em.make_or( x, k)),
                              em.make_main()));

        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_eq(y,
                                         em.make_xor( x, k)),
                              em.make_main()));

        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_eq(y,
                                         em.make_xnor( x, k)),
                              em.make_main()));

        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_eq(y,
                                         em.make_implies( x, k)),
                              em.make_main()));

        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_eq(y,
                                         em.make_iff( x, k)),
                              em.make_main()));

        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_eq(y,
                                         em.make_lshift( x, k)),
                              em.make_main()));

        BOOST_CHECK( tm.find_boolean() ==
                     mm.type( em.make_eq(y,
                                         em.make_rshift( x, k)),
                              em.make_main()));
    }

}

BOOST_AUTO_TEST_SUITE_END()

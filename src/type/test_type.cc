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
    BOOST_CHECK(! type->is_algebraic());
    BOOST_CHECK(! type->is_signed_algebraic());
    BOOST_CHECK(! type->is_unsigned_algebraic());
    BOOST_CHECK(! type->is_enum());
}

BOOST_AUTO_TEST_CASE(unsigned_int_type)
{
    TypeMgr& tm = TypeMgr::INSTANCE();
    Type_ptr type = tm.find_unsigned(8);

    BOOST_CHECK(! type->is_boolean());
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
    BOOST_CHECK(  type->is_algebraic());
    BOOST_CHECK(  type->is_signed_algebraic());
    BOOST_CHECK(! type->is_unsigned_algebraic());
    BOOST_CHECK(! type->is_enum());
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
}

BOOST_AUTO_TEST_CASE(type_inference)
{
    /* a rather rough setup... */
    ModelMgr& mm (ModelMgr::INSTANCE());
    ExprMgr& em (ExprMgr::INSTANCE());
    TypeMgr& tm (TypeMgr::INSTANCE());

    Model& model (mm.model());
    Module& main (* new Module(em.make_main()));

    /* A few types */
    Type_ptr boolean = tm.find_boolean();
    Type_ptr uint16 = tm.find_unsigned(16);
    Type_ptr int16 = tm.find_signed(16);

    /* A pair of variables for each type:
       (x, y) are booleans;
       (s, t) are unsigned(16);
       (u, v) are signed(16)
    */
    Atom a_x("x");
    Expr_ptr x = em.make_identifier(a_x);
    main.add_var(x, new Variable(main.name(), x, boolean));

    Atom a_y("y"); Expr_ptr y = em.make_identifier(a_y);
    main.add_var(y, new Variable(main.name(), y, boolean));

    Atom a_s("s"); Expr_ptr s = em.make_identifier(a_s);
    main.add_var(s, new Variable(main.name(), s, uint16));

    Atom a_t("t"); Expr_ptr t = em.make_identifier(a_t);
    main.add_var(t, new Variable(main.name(), t, uint16));

    Atom a_u("u"); Expr_ptr u = em.make_identifier(a_u);
    main.add_var(u, new Variable(main.name(), u, int16));

    Atom a_v("v"); Expr_ptr v = em.make_identifier(a_v);
    main.add_var(v, new Variable(main.name(), v, int16));

    // add the main module to the model, model analysis will be
    // triggered automatically when invoking the type checker.
    model.add_module(main);

    BOOST_CHECK(boolean ==
                mm.type(x));

    BOOST_CHECK( boolean ==
                 mm.type( em.make_next( x )));

    BOOST_CHECK( boolean ==
                 mm.type( em.make_not( x )));

    BOOST_CHECK( boolean ==
                 mm.type( em.make_and( x, y )));

    BOOST_CHECK( boolean ==
                 mm.type( em.make_or( x, y )));

    BOOST_CHECK( boolean ==
                 mm.type( em.make_eq( x, y )));

    BOOST_CHECK( boolean ==
                 mm.type( em.make_ne( x, y )));

    BOOST_CHECK( boolean ==
                 mm.type( em.make_implies( x, y )));

    // relationals (unsigned)
    BOOST_CHECK( boolean ==
                 mm.type( em.make_eq( s, t )));

    BOOST_CHECK( boolean ==
                 mm.type( em.make_ne( s, t )));

    BOOST_CHECK( boolean ==
                 mm.type( em.make_ge( s, t )));

    BOOST_CHECK( boolean ==
                 mm.type( em.make_gt( s, t )));

    BOOST_CHECK( boolean ==
                 mm.type( em.make_le( s, t )));

    BOOST_CHECK( boolean ==
                 mm.type( em.make_lt( s, t )));

    // relationals (signed)
    BOOST_CHECK( boolean ==
                 mm.type( em.make_eq( u, v )));

    BOOST_CHECK( boolean ==
                 mm.type( em.make_ne( u, v )));

    BOOST_CHECK( boolean ==
                 mm.type( em.make_ge( u, v )));

    BOOST_CHECK( boolean ==
                 mm.type( em.make_gt( u, v )));

    BOOST_CHECK( boolean ==
                 mm.type( em.make_le( u, v )));

    BOOST_CHECK( boolean ==
                 mm.type( em.make_lt( u, v )));

    // arithmetics
    BOOST_CHECK( uint16 ==
                 mm.type( em.make_add( s, t)));

    BOOST_CHECK( int16 ==
                 mm.type( em.make_add( u, v)));

    BOOST_CHECK( uint16 ==
                 mm.type( em.make_sub( s, t)));

    BOOST_CHECK( int16 ==
                 mm.type( em.make_sub( u, v)));

    BOOST_CHECK( uint16 ==
                 mm.type( em.make_mul( s, t)));

    BOOST_CHECK( int16 ==
                 mm.type( em.make_mul( u, v)));

    BOOST_CHECK( uint16 ==
                 mm.type( em.make_div( s, t)));

    BOOST_CHECK( int16 ==
                 mm.type( em.make_div( u, v)));

    BOOST_CHECK( uint16 ==
                 mm.type( em.make_mod( s, t)));

    BOOST_CHECK( int16 ==
                 mm.type( em.make_mod( u, v)));

    BOOST_CHECK( uint16 ==
                 mm.type( em.make_lshift( s, t)));

    BOOST_CHECK( int16 ==
                 mm.type( em.make_lshift( u, v)));

    BOOST_CHECK( uint16 ==
                 mm.type( em.make_rshift( s, t)));

    BOOST_CHECK( int16 ==
                 mm.type( em.make_rshift( u, v)));

    #if 0
    // arithmetics with a constant
    Expr_ptr k = em.make_const(42);

    BOOST_CHECK( uint16 ==
                 mm.type( em.make_add( s, k)));

    BOOST_CHECK( int16 ==
                 mm.type( em.make_add( u, k)));

    BOOST_CHECK( uint16 ==
                 mm.type( em.make_sub( s, k)));

    BOOST_CHECK( int16 ==
                 mm.type( em.make_sub( u, k)));

    BOOST_CHECK( uint16 ==
                 mm.type( em.make_mul( s, k)));

    BOOST_CHECK( int16 ==
                 mm.type( em.make_mul( u, k)));

    BOOST_CHECK( uint16 ==
                 mm.type( em.make_div( s, k)));

    BOOST_CHECK( int16 ==
                 mm.type( em.make_div( u, k)));

    BOOST_CHECK( uint16 ==
                 mm.type( em.make_mod( s, k)));

    BOOST_CHECK( int16 ==
                 mm.type( em.make_mod( u, k)));
    #endif
}

BOOST_AUTO_TEST_SUITE_END()

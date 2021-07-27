/**
 * @file test_type.cc
 * @brief Type classes unit tests
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA
 *
 **/

#define BOOST_TEST_DYN_LINK
#include <boost/test/unit_test.hpp>

#include <model/model.hh>
#include <model/model_mgr.hh>
#include <model/module.hh>

#include <expr/expr.hh>
#include <expr/expr_mgr.hh>
#include <expr/printer/printer.hh>

#include <type/type.hh>
#include <type/type_mgr.hh>

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
    BOOST_CHECK(! type->is_array());
    BOOST_CHECK(! type->is_instance());
}

BOOST_AUTO_TEST_CASE(boolean_array_type)
{
    TypeMgr& tm = TypeMgr::INSTANCE();
    Type_ptr type = tm.find_boolean_array(10);

    BOOST_CHECK(! type->is_boolean());
    BOOST_CHECK(! type->is_algebraic());
    BOOST_CHECK(! type->is_signed_algebraic());
    BOOST_CHECK(! type->is_unsigned_algebraic());
    BOOST_CHECK(! type->is_enum());
    BOOST_CHECK(  type->is_array());
    BOOST_CHECK(! type->is_instance());
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
    BOOST_CHECK(! type->is_array());
    BOOST_CHECK(! type->is_instance());
}

BOOST_AUTO_TEST_CASE(unsigned_int_array_type)
{
    TypeMgr& tm = TypeMgr::INSTANCE();
    Type_ptr type = tm.find_unsigned_array(8, 10);

    BOOST_CHECK(! type->is_boolean());
    BOOST_CHECK(! type->is_algebraic());
    BOOST_CHECK(! type->is_signed_algebraic());
    BOOST_CHECK(! type->is_unsigned_algebraic());
    BOOST_CHECK(! type->is_enum());
    BOOST_CHECK(  type->is_array());
    BOOST_CHECK(! type->is_instance());
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
    BOOST_CHECK(! type->is_array());
    BOOST_CHECK(! type->is_instance());
}

BOOST_AUTO_TEST_CASE(signed_int_array_type)
{
    TypeMgr& tm = TypeMgr::INSTANCE();
    Type_ptr type = tm.find_signed_array(8, 10);

    BOOST_CHECK(! type->is_boolean());
    BOOST_CHECK(! type->is_algebraic());
    BOOST_CHECK(! type->is_signed_algebraic());
    BOOST_CHECK(! type->is_unsigned_algebraic());
    BOOST_CHECK(! type->is_enum());
    BOOST_CHECK(  type->is_array());
    BOOST_CHECK(! type->is_instance());
}

BOOST_AUTO_TEST_CASE(enum_type)
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
    BOOST_CHECK(! type->is_array());
    BOOST_CHECK(! type->is_instance());

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

BOOST_AUTO_TEST_CASE(enum_array_type)
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

    Type_ptr type = tm.find_enum_array(ev, 10);

    BOOST_CHECK(! type->is_boolean());
    BOOST_CHECK(! type->is_constant());
    BOOST_CHECK(! type->is_algebraic());
    BOOST_CHECK(! type->is_signed_algebraic());
    BOOST_CHECK(! type->is_unsigned_algebraic());
    BOOST_CHECK(! type->is_enum());
    BOOST_CHECK(  type->is_array());
    BOOST_CHECK(! type->is_instance());
}

BOOST_AUTO_TEST_CASE(type_checking)
{
    /* a rather rough setup... */
    ModelMgr& mm (ModelMgr::INSTANCE());
    ExprMgr& em (ExprMgr::INSTANCE());
    TypeMgr& tm (TypeMgr::INSTANCE());

    /* set word width to 16 bits */
    opts::OptsMgr& om { opts::OptsMgr::INSTANCE() };
    om.set_word_width(16);

    Model& model (mm.model());
    Atom a_main("main");
    Module& main (* new Module(em.make_identifier(a_main)));
    model.add_module(main);

    /* A few types */
    Type_ptr boolean = tm.find_boolean();
    Type_ptr uint16 = tm.find_unsigned(16);
    Type_ptr int16 = tm.find_signed(16);

    /*
       A pair of variables for each type:
       (x, y) are booleans;
       (s, t) are unsigned(16);
       (u, v) are signed(16)
    */
    Atom a_x("x");
    Expr_ptr x = em.make_identifier(a_x);
    main.add_var(x, new symb::Variable(main.name(), x, boolean));

    Atom a_y("y"); Expr_ptr y = em.make_identifier(a_y);
    main.add_var(y, new symb::Variable(main.name(), y, boolean));

    Atom a_s("s"); Expr_ptr s = em.make_identifier(a_s);
    main.add_var(s, new symb::Variable(main.name(), s, uint16));

    Atom a_t("t"); Expr_ptr t = em.make_identifier(a_t);
    main.add_var(t, new symb::Variable(main.name(), t, uint16));

    Atom a_u("u"); Expr_ptr u = em.make_identifier(a_u);
    main.add_var(u, new symb::Variable(main.name(), u, int16));

    Atom a_v("v"); Expr_ptr v = em.make_identifier(a_v);
    main.add_var(v, new symb::Variable(main.name(), v, int16));

    // add the main module to the model
    model.add_module(main);

    BOOST_CHECK(ModelMgr::INSTANCE().analyze());

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

    // type system violations
    BOOST_CHECK_THROW(mm.type( em.make_neg( x )),
                      TypeException);

    BOOST_CHECK_THROW(mm.type( em.make_ge( x, y )),
                      TypeException);

    BOOST_CHECK_THROW(mm.type( em.make_gt( x, y )),
                      TypeException);

    BOOST_CHECK_THROW(mm.type( em.make_le( x, y )),
                      TypeException);

    BOOST_CHECK_THROW(mm.type( em.make_lt( x, y )),
                      TypeException);

    BOOST_CHECK_THROW(mm.type( em.make_lshift( x, y )),
                      TypeException);

    BOOST_CHECK_THROW(mm.type( em.make_rshift( x, y )),
                      TypeException);

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

    // type system violations
    BOOST_CHECK_THROW(mm.type( em.make_not( s )),
                      TypeException);

    BOOST_CHECK_THROW(mm.type( em.make_and( s, t )),
                      TypeException);

    BOOST_CHECK_THROW(mm.type( em.make_or( s, t )),
                      TypeException);

    BOOST_CHECK_THROW(mm.type( em.make_implies( s, t )),
                      TypeException);

    BOOST_CHECK_THROW(mm.type( em.make_eq( x, s )),
                      TypeException);

    BOOST_CHECK_THROW(mm.type( em.make_eq( x, u )),
                      TypeException);

    BOOST_CHECK_THROW(mm.type( em.make_ne( x, s )),
                      TypeException);

    BOOST_CHECK_THROW(mm.type( em.make_ne( x, u )),
                      TypeException);

    BOOST_CHECK_THROW(mm.type( em.make_ge( x, s )),
                      TypeException);

    BOOST_CHECK_THROW(mm.type( em.make_ge( x, u )),
                      TypeException);

    BOOST_CHECK_THROW(mm.type( em.make_gt( x, s )),
                      TypeException);

    BOOST_CHECK_THROW(mm.type( em.make_gt( x, u )),
                      TypeException);

    BOOST_CHECK_THROW(mm.type( em.make_le( x, s )),
                      TypeException);

    BOOST_CHECK_THROW(mm.type( em.make_le( x, u )),
                      TypeException);

    BOOST_CHECK_THROW(mm.type( em.make_lt( x, s )),
                      TypeException);

    BOOST_CHECK_THROW(mm.type( em.make_lt( x, u )),
                      TypeException);

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

    // type system violations
    BOOST_CHECK_THROW(mm.type( em.make_not( u )),
                      TypeException);

    BOOST_CHECK_THROW(mm.type( em.make_and( u, v )),
                      TypeException);

    BOOST_CHECK_THROW(mm.type( em.make_or( u, v )),
                      TypeException);

    BOOST_CHECK_THROW(mm.type( em.make_implies( u, v )),
                      TypeException);

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
}


BOOST_AUTO_TEST_SUITE_END()

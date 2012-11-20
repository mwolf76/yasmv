#define BOOST_TEST_DYN_LINK
#include <boost/test/unit_test.hpp>

#include <stdint.h>

#include <expr.hh>
#include <expr_mgr.hh>
#include <expr_printer.hh>

#include <model.hh>
#include <model_mgr.hh>

#include <compilers/compiler.hh>

#include <dd_walker.hh>

class TestWalker : public DDWalker {
public:
    TestWalker(CuddMgr& owner)
        : DDWalker(owner)
    {}

    bool condition(const DdNode *node)
    {
        DdNode *N = Cudd_Regular(node);
        assert( cuddIsConstant(N) );

        /* arithmetical zero */
        if (node == f_owner.dd().getManager()->zero) {
            return false;
        }

        return true;
    }

    virtual void action(value_t value) =0;

protected:

    /* services */
    value_t pow2(unsigned exp)
    {
        value_t res = 1;
        for (unsigned i = exp; i; -- i) {
            res *= 2;
        }

        return res;
    }

    value_t value(bool msb)
    {
        long i, res = 0;
        int size = f_owner.dd().getManager()->size;
        assert( 0 == size % 2); // size is even

        int half = size/2;
        char *data = (msb)
            ? f_data
            : f_data + half;

        for (i = half -1; 0 <= i; -- i) {
            if ( *data == 1 ) {
                res += pow2(i);
            }

            ++ data;
        }

        return res;

    }

    inline value_t msb_value()
    { return value (true); }

    inline value_t lsb_value()
    { return value (false); }

};

// a decent abstraction :-)
class PlusTestWalker : public TestWalker {
public:
    PlusTestWalker(CuddMgr& owner, int ofs = 1)
        : TestWalker(owner)
        , f_ofs(ofs)
    {}

    virtual void action(value_t value)
    {
        BOOST_CHECK(1 == value); /* 0-1 ADDs */

        value_t msb = msb_value();
        value_t lsb = lsb_value();

        BOOST_CHECK(msb == (f_ofs + lsb) % 0x100);
    }

private:
    int f_ofs;
};

class NegTestWalker : public TestWalker {
public:
    NegTestWalker(CuddMgr& owner)
        : TestWalker(owner)
    {}

    virtual void action(value_t value)
    {
        BOOST_CHECK(1 == value); /* 0-1 ADDs */

        value_t msb = msb_value();
        value_t lsb = lsb_value();
        BOOST_CHECK(0 == ((msb + lsb) % 0x100));
    }
};

class SubTestWalker : public TestWalker {
public:
    SubTestWalker(CuddMgr& owner, int ofs = 1)
        : TestWalker(owner)
        , f_ofs(ofs)
    {}

    virtual void action(value_t value)
    {
        BOOST_CHECK(1 == value); /* 0-1 ADDs */

        uint8_t lhs = (uint8_t) msb_value();
        uint8_t rhs = (uint8_t) lsb_value() - f_ofs;
        BOOST_CHECK(lhs == rhs);
    }

private:
    int f_ofs;
};

class AndTestWalker : public TestWalker {
public:
    AndTestWalker(CuddMgr& owner, int ofs = 1)
        : TestWalker(owner)
        , f_ofs(ofs)
    {}

    virtual void action(value_t value)
    {
        BOOST_CHECK(1 == value); /* 0-1 ADDs */

        uint8_t lhs = (uint8_t) msb_value();
        uint8_t rhs = (uint8_t) lsb_value();
        BOOST_CHECK(lhs == (rhs & f_ofs));
    }

private:
    int f_ofs;
};

class OrTestWalker : public TestWalker {
public:
    OrTestWalker(CuddMgr& owner, int ofs = 1)
        : TestWalker(owner)
        , f_ofs(ofs)
    {}

    virtual void action(value_t value)
    {
        BOOST_CHECK(1 == value); /* 0-1 ADDs */

        uint8_t lhs = (uint8_t) msb_value();
        uint8_t rhs = (uint8_t) lsb_value();
        BOOST_CHECK(lhs == (rhs | f_ofs));
    }

private:
    int f_ofs;
};

class XorTestWalker : public TestWalker {
public:
    XorTestWalker(CuddMgr& owner, int ofs = 1)
        : TestWalker(owner)
        , f_ofs(ofs)
    {}

    virtual void action(value_t value)
    {
        BOOST_CHECK(1 == value); /* 0-1 ADDs */

        uint8_t lhs = (uint8_t) msb_value();
        uint8_t rhs = (uint8_t) lsb_value();
        BOOST_CHECK(lhs == (rhs ^ f_ofs));
    }

private:
    int f_ofs;
};

class XnorTestWalker : public TestWalker {
public:
    XnorTestWalker(CuddMgr& owner, int ofs = 1)
        : TestWalker(owner)
        , f_ofs(ofs)
    {}

    virtual void action(value_t value)
    {
        BOOST_CHECK(1 == value); /* 0-1 ADDs */

        uint8_t lhs = (uint8_t) msb_value();
        uint8_t rhs = (uint8_t) ~ ((lsb_value() ^ f_ofs));
        BOOST_CHECK(lhs == rhs);
    }

private:
    int f_ofs;
};

class LtTestWalker : public TestWalker {
public:
    LtTestWalker(CuddMgr& owner)
        : TestWalker(owner)
    {}

    virtual void action(value_t value)
    {
        uint8_t lhs = (uint8_t) msb_value();
        uint8_t rhs = (uint8_t) lsb_value();
        BOOST_CHECK(lhs < rhs);
    }
};

class LeTestWalker : public TestWalker {
public:
    LeTestWalker(CuddMgr& owner)
        : TestWalker(owner)
    {}

    virtual void action(value_t value)
    {
        assert(1 == value);
        uint8_t lhs = (uint8_t) msb_value();
        uint8_t rhs = (uint8_t) lsb_value();
        BOOST_CHECK(lhs <= rhs);
    }
};

class GtTestWalker : public TestWalker {
public:
    GtTestWalker(CuddMgr& owner)
        : TestWalker(owner)
    {}

    virtual void action(value_t value)
    {
        uint8_t lhs = (uint8_t) msb_value();
        uint8_t rhs = (uint8_t) lsb_value();
        BOOST_CHECK(lhs > rhs);
    }
};

class GeTestWalker : public TestWalker {
public:
    GeTestWalker(CuddMgr& owner)
        : TestWalker(owner)
    {}

    virtual void action(value_t value)
    {
        uint8_t lhs = (uint8_t) msb_value();
        uint8_t rhs = (uint8_t) lsb_value();
        BOOST_CHECK(lhs >= rhs);
    }
};

BOOST_AUTO_TEST_SUITE(tests)
BOOST_AUTO_TEST_CASE(compiler)
{
    ModelMgr& mm(ModelMgr::INSTANCE());
    ExprMgr& em(ExprMgr::INSTANCE());
    TypeMgr& tm(TypeMgr::INSTANCE());

    Compiler f_compiler;

    Expr_ptr main_expr(em.make_main());
    IModule_ptr main_module = new Module( main_expr );
    Type_ptr u2 = tm.find_unsigned(2);

    Atom a_x("x"); Expr_ptr x = em.make_identifier(a_x);
    main_module->add_localVar(x, new StateVar(main_expr, x, u2));

    Atom a_y("y"); Expr_ptr y = em.make_identifier(a_y);
    main_module->add_localVar(y, new StateVar(main_expr, y, u2));

    mm.model()->add_module(main_expr, main_module);

    // WEIRD BUG!!!
    // {
    //     Atom a_d("d_plus_1"); Expr_ptr define = em.make_identifier(a_d);

    //     /* y := x + 1 */
    //     Expr_ptr test_expr = em.make_eq( y, em.make_add( x, em.make_one()));

    //     main_module->add_localDef(define, new Define(main_expr, define, test_expr));
    //     PlusTestWalker ptw(CuddMgr::INSTANCE());

    //     ptw(f_compiler.process( main_expr, define, 0));
    // }

    // {
    //     Atom a_d("d_plus_2"); Expr_ptr define = em.make_identifier(a_d);

    //     /* y := x + 17 */
    //     Expr_ptr test_expr = em.make_eq( y, em.make_add( x, em.make_iconst(17)));

    //     main_module->add_localDef(define, new Define(main_expr, define, test_expr));
    //     PlusTestWalker ptw(CuddMgr::INSTANCE(), 17);

    //     ptw(f_compiler.process( main_expr, define, 0));
    // }

    // {
    //     Atom a_d("d_plus_3"); Expr_ptr define = em.make_identifier(a_d);

    //     /* y := 1 + x */
    //     Expr_ptr test_expr = em.make_eq( y, em.make_add( em.make_one(), x));

    //     main_module->add_localDef(define, new Define(main_expr, define, test_expr));
    //     PlusTestWalker ptw(CuddMgr::INSTANCE());

    //     ptw(f_compiler.process( main_expr, define, 0));
    // }

    // {
    //     Atom a_d("d_plus_4"); Expr_ptr define = em.make_identifier(a_d);

    //     /* y := 17 + x */
    //     Expr_ptr test_expr = em.make_eq( y, em.make_add( em.make_iconst(17), x));

    //     main_module->add_localDef(define, new Define(main_expr, define, test_expr));
    //     PlusTestWalker ptw(CuddMgr::INSTANCE(), 17);

    //     ptw(f_compiler.process( main_expr, define, 0));
    // }

    // {
    //     Atom a_d("d_neg"); Expr_ptr define = em.make_identifier(a_d);

    //     /* y := - x */
    //     Expr_ptr test_expr = em.make_eq( y, em.make_neg( x ));
    //     main_module->add_localDef(define, new Define(main_expr, define, test_expr));

    //     NegTestWalker ntw(CuddMgr::INSTANCE());
    //     ntw(f_compiler.process( main_expr, define, 0));
    // }

    // {
    //     Atom a_d("d_sub_1"); Expr_ptr define = em.make_identifier(a_d);

    //     /* y := x - 1 */
    //     Expr_ptr test_expr = em.make_eq( y, em.make_sub( x, em.make_one()));
    //     main_module->add_localDef(define, new Define(main_expr, define, test_expr));

    //     SubTestWalker stw(CuddMgr::INSTANCE());
    //     stw(f_compiler.process( main_expr, define, 0));
    // }

    // {
    //     Atom a_d("d_sub_2"); Expr_ptr define = em.make_identifier(a_d);

    //     /* y := x - 42 */
    //     Expr_ptr test_expr = em.make_eq( y, em.make_sub( x, em.make_iconst(42)));
    //     main_module->add_localDef(define, new Define(main_expr, define, test_expr));

    //     SubTestWalker stw(CuddMgr::INSTANCE(), 42);
    //     stw(f_compiler.process( main_expr, define, 0));
    // }

    // {
    //     Atom a_d("d_and_1"); Expr_ptr define = em.make_identifier(a_d);

    //     /* y := x & 1 */
    //     Expr_ptr test_expr = em.make_eq( y, em.make_and( x, em.make_one()));
    //     main_module->add_localDef(define, new Define(main_expr, define, test_expr));

    //     AndTestWalker atw(CuddMgr::INSTANCE());
    //     atw(f_compiler.process( main_expr, define, 0));
    // }

    // {
    //     Atom a_d("d_or_1"); Expr_ptr define = em.make_identifier(a_d);

    //     /* y := x & 1 */
    //     Expr_ptr test_expr = em.make_eq( y, em.make_or( x, em.make_one()));
    //     main_module->add_localDef(define, new Define(main_expr, define, test_expr));

    //     OrTestWalker atw(CuddMgr::INSTANCE());
    //     atw(f_compiler.process( main_expr, define, 0));
    // }

    // {
    //     Atom a_d("d_xor_1"); Expr_ptr define = em.make_identifier(a_d);

    //     /* y := x ^ 1 */
    //     Expr_ptr test_expr = em.make_eq( y, em.make_xor( x, em.make_one()));
    //     main_module->add_localDef(define, new Define(main_expr, define, test_expr));

    //     XorTestWalker atw(CuddMgr::INSTANCE());
    //     atw(f_compiler.process( main_expr, define, 0));
    // }

    // {
    //     Atom a_d("d_xnor_1"); Expr_ptr define = em.make_identifier(a_d);

    //     /* y := ~ (x ^ 1) */
    //     Expr_ptr test_expr = em.make_eq( y, em.make_xnor( x, em.make_one()));
    //     main_module->add_localDef(define, new Define(main_expr, define, test_expr));

    //     XnorTestWalker atw(CuddMgr::INSTANCE());
    //     atw(f_compiler.process( main_expr, define, 0));
    // }

    {
        Atom a_d("d_lt_1"); Expr_ptr define = em.make_identifier(a_d);

        /* y < x */
        Expr_ptr test_expr = em.make_lt( y, x );
        main_module->add_localDef(define, new Define(main_expr, define, test_expr));

        LtTestWalker ltw(CuddMgr::INSTANCE());
        ltw(f_compiler.process( main_expr, define, 0));
    }

    {
        Atom a_d("d_le_1"); Expr_ptr define = em.make_identifier(a_d);

        /* y <= x */
        Expr_ptr test_expr = em.make_le( y, x );
        main_module->add_localDef(define, new Define(main_expr, define, test_expr));

        LeTestWalker lew(CuddMgr::INSTANCE());
        lew(f_compiler.process( main_expr, define, 0));
    }

    {
        Atom a_d("d_gt_1"); Expr_ptr define = em.make_identifier(a_d);

        /* y > x */
        Expr_ptr test_expr = em.make_gt( y, x );
        main_module->add_localDef(define, new Define(main_expr, define, test_expr));

        GtTestWalker gtw(CuddMgr::INSTANCE());
        gtw(f_compiler.process( main_expr, define, 0));
    }

    {
        Atom a_d("d_ge_1"); Expr_ptr define = em.make_identifier(a_d);

        /* y >= x */
        Expr_ptr test_expr = em.make_ge( y, x );
        main_module->add_localDef(define, new Define(main_expr, define, test_expr));

        GeTestWalker gew(CuddMgr::INSTANCE());
        gew(f_compiler.process( main_expr, define, 0));
    }

}

BOOST_AUTO_TEST_SUITE_END()

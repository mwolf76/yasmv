#define BOOST_TEST_DYN_LINK
#include <boost/test/unit_test.hpp>

#include <expr.hh>
#include <expr_mgr.hh>
#include <expr_printer.hh>

#include <model.hh>
#include <model_mgr.hh>

#include <compilers/be_compiler.hh>

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

        /* true otherwise */
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
    PlusTestWalker(CuddMgr& owner)
        : TestWalker(owner)
    {}

    virtual void action(value_t value)
    {
        BOOST_CHECK(1 == value); /* 0-1 ADDs */

        value_t msb = msb_value();
        value_t lsb = lsb_value();

        BOOST_CHECK(msb == (1 + lsb) % 256);
    }
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

BOOST_AUTO_TEST_SUITE(tests)
BOOST_AUTO_TEST_CASE(compiler_plus)
{
    ModelMgr& mm(ModelMgr::INSTANCE());
    ExprMgr& em(ExprMgr::INSTANCE());
    TypeMgr& tm(TypeMgr::INSTANCE());

    BECompiler f_compiler;

    Expr_ptr main_expr(em.make_main());
    IModule_ptr main_module = new Module( main_expr );
    Type_ptr u2 = tm.find_unsigned(2);

    Atom a_x("x"); Expr_ptr x = em.make_identifier(a_x);
    main_module->add_localVar(x, new StateVar(main_expr, x, u2));

    Atom a_y("y"); Expr_ptr y = em.make_identifier(a_y);
    main_module->add_localVar(y, new StateVar(main_expr, y, u2));

    mm.model()->add_module(main_expr, main_module);

    // {
    //     Atom a_d("d_plus"); Expr_ptr define = em.make_identifier(a_d);

    //     /* y := x + 1 */
    //     Expr_ptr test_expr = em.make_eq( y, em.make_add( x, em.make_one()));

    //     main_module->add_localDef(define, new Define(main_expr, define, test_expr));
    //     PlusTestWalker ptw(CuddMgr::INSTANCE());

    //     ptw(f_compiler.process( main_expr, define, 0));
    // }

    {
        Atom a_d("d_neg"); Expr_ptr define = em.make_identifier(a_d);

        /* y := - x */
        Expr_ptr test_expr = em.make_eq( y, em.make_neg( x ));
        main_module->add_localDef(define, new Define(main_expr, define, test_expr));

        NegTestWalker ntw(CuddMgr::INSTANCE());
        ntw(f_compiler.process( main_expr, define, 0));
    }

}

BOOST_AUTO_TEST_SUITE_END()

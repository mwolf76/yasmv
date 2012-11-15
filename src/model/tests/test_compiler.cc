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

        /* logical zero */
        if (node == Cudd_Not(f_owner.dd().getManager()->one)) {
            return false;
        }

        /* true otherwise */
        return true;
    }

    virtual void action(value_t value) =0;

protected:
    value_t pow2(unsigned exp)
    {
        value_t res = 1;
        for (unsigned i = exp; i; -- i) {
            res *= 2;
        }

        return res;
    }

    value_t bits2value()
    {
        long i, res = 0;
        char *data = f_data;

        for (i = pow2(f_owner.dd().getManager()->size -1); i; i /= 2) {
            if ( *data == 1 ) res += i;
            else if (*data == 0) ;
            else assert(0); // unexpected

        ++ data;
        }

        return res;
    }

};

// a decent abstraction :-)
class PlusTestWalker : public TestWalker {
public:
    PlusTestWalker(CuddMgr& owner)
        : TestWalker(owner)
    {}

    virtual void action(value_t value)
    {
        BOOST_CHECK(value == 1 + bits2value());
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

    Atom a_d("d"); Expr_ptr define = em.make_identifier(a_d);

    /* y := x + 1 */
    Expr_ptr test_expr = em.make_eq( y, em.make_add( x, em.make_one()));

    main_module->add_localDef(define, new Define(main_expr, define, test_expr));
    mm.model()->add_module(main_expr, main_module);

    PlusTestWalker ptw(CuddMgr::INSTANCE());
    ptw(f_compiler.process( main_expr, define, 0));
}

BOOST_AUTO_TEST_SUITE_END()

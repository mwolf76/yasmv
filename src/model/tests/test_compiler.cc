#define BOOST_TEST_DYN_LINK
#include <boost/test/unit_test.hpp>

#include <expr.hh>
#include <expr_mgr.hh>
#include <expr_printer.hh>

#include <model.hh>
#include <model_mgr.hh>

#include <compiler.hh>

#include <sat/terms/ddterms.hh>
using Minisat::DDTermFactory;

class DDPlusInspector : public IObject {
public:

    void callback(int *list, int size);
};


// 8 bits
long byte2int(int *data)
{
    long i, res = 0;

    for (i = 128; i; i /= 2) {
        if ( *data == 1 ) res += i;
        else if (*data == 0) ;
        else assert(0); // ???

        ++ data;
    }

    return res;
}

void DDPlusInspector::callback(int *list, int size)
{
    assert(16 == size);

    /* LHS = bits 0..7 */
    long lhs = byte2int(list);

    /* RHS = bits 8..15 */
    long rhs = byte2int(list + 8);

    BOOST_CHECK( lhs == rhs + 1 );
}

void test_plus_minterm_bridge(void *obj, int *list, int size)
{
    assert(obj);
    DDPlusInspector *inst = reinterpret_cast<DDPlusInspector *>(obj);

    inst->callback(list, size);
}

BOOST_AUTO_TEST_SUITE(tests)
BOOST_AUTO_TEST_CASE(compiler_plus)
{
    ModelMgr& mm(ModelMgr::INSTANCE());
    ExprMgr& em(ExprMgr::INSTANCE());
    TypeMgr& tm(TypeMgr::INSTANCE());

    DDTermFactory f_factory(CuddMgr::INSTANCE().dd());

    BECompiler f_compiler;

    Expr_ptr main_expr(em.make_main());
    IModule_ptr main_module = new Module( main_expr );
    Type_ptr u4 = tm.find_unsigned(4);

    Atom a_x("x"); Expr_ptr x = em.make_identifier(a_x);
    main_module->add_localVar(x, new StateVar(main_expr, x, u4));

    Atom a_y("y"); Expr_ptr y = em.make_identifier(a_y);
    main_module->add_localVar(y, new StateVar(main_expr, y, u4));

    mm.model()->add_module(main_expr, main_module);

    {
        Expr_ptr expr = em.make_ge( em.make_add( x, em.make_one()), em.make_zero());
        ADD add = f_compiler.process( main_expr, expr, 0);
        f_factory.walk_ones(add, this, test_plus_minterm_bridge);
    }

    // {
    //     Expr_ptr expr = em.make_add( em.make_one(), x);
    //     ADD add = f_compiler.process( main_expr, expr, 0);
    //     f_factory.walk_ones(add, this, test_plus_minterm_bridge);
    // }

    // {
    //     Expr_ptr expr = em.make_add( x, y );
    //     ADD add = f_compiler.process( main_expr, expr, 0);
    //     f_factory.walk_ones(add, this, test_plus_minterm_bridge);
    // }

}

BOOST_AUTO_TEST_SUITE_END()

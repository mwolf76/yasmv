#include "model_fixture.hh"

#include <expr/expr_mgr.hh>

#include <model/model.hh>
#include <model/model_mgr.hh>
#include <model/module.hh>

#include <opts/opts_mgr.hh>

#include <type/type_mgr.hh>

static bool build_model()
{
    model::ModelMgr& mm { model::ModelMgr::INSTANCE() };
    expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };
    type::TypeMgr& tm { type::TypeMgr::INSTANCE() };

    /* set word width to 16 bits */
    opts::OptsMgr::INSTANCE().set_word_width(16);

    model::Module& main {
        *new model::Module(em.make_identifier("main"))
    };
    mm.model().add_module(main);

    type::Type_ptr boolean { tm.find_boolean() };
    type::Type_ptr uint16 { tm.find_unsigned(16) };
    type::Type_ptr int16 { tm.find_signed(16) };

    const std::pair<const char*, type::Type_ptr> vars[] {
        { "x", boolean },
        { "y", boolean },
        { "s", uint16 },
        { "t", uint16 },
        { "u", int16 },
        { "v", int16 },
    };

    for (const auto& [name, type] : vars) {
        expr::Expr_ptr id { em.make_identifier(name) };
        main.add_var(id, new symb::Variable(main.name(), id, type));
    }

    return mm.analyze();
}

ModelFixture::ModelFixture()
{
    expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };

    x = em.make_identifier("x");
    y = em.make_identifier("y");
    s = em.make_identifier("s");
    t = em.make_identifier("t");
    u = em.make_identifier("u");
    v = em.make_identifier("v");

    static const bool once { build_model() };
    analyzed = once;
}

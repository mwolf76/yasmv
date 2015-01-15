/**
 *  @file Base Algorithm.cc
 *  @brief Base Algorithm
 *
 *  Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU Lesser General Public
 *  License as published by the Free Software Foundation; either
 *  version 2.1 of the License, or (at your option) any later version.
 *
 *  This library is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public
 *  License along with this library; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/
#include <vector>

#include <base.hh>

Algorithm::Algorithm(Command& command, Model& model)
    : f_command(command)
    , f_model(model)
    , f_mm(ModelMgr::INSTANCE())
    , f_bm(EncodingMgr::INSTANCE())
    , f_em(ExprMgr::INSTANCE())
    , f_tm(TypeMgr::INSTANCE())
    , f_witness(NULL)
{
    set_param("alg_name", "test");
    DEBUG
        << "Creating algorithm instance "
        << get_param("alg_name")
        << " @" << this
        << std::endl;
}

Algorithm::~Algorithm()
{
    DEBUG
        << "Destroying algorithm instance "
        << get_param("alg_name")
        << " @" << this
        << std::endl;
}

void Algorithm::set_param(std::string key, Variant value)
{ f_params [ key ] = value; }

Variant& Algorithm::get_param(const std::string key)
{
    const ParametersMap::iterator eye = f_params.find(key);

    if (eye != f_params.end()) {
        return (*eye).second;
    }

    else return NilValue;
}

void Algorithm::setup()
{
#if 0
    Compiler& cmpl(compiler()); // just a local ref

    ExprMgr& em (ExprMgr::INSTANCE());
    ModelMgr& mm (ModelMgr::INSTANCE());

    Model& model(f_model);
    const Modules& modules = model.modules();
    Expr_ptr main_module = em.make_main();

    Modules::const_iterator main_iter = modules.find(main_module);

    if (modules.end() == main_iter)
        throw ModuleNotFound(main_module);

    Module_ptr main_ = main_iter -> second;

    DEBUG
        << "Compiling FSM..."
        << std::endl;

    std::stack< Expr_ptr > stack;
    stack.push( em.make_empty());

    // recursive walk of model, starting from main module
    while (0 < stack.size()) {
    {
        Expr_ptr ctx (stack.top());
        Module& module (mm.scope( ContextKey( curr_module, ctx)));

        /* INIT */
        const ExprVector init = module.init();
        for (ExprVector::const_iterator init_eye = init.begin(); init_eye != init.end(); ++ init_eye)
            f_init.push_back( cmpl.process(ctx, *init_eye));

        /* INVAR */
        const ExprVector invar = module.invar();
        for (ExprVector::const_iterator invar_eye = invar.begin(); invar_eye != invar.end(); ++ invar_eye)
            f_invar.push_back( cmpl.process(ctx, *invar_eye));

        /* TRANS */
        const ExprVector trans = module.trans();
        for (ExprVector::const_iterator trans_eye = trans.begin(); trans_eye != trans.end(); ++ trans_eye)
            f_trans.push_back( cmpl.process(ctx, *trans_eye));

        /* recursively visit child modules */
        Variables attrs ( module -> vars());
        for (vi = attrs.begin(); attrs.end() != vi; ++ vi) {
            Variable& var (* vi -> second);
            Type_ptr vtype (var.type());

            if (vtype -> is_instance()) {
                InstanceType_ptr instance = vtype -> as_instance();

                Expr_ptr module_name (instance -> name());
                Module_ptr inst_module( & model.module(module_name));


            }
        }
    }
#endif
}

void Algorithm::assert_fsm_init(Engine& engine, step_t time, group_t group)
{
    unsigned n = f_init.size();
    DEBUG
        << "CNFizing INIT @" << time
        << "... (" << n << " fragments)"
        << std::endl;

    clock_t t0 = clock();

    CompilationUnits::const_iterator i;
    for (i = f_init.begin(); f_init.end() != i; ++ i) {
        engine.push( *i, time, group);
    }

    clock_t elapsed = clock() - t0;
    double secs = (double) elapsed / (double) CLOCKS_PER_SEC;
    DEBUG
        << "Done. (took " << secs << " seconds)"
        << std::endl;
}

void Algorithm::assert_fsm_invar(Engine& engine, step_t time, group_t group)
{
    unsigned n = f_invar.size();
    DEBUG
        << "CNFizing INVAR @" << time
        << "... (" << n << " fragments)"
        << std::endl;

    clock_t t0 = clock();

    CompilationUnits::const_iterator i;
    for (i = f_invar.begin(); f_invar.end() != i; ++ i) {
        engine.push( *i, time, group);
    }

    clock_t elapsed = clock() - t0;
    double secs = (double) elapsed / (double) CLOCKS_PER_SEC;
    DEBUG
        << "Done. (took " << secs << " seconds)"
        << std::endl;
}

void Algorithm::assert_fsm_trans(Engine& engine, step_t time, group_t group)
{
    unsigned n = f_trans.size();
    DEBUG
        << "CNFizing TRANS @" << time
        << "... (" << n << " fragments)"
        << std::endl;

    clock_t t0 = clock();

    CompilationUnits::const_iterator i;
    for (i = f_trans.begin(); f_trans.end() != i; ++ i) {
        engine.push( *i, time, group);
    }

    clock_t elapsed = clock() - t0;
    double secs = (double) elapsed / (double) CLOCKS_PER_SEC;
    DEBUG
        << "Done. (took " << secs << " seconds)"
        << std::endl;
}

void Algorithm::assert_fsm_uniqueness(Engine& engine, step_t j, step_t k, group_t group)
{
    SymbIter symbs( model(), NULL ); // no COI support yet

    clock_t t0 = clock();
    DEBUG
        << "CNFizing uniqueness(" << j << ", " << k << ")"
        << std::endl;

    typedef std::vector<Var> Vars;
    Vars uniqueness_vars;

    /* define uniqueness_vars into the solver ... */
    while (symbs.has_next()) {
        Symbol_ptr symb = symbs.next();

        if (symb->is_variable()) {

            Variable& var (symb->as_variable());
            if (! var.input() && ! var.temp()) {

                Expr_ptr ctx  (var.ctx());
                Expr_ptr expr (var.expr());

                FQExpr key(ctx, expr);
                Encoding_ptr enc = f_bm.find_encoding(key);

                DDVector::const_iterator di;
                unsigned ndx;
                for (ndx = 0, di = enc->bits().begin();
                     enc->bits().end() != di; ++ ndx, ++ di) {

                    unsigned bit = (*di).getNode()->index;

                    const UCBI& ucbi = f_bm.find_ucbi(bit);
                    const TCBI& jtcbi = TCBI(ucbi.ctx(), ucbi.expr(),
                                             ucbi.time(), ucbi.bitno(), j);
                    const TCBI& ktcbi = TCBI(ucbi.ctx(), ucbi.expr(),
                                             ucbi.time(), ucbi.bitno(), k);

                    Var jkne = engine.new_sat_var();
                    uniqueness_vars.push_back(jkne);

                    Var jvar = engine.tcbi_to_var(jtcbi);
                    Var kvar = engine.tcbi_to_var(ktcbi);

                    {
                        vec<Lit> ps;
                        ps.push( mkLit( jkne, true));
                        ps.push( mkLit( jvar, true));
                        ps.push( mkLit( kvar, true));

                        DRIVEL
                            << ps
                            << std::endl;

                        engine.add_clause(ps);
                    }

                    {
                        vec<Lit> ps;
                        ps.push( mkLit( jkne, true));
                        ps.push( mkLit( jvar, true));
                        ps.push( mkLit( kvar, true));

                        DRIVEL
                            << ps
                            << std::endl;

                        engine.add_clause(ps);
                    }
                }
            }
        }
    }

    // ... and then assert at least one of them is true
    vec<Lit> ps;
    ps.push( mkLit( group, true));

    for (Vars::iterator eye = uniqueness_vars.begin();
         eye != uniqueness_vars.end(); ++ eye) {
        ps.push( mkLit( *eye, false));
    }

    DRIVEL
        << ps
        << std::endl;

    engine.add_clause(ps);

    clock_t elapsed = clock() - t0;
    double secs = (double) elapsed / (double) CLOCKS_PER_SEC;
    DEBUG
        << "Done. (took " << secs << " seconds)"
        << std::endl;
}

void Algorithm::assert_formula(Engine& engine, step_t time, CompilationUnit& term, group_t group)
{
    clock_t t0 = clock();
    DEBUG
        << "CNFizing formula @" << time << " ..."
        << std::endl;

    engine.push( term, time, group);

    clock_t elapsed = clock() - t0;
    double secs = (double) elapsed / (double) CLOCKS_PER_SEC;
    DEBUG
        << "Done. (took " << secs << " seconds)"
        << std::endl;
}



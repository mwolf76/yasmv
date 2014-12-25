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
#include <base.hh>

Algorithm::Algorithm(IModel& model)
    : f_model(model)
    , f_mm(ModelMgr::INSTANCE())
    , f_em(ExprMgr::INSTANCE())
    , f_tm(TypeMgr::INSTANCE())
    , f_engine(* new SAT())
    , f_witness(NULL)
{
    set_param("alg_name", "test");
    DEBUG  << "Creating algorithm instance "
           << get_param("alg_name")
           << " @" << this
           << endl;
}

Algorithm::~Algorithm()
{
    DEBUG << "Destroying algorithm instance "
          << get_param("alg_name")
          << " @" << this
          << endl;

    delete & f_engine;
}

void Algorithm::set_param(string key, Variant value)
{ f_params [ key ] = value; }

Variant& Algorithm::get_param(const string key)
{
    const ParametersMap::iterator eye = f_params.find(key);

    if (eye != f_params.end()) {
        return (*eye).second;
    }

    else return NilValue;
}

void Algorithm::prepare()
{
    Compiler& cmpl(compiler()); // just a local ref
    const Modules& modules = f_model.modules();
    for (Modules::const_iterator m = modules.begin();
         m != modules.end(); ++ m) {

        Module& module = dynamic_cast <Module&> (*m->second);

        /* INIT */
        const ExprVector init = module.init();
        for (ExprVector::const_iterator init_eye = init.begin();
             init_eye != init.end(); ++ init_eye) {

            Expr_ptr ctx = module.expr();
            Expr_ptr body = (*init_eye);

            cmpl.preprocess(ctx, body);
        }

        /* INVAR */
        const ExprVector invar = module.invar();
        for (ExprVector::const_iterator invar_eye = invar.begin();
             invar_eye != invar.end(); ++ invar_eye) {

            Expr_ptr ctx = module.expr();
            Expr_ptr body = (*invar_eye);

            cmpl.preprocess(ctx, body);
        }

        /* TRANS */
        const ExprVector trans = module.trans();
        for (ExprVector::const_iterator trans_eye = trans.begin();
             trans_eye != trans.end(); ++ trans_eye) {

            Expr_ptr ctx = module.expr();
            Expr_ptr body = (*trans_eye);

            cmpl.preprocess(ctx, body);
        }
    }
} /* prepare() */

void Algorithm::compile()
{
    Compiler& cmpl(compiler()); // just a local ref
    const Modules& modules = f_model.modules();
    for (Modules::const_iterator m = modules.begin();
         m != modules.end(); ++ m) {

        Module& module = dynamic_cast <Module&> (*m->second);

        /* INIT */
        const ExprVector init = module.init();
        for (ExprVector::const_iterator init_eye = init.begin();
             init_eye != init.end(); ++ init_eye) {

            Expr_ptr ctx = module.expr();
            Expr_ptr body = (*init_eye);

            f_init.push_back( cmpl.process(ctx, body));
        }

        /* INVAR */
        const ExprVector invar = module.invar();
        for (ExprVector::const_iterator invar_eye = invar.begin();
             invar_eye != invar.end(); ++ invar_eye) {

            Expr_ptr ctx = module.expr();
            Expr_ptr body = (*invar_eye);

            f_invar.push_back( cmpl.process(ctx, body));
        }

        /* TRANS */
        const ExprVector trans = module.trans();
        for (ExprVector::const_iterator trans_eye = trans.begin();
             trans_eye != trans.end(); ++ trans_eye) {

            Expr_ptr ctx = module.expr();
            Expr_ptr body = (*trans_eye);

            f_trans.push_back( cmpl.process(ctx, body));
        }
    }
} /* compile() */

void Algorithm::assert_fsm_init(step_t time, group_t group)
{
    unsigned n = f_init.size();
    DEBUG << "CNFizing INIT @" << time
          << "... (" << n << " fragments)"
          << endl;

    clock_t t0 = clock();

    Terms::const_iterator i;
    for (i = f_init.begin(); f_init.end() != i; ++ i) {
        engine().push( *i, time, group);
    }

    clock_t elapsed = clock() - t0;
    double secs = (double) elapsed / (double) CLOCKS_PER_SEC;
    DEBUG << "Done. (took " << secs << " seconds)" << endl;
}

void Algorithm::assert_fsm_invar(step_t time, group_t group)
{
    unsigned n = f_invar.size();
    DEBUG << "CNFizing INVAR @" << time
          << "... (" << n << " fragments)"
          << endl;

    clock_t t0 = clock();

    Terms::const_iterator i;
    for (i = f_invar.begin(); f_invar.end() != i; ++ i) {
        engine().push( *i, time, group);
    }

    clock_t elapsed = clock() - t0;
    double secs = (double) elapsed / (double) CLOCKS_PER_SEC;
    DEBUG << "Done. (took " << secs << " seconds)" << endl;
}

void Algorithm::assert_fsm_trans(step_t time, group_t group)
{
    unsigned n = f_trans.size();
    DEBUG << "CNFizing TRANS @" << time
          << "... (" << n << " fragments)"
          << endl;

    clock_t t0 = clock();

    Terms::const_iterator i;
    for (i = f_trans.begin(); f_trans.end() != i; ++ i) {
        engine().push( *i, time, group);
    }

    clock_t elapsed = clock() - t0;
    double secs = (double) elapsed / (double) CLOCKS_PER_SEC;
    DEBUG << "Done. (took " << secs << " seconds)" << endl;
}

void Algorithm::assert_formula(step_t time, Term& term, group_t group)
{ engine().push( term, time, group); }

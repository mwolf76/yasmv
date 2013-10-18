/**
 *  @file model_mgr.cc
 *  @brief Model module (ModelMgr class)
 *
 *  This module contains definitions and services that implement an
 *  optimized storage for expressions. Expressions are stored in a
 *  Directed Acyclic Graph (DAG) for data sharing.
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

#include <model_mgr.hh>
#include <type_exceptions.hh>


// static initialization
ModelMgr_ptr ModelMgr::f_instance = NULL;

ModelMgr::ModelMgr()
    : f_model()
    , f_em(ExprMgr::INSTANCE())
    , f_tm(TypeMgr::INSTANCE())
    , f_resolver(* new ModelResolver(* this))
    , f_inferrer(* new Inferrer(* this))
{}

void ModelMgr::first_pass()
{
    /* nop */
}

void ModelMgr::second_pass()
{
    Model& model(f_model);
    const Modules& modules = model.modules();

    for (Modules::const_iterator mod_eye = modules.begin();
         mod_eye != modules.end(); mod_eye ++ ) {

        Module& module = dynamic_cast <Module&> (*mod_eye->second);
        DEBUG << "processing module '" << module << "' " << endl;

        // Remark: ctx name is MODULE name, not instance's
        // rationale: you may have several instances but they
        // all should refer to the same entry on the type map.
        Expr_ptr ctx = module.expr();

        // type inference: defines
        const Defines defines = module.defs();
        for (Defines::const_iterator define_eye = defines.begin();
             define_eye != defines.end(); define_eye ++) {

            Define& define = dynamic_cast <Define&> (*define_eye->second);

            Expr_ptr dname = define.expr();
            FQExpr fqdn(ctx, dname);

            Expr_ptr dbody = define.body();
            FQExpr fqdb(ctx, dbody);

            // try to infer type
            try {
                Type_ptr tmp = type(fqdb);
            }
            catch (AnalyzerException& ae) {
                cerr << "DEFINE " << fqdn << endl
                     << ae.what() << endl;
            }
        } // for defines

        // type inference: FSM
        const ExprVector init = module.init();
        for (ExprVector::const_iterator init_eye = init.begin();
             init_eye != init.end(); init_eye ++) {

            Expr_ptr body = (*init_eye);
            FQExpr fqdn(ctx, body);

            DEBUG << "processing INIT " << fqdn << endl;

            try {
                f_inferrer.process(ctx, body);
            }
            catch (AnalyzerException& ae) {
                cerr << "INIT " << fqdn << endl
                     << ae.what() << endl;
            }

        } // for init

        const ExprVector trans = module.trans();
        for (ExprVector::const_iterator trans_eye = trans.begin();
             trans_eye != trans.end(); trans_eye ++) {

            Expr_ptr body = (*trans_eye);
            FQExpr fqdn(ctx, body);
            DEBUG << "processing TRANS " << fqdn << endl;

            try {
                f_inferrer.process(ctx, body);
            }
            catch (AnalyzerException& ae) {
                cerr << "TRANS " << fqdn << endl
                     << ae.what() << endl;
            }
        }
    }
}

void ModelMgr::analyze()
{
    DEBUG << "-- first pass (binding)" << endl;
    // (binding) For each module m in M, A goes deep in the module
    // defs. Every variable decl is resolved either to a native type
    // (boolean, ranged int, ...) or to an instance. Due to (1) all
    // modules are defined so any unresolved symbol at this point is a
    // fatal. Native types are taken care of as well.
    first_pass();

    DEBUG << "-- second pass (type checking)" << endl;
    // (typechecking) For each module m in M, A inspects FSM exprs:
    // INVAR, TRANS, FAIRNESS have all to be boolean formulae; ASSIGNs
    // have to match lvalue type. The type for every expression is
    // inferred using the lazy walker strategy.
    second_pass();
}


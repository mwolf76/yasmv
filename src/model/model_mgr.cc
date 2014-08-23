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

#include <symbol.hh>
#include <model_mgr.hh>

// static initialization
ModelMgr_ptr ModelMgr::f_instance = NULL;

ModelMgr::ModelMgr()
    : f_model()
    , f_em(ExprMgr::INSTANCE())
    , f_tm(TypeMgr::INSTANCE())
    , f_resolver(* new ModelResolver(* this))
    , f_preprocessor(* new Preprocessor(* this))
    , f_inferrer(* new Inferrer(* this))
{}

// ResolutionException::ResolutionException(Expr_ptr expr)
//     : f_expr(expr)
// {}

// const char* ResolutionException::what() const throw()
// {
//     ostringstream oss;

//     oss << "UnresolvedSymbol: " << f_expr;
//     return oss.str().c_str();
// }


void ModelMgr::first_pass()
{
    DEBUG << "Not yet implemented" << endl;
}

void ModelMgr::second_pass()
{
    Model& model(f_model);
    const Modules& modules = model.modules();

    for (Modules::const_iterator mi = modules.begin(); mi != modules.end(); ++ mi ) {

        Module& module = dynamic_cast <Module&> (*mi->second);
        DEBUG << "processing module '" << module << "' " << endl;

        // Remark: ctx name is MODULE name, not instance's
        // rationale: you may have several instances but they
        // all should refer to the same entry on the type map.
        Expr_ptr ctx = module.expr();

        // type inference: FSM
        const ExprVector& init = module.init();
        for (ExprVector::const_iterator ii = init.begin(); ii != init.end(); ++ ii ) {

            Expr_ptr body = (*ii);

            FQExpr fqdn(ctx, body);
            DEBUG << "processing INIT " << fqdn << endl;

            try {
                f_inferrer.process(body, ctx);
            }
            catch (Exception& ae) {
                cerr << ae.what()
                     << endl
                     << "  in INIT "
                     << fqdn << endl;
                f_status = false;
            }
        } // for init

        const ExprVector& invar = module.invar();
        for (ExprVector::const_iterator ii = invar.begin(); ii != invar.end(); ++ ii ) {

            Expr_ptr body = (*ii);

            FQExpr fqdn(ctx, body);
            DEBUG << "processing INVAR " << fqdn << endl;

            try {
                f_inferrer.process(body, ctx);
            }
            catch (Exception& ae) {
                cerr << ae.what()
                     << endl
                     << "  in INVAR "
                     << fqdn << endl;
                f_status = false;
            }
        } // for invar

        const ExprVector& trans = module.trans();
        for (ExprVector::const_iterator ti = trans.begin(); ti != trans.end(); ++ ti ) {

            Expr_ptr body = (*ti);

            FQExpr fqdn(ctx, body);
            DEBUG << "processing TRANS " << fqdn << endl;

            try {
                f_inferrer.process(body, ctx);
            }
            catch (Exception& ae) {
                cerr << ae.what()
                     << endl
                     << "  in TRANS "
                     << fqdn << endl;
                f_status = false;
            }
        } // for trans

        const Defines& defs = module.defs();
        for (Defines::const_iterator di = defs.begin(); di != defs.end(); ++ di ) {
            FQExpr fqdn = (*di).first;
            Expr_ptr body = (*di).second -> body();

            DEBUG << "processing DEFINE " << fqdn << endl;

            try {
                f_inferrer.process(body, ctx);
            }
            catch (Exception& ae) {
                cerr << ae.what()
                     << endl
                     << "  in DEFINE "
                     << fqdn << endl;
                f_status = false;
            }
        } // for defines

    } // for module
}

bool ModelMgr::analyze()
{
    f_status = true;

    DEBUG << "-- first pass (binding)" << endl;
    // (binding) For each module m in M, A goes deep in the module
    // defs. Every variable decl is resolved either to a native type
    // (boolean, ranged int, ...) or to an instance. Due to (1) all
    // modules are defined so any unresolved symbol at this point is a
    // fatal. Native types are taken care of as well.
    first_pass();
    if (! f_status) return false;

    DEBUG << "-- second pass (type checking)" << endl;
    // (typechecking) For each module m in M, A inspects FSM exprs:
    // INVAR, TRANS, FAIRNESS have all to be boolean formulae; ASSIGNs
    // have to match lvalue type. The type for every expression is
    // inferred using the lazy walker strategy.
    second_pass();
    if (! f_status) return false;

    return true;
}


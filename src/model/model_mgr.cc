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

#include <symb/symbol.hh>

#include <model/model_mgr.hh>

// static initialization
ModelMgr_ptr ModelMgr::f_instance = NULL;

ModelMgr::ModelMgr()
    : f_model()
    , f_em(ExprMgr::INSTANCE())
    , f_tm(TypeMgr::INSTANCE())
    , f_resolver(* new ModelResolver(* this))
    , f_preprocessor(* new Preprocessor(* this))
    , f_type_checker(* new TypeChecker(* this))
{}

void ModelMgr::first_pass()
{
    ExprMgr& em (ExprMgr::INSTANCE());
    Model& model(f_model);
    const Modules& modules = model.modules();
    Modules::const_iterator main_iter = modules.find(em.make_main());

    if (modules.end() == main_iter)
        throw ModuleNotFound( em.make_main());

    typedef std::stack<Module_ptr> ModuleStack;
    ModuleStack module_stack;
    module_stack.push( main_iter->second );

    typedef std::stack<Expr_ptr> ExprStack;
    ExprStack params_stack;
    params_stack.push( ExprMgr::INSTANCE().make_empty());

    // recursive walk of all var decls, starting from main module
    while (0 < module_stack.size()) {

        assert( module_stack.size() == params_stack.size());
        Module_ptr mi = module_stack.top(); module_stack.pop();
        assert( mi );

        Expr_ptr   ei = params_stack.top(); params_stack.pop();
        assert( ei );

        Module& module( *mi ); Variables vars ( module.vars());
        Expr_ptr params( ei ); (void) params;

        Variables::const_iterator vi;
        for (vi = vars.begin(); vars.end() != vi; ++ vi) {
            FQExpr fqdn (vi -> first);
            Variable& var (* vi -> second);
            Type_ptr vtype (var.type());

            DEBUG
                << "processing var `" << fqdn << "`, "
                << "type " << vtype
                << std::endl;

            if (vtype -> is_instance()) {
                InstanceType_ptr instance (vtype -> as_instance());

                Module& instance_module ( model.module( instance -> name()));
                module_stack.push( &instance_module );

                Expr_ptr instance_params( instance -> params());
                params_stack.push( instance_params );
            }
        }
    }
}

void ModelMgr::second_pass()
{
    Model& model(f_model);
    const Modules& modules = model.modules();

    for (Modules::const_iterator mi = modules.begin(); mi != modules.end(); ++ mi ) {

        Module& module = * mi->second;
        DEBUG
            << "processing module `" << module << "` "
            << std::endl;

        // Remark: ctx name is MODULE name, not instance's
        // rationale: you may have several instances but they
        // all should refer to the same entry on the type map.
        Expr_ptr ctx = module.name();

        const ExprVector& init = module.init();
        for (ExprVector::const_iterator ii = init.begin(); ii != init.end(); ++ ii ) {

            Expr_ptr body = (*ii);

            FQExpr fqdn(ctx, body);
            DEBUG
                << "processing INIT " << fqdn
                << std::endl;

            try {
                f_type_checker.process(body, ctx);
            }
            catch (Exception& ae) {
                std::string tmp(ae.what());
                WARN
                    << tmp
                    << std::endl
                    << "  in INIT "
                    << fqdn
                    << std::endl;

                f_status = false;
            }
        } // for init

        const ExprVector& invar = module.invar();
        for (ExprVector::const_iterator ii = invar.begin(); ii != invar.end(); ++ ii ) {

            Expr_ptr body = (*ii);

            FQExpr fqdn(ctx, body);
            DEBUG
                << "processing INVAR " << fqdn
                << std::endl;

            try {
                f_type_checker.process(body, ctx);
            }
            catch (Exception& ae) {
                std::string tmp (ae.what());
                WARN
                    << tmp
                    << std::endl
                    << "  in INVAR "
                    << fqdn
                    << std::endl;

                f_status = false;
            }
        } // for invar

        const ExprVector& trans = module.trans();
        for (ExprVector::const_iterator ti = trans.begin(); ti != trans.end(); ++ ti ) {

            Expr_ptr body = (*ti);

            FQExpr fqdn(ctx, body);
            DEBUG
                << "processing TRANS " << fqdn
                << std::endl;

            try {
                f_type_checker.process(body, ctx);
            }
            catch (Exception& ae) {
                std::string tmp(ae.what());
                WARN
                    << tmp
                    << std::endl
                    << "  in TRANS "
                    << fqdn
                    << std::endl;

                f_status = false;
            }
        } // for trans

        const Defines& defs = module.defs();
        for (Defines::const_iterator di = defs.begin(); di != defs.end(); ++ di ) {
            FQExpr fqdn = (*di).first;
            Expr_ptr body = (*di).second -> body();

            DEBUG
                << "processing DEFINE " << fqdn
                << std::endl;

            try {
                f_type_checker.process(body, ctx);
            }
            catch (Exception& ae) {
                std::string tmp (ae.what());
                WARN
                    << tmp
                    << std::endl
                    << "  in DEFINE "
                    << fqdn
                    << std::endl;

                f_status = false;
            }

        } // for defines

    } // for module
}

bool ModelMgr::analyze()
{
    f_status = true;

    DEBUG
        << "-- first pass (binding)"
        << std::endl;

    // (binding) For each module m in M, A goes deep in the module
    // defs. Every variable decl is resolved either to a native type
    // (boolean, ranged int, ...) or to an instance. Due to (1) all
    // modules are defined so any unresolved symbol at this point is a
    // fatal. Native types are taken care of as well.
    first_pass();
    if (! f_status)
        return false;

    DEBUG
        << "-- second pass (type checking)"
        << std::endl;

    // (typechecking) For each module m in M, inspect FSM exprs:
    // INITs, INVARs and TRANSes have all to be boolean formulas;
    second_pass();
    if (! f_status)
        return false;

    return true;
}


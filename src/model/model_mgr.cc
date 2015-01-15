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
{
}

void ModelMgr::register_scope(const std::pair< Expr_ptr, Module_ptr >& pair)
{
    Expr_ptr key (pair.first);
    Expr_ptr tgt (pair.second -> name());

    DEBUG
        << "Registering scope "
        << "`" << key << "`"
        << " :: " << tgt
        << std::endl;

    f_context_map.insert( pair );
}

Module_ptr ModelMgr::scope(Expr_ptr key)
{
    DEBUG
        << "Resolving scope `" << key << "` "
        << std::endl;

    ContextMap::const_iterator mi = f_context_map.find( key );
    assert( f_context_map.end() != mi );

    return mi -> second;
}

/* Build Context map by DFS traversal */
void ModelMgr::first_pass()
{
    ExprMgr& em (ExprMgr::INSTANCE());

    Model& model(f_model);
    const Modules& modules = model.modules();
    Expr_ptr main_module = em.make_main();

    Modules::const_iterator main_iter = modules.find(main_module);

    if (modules.end() == main_iter)
        throw ModuleNotFound(main_module);

    Module& main_ = *main_iter -> second;

    std::stack< std::pair<Expr_ptr, Module_ptr> > stack;
    stack.push( std::make_pair< Expr_ptr, Module_ptr >
                (em.make_empty(), &main_));

    /* walk of var decls, starting from main module */
    while (0 < stack.size()) {

        const std::pair< Expr_ptr, Module_ptr > top (stack.top()); stack.pop();

        /* register context resolution */
        register_scope( top );

        Expr_ptr ctx ( top.first );
        Module& module ( * top.second );

        Variables attrs (module.vars());
        Variables::const_iterator vi;
        for (vi = attrs.begin(); attrs.end() != vi; ++ vi) {

            Expr_ptr id( vi -> first.expr());

            Variable& var (* vi -> second);
            Type_ptr vtype (var.type());

            Expr_ptr local_ctx (em.make_dot( ctx, id));

            DRIVEL
                << "processing var `" << local_ctx << "`, "
                << "type " << vtype
                << std::endl;

            if (vtype -> is_instance()) {
                InstanceType_ptr instance = vtype -> as_instance();
                Module&  module( model.module(instance -> name()));

                stack.push( std::make_pair< Expr_ptr, Module_ptr >
                            (local_ctx, &module));
            }
        }
    }
}

void ModelMgr::second_pass()
{
    ExprMgr& em (ExprMgr::INSTANCE());

    Model& model(f_model);
    const Modules& modules = model.modules();
    Expr_ptr main_module = em.make_main();

    Modules::const_iterator main_iter = modules.find(main_module);

    if (modules.end() == main_iter)
        throw ModuleNotFound(main_module);

    Module& main_ = *main_iter -> second;

    std::stack< std::pair<Expr_ptr, Module_ptr> > stack;
    stack.push( std::make_pair< Expr_ptr, Module_ptr >
                (em.make_empty(), &main_));

    /* walk of var decls, starting from main module */
    while (0 < stack.size()) {

        const std::pair< Expr_ptr, Module_ptr > top (stack.top()); stack.pop();

        Expr_ptr ctx ( top.first );
        Module& module ( * top.second );

        const ExprVector& init = module.init();
        for (ExprVector::const_iterator ii = init.begin(); ii != init.end(); ++ ii ) {

            Expr_ptr body = (*ii);
            DEBUG
                << "processing INIT "
                << ctx << "::" << body
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
                    << ctx << "::" << body
                    << std::endl;

                f_status = false;
            }
        } // for init

        const ExprVector& invar = module.invar();
        for (ExprVector::const_iterator ii = invar.begin(); ii != invar.end(); ++ ii ) {

            Expr_ptr body = (*ii);
            DEBUG
                << "processing INVAR "
                << ctx << "::" << body
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
                    << ctx << "::" << body
                    << std::endl;

                f_status = false;
            }
        } // for invar

        const ExprVector& trans = module.trans();
        for (ExprVector::const_iterator ti = trans.begin(); ti != trans.end(); ++ ti ) {

            Expr_ptr body = (*ti);
            DEBUG
                << "processing TRANS "
                << ctx << "::" << body
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
                    << ctx << "::" << body
                    << std::endl;

                f_status = false;
            }
        } // for trans

        const Defines& defs = module.defs();
        for (Defines::const_iterator di = defs.begin(); di != defs.end(); ++ di ) {

            Expr_ptr body = (*di).second -> body();
            DEBUG
                << "processing DEFINE "
                << ctx << "::" << body
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
                    << ctx << "::" << body
                    << std::endl;

                f_status = false;
            }

        } // for defines

        Variables attrs (module.vars());
        Variables::const_iterator vi;
        for (vi = attrs.begin(); attrs.end() != vi; ++ vi) {

            Expr_ptr id( vi -> first.expr());

            Variable& var (* vi -> second);
            Type_ptr vtype (var.type());

            Expr_ptr local_ctx (em.make_dot( ctx, id));

            if (vtype -> is_instance()) {
                InstanceType_ptr instance = vtype -> as_instance();
                Module&  module( model.module(instance -> name()));

                stack.push( std::make_pair< Expr_ptr, Module_ptr >
                            (local_ctx, &module));
            }
        }
    }
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


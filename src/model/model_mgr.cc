/**
 * @file model_mgr.cc
 * @brief Model management subsystem, Model Manager class implementation.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA
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
    , f_analyzer(* new Analyzer(* this))
    , f_type_checker(* new TypeChecker(* this))
    , f_analyzed(false)
{
}

Module_ptr ModelMgr::scope(Expr_ptr key)
{
    ContextMap::const_iterator mi
        (f_context_map.find( key ));
    assert( f_context_map.end() != mi );

    return mi -> second;
}

Expr_ptr ModelMgr::rewrite_parameter(Expr_ptr expr)
{
    ParamMap::const_iterator i
        (f_param_map.find(expr));
    assert(f_param_map.end() != i);

    return i->second;
}

bool ModelMgr::analyze_aux(analyzer_pass_t pass)
{
    ExprMgr& em
        (ExprMgr::INSTANCE());

    Model& model
        (f_model);

    Module& main_
        (model.main_module());

    std::stack< boost::tuple<Expr_ptr, Module_ptr, Expr_ptr> > stack;
    stack.push( boost::make_tuple< Expr_ptr, Module_ptr, Expr_ptr >
                (em.make_empty(), &main_, em.make_empty()));

    /* walk of var decls, starting from main module */
    while (0 < stack.size()) {

        boost::tuple< Expr_ptr, Module_ptr, Expr_ptr > top
            (stack.top()); stack.pop();

        if (MMGR_BUILD_CTX_MAP == pass) {
            Expr_ptr key
                (top.get<0>());
            Module_ptr tgt
                (top.get<1>());
            Expr_ptr tgt_name
                (tgt -> name());

            DRIVEL
                << "Registering scope "
                << "`" << key << "`"
                << " instance of `" << tgt_name << "`"
                << std::endl;

            f_context_map.insert( std::make_pair< Expr_ptr, Module_ptr >
                                  ( key, tgt ));
        }

        Expr_ptr curr_ctx
            (top.get<0>());
        Module& curr_module
            (* top.get<1>());
        Expr_ptr curr_params
            (top.get<2>());

        if (MMGR_ANALYZE == pass) {
            const ExprVector& init
                (curr_module.init());

            for (ExprVector::const_iterator ii = init.begin();
                 ii != init.end(); ++ ii ) {

                Expr_ptr body
                    (*ii);

                DEBUG
                    << "Analzying INIT "
                    << curr_ctx << "::" << body
                    << std::endl;

                try {
                    f_analyzer.process(body, curr_ctx);
                }
                catch (Exception& ae) {
                    std::string tmp
                        (ae.what());

                    WARN
                        << tmp
                        << std::endl
                        << "  in INIT "
                        << curr_ctx << "::" << body
                        << std::endl;

                    return false;
                }
            } // for init

            const ExprVector& invar = curr_module.invar();
            for (ExprVector::const_iterator ii = invar.begin();
                 ii != invar.end(); ++ ii ) {

                Expr_ptr body
                    (*ii);

                DEBUG
                    << "Analzying INVAR "
                    << curr_ctx << "::" << body
                    << std::endl;

                try {
                    f_analyzer.process(body, curr_ctx);
                }
                catch (Exception& ae) {
                    std::string tmp
                        (ae.what());

                    WARN
                        << tmp
                        << std::endl
                        << "  in INVAR "
                        << curr_ctx << "::" << body
                        << std::endl;

                    return false;
                }
            } // for invar

            const ExprVector& trans = curr_module.trans();
            for (ExprVector::const_iterator ti = trans.begin();
                 ti != trans.end(); ++ ti ) {

                Expr_ptr body
                    (*ti);

                DEBUG
                    << "Analzying TRANS "
                    << curr_ctx << "::" << body
                    << std::endl;

                try {
                    f_analyzer.process(body, curr_ctx);
                }
                catch (Exception& ae) {
                    std::string tmp
                        (ae.what());
                    WARN
                        << tmp
                        << std::endl
                        << "  in TRANS "
                        << curr_ctx << "::" << body
                        << std::endl;

                    return false;
                }
            } // for trans

            const Defines& defs
                (curr_module.defs());

            for (Defines::const_iterator di = defs.begin();
                 di != defs.end(); ++ di ) {

                Expr_ptr body
                    ((*di).second -> body());

                DEBUG
                    << "Analzying "
                    << curr_ctx << "::" << body
                    << std::endl;

                try {
                    f_analyzer.process(body, curr_ctx);
                }
                catch (Exception& ae) {
                    std::string tmp
                        (ae.what());

                    WARN
                        << tmp
                        << std::endl
                        << "  in DEFINE "
                        << curr_ctx << "::" << body
                        << std::endl;

                    return false;
                }
            } // for defines
        } /* MMGR_ANALYZE */

        else if (MMGR_TYPE_CHECK == pass) {
            const ExprVector& init
                (curr_module.init());

            for (ExprVector::const_iterator ii = init.begin();
                 ii != init.end(); ++ ii ) {

                Expr_ptr body
                    (*ii);

                DEBUG
                    << "Analzying INIT "
                    << curr_ctx << "::" << body
                    << std::endl;

                try {
                    f_analyzer.process(body, curr_ctx);
                }
                catch (Exception& ae) {
                    std::string tmp
                        (ae.what());

                    WARN
                        << tmp
                        << std::endl
                        << "  in INIT "
                        << curr_ctx << "::" << body
                        << std::endl;

                    return false;
                }
            } // for init

            const ExprVector& invar = curr_module.invar();
            for (ExprVector::const_iterator ii = invar.begin();
                 ii != invar.end(); ++ ii ) {

                Expr_ptr body
                    (*ii);

                DEBUG
                    << "Analzying INVAR "
                    << curr_ctx << "::" << body
                    << std::endl;

                try {
                    f_analyzer.process(body, curr_ctx);
                }
                catch (Exception& ae) {
                    std::string tmp
                        (ae.what());

                    WARN
                        << tmp
                        << std::endl
                        << "  in INVAR "
                        << curr_ctx << "::" << body
                        << std::endl;

                    return false;
                }
            } // for invar

            const ExprVector& trans = curr_module.trans();
            for (ExprVector::const_iterator ti = trans.begin();
                 ti != trans.end(); ++ ti ) {

                Expr_ptr body
                    (*ti);

                DEBUG
                    << "Analzying TRANS "
                    << curr_ctx << "::" << body
                    << std::endl;

                try {
                    f_analyzer.process(body, curr_ctx);
                }
                catch (Exception& ae) {
                    std::string tmp
                        (ae.what());
                    WARN
                        << tmp
                        << std::endl
                        << "  in TRANS "
                        << curr_ctx << "::" << body
                        << std::endl;

                    return false;
                }
            } // for trans

            const Defines& defs
                (curr_module.defs());

            for (Defines::const_iterator di = defs.begin();
                 di != defs.end(); ++ di ) {

                Expr_ptr body
                    ((*di).second -> body());

                DEBUG
                    << "Analzying "
                    << curr_ctx << "::" << body
                    << std::endl;

                try {
                    f_analyzer.process(body, curr_ctx);
                }
                catch (Exception& ae) {
                    std::string tmp
                        (ae.what());

                    WARN
                        << tmp
                        << std::endl
                        << "  in DEFINE "
                        << curr_ctx << "::" << body
                        << std::endl;

                    return false;
                }
            } // for defines
        } /* MMGR_TYPE_CHECK */

        Variables attrs
            (curr_module.vars());
        Variables::const_iterator vi;

        for (vi = attrs.begin(); attrs.end() != vi; ++ vi) {

            Expr_ptr var_name
               (vi -> first);

            Type_ptr var_tp
                ((* vi -> second).type());

            if (var_tp -> is_instance()) {
                InstanceType_ptr instance
                    (var_tp -> as_instance());
                Expr_ptr inner_ctx
                    (em.make_dot( curr_ctx, var_name));
                Expr_ptr inner_params
                    (instance -> params());
                Module&  module_
                    ( module(instance -> name()));

                stack.push( boost::make_tuple< Expr_ptr, Module_ptr, Expr_ptr >
                            (inner_ctx, &module_, inner_params));
            }
        }

        if (MMGR_BUILD_PARAM_MAP == pass) {

            // analyze_params( curr_module, curr_params );
            std::vector<Expr_ptr> actuals;

            // 1. in-order visit, build fwd expr stack
            std::stack<Expr_ptr> comma_stack;
            comma_stack.push( curr_params );

            while (0 < comma_stack.size()) {
                Expr_ptr top
                    (comma_stack.top());
                comma_stack.pop();

                if (f_em.is_params_comma( top)) {
                    comma_stack.push( top->rhs());
                    comma_stack.push( top->lhs());
                    continue;
                }

                if (! f_em.is_empty(top))
                    actuals.push_back( em.make_dot( em.make_empty(), top));
            }

            // 2. good, now associate formals and actuals
            const Parameters& formals
                (curr_module.parameters());

            if (actuals.size() != formals.size())
                throw BadParamCount( curr_module.name(), formals.size(), actuals.size());

            Parameters::const_iterator fi
                (formals.begin());

            std::vector<Expr_ptr>::const_iterator ai
                (actuals.begin());

            while (formals.end() != fi) {

                Expr_ptr formal
                    (em.make_dot( curr_ctx, ((* fi -> second).name())));

                Expr_ptr actual
                    (*ai);

                DEBUG
                    << "Mapping `"
                    << formal
                    << "` to `"
                    << actual << "`"
                    << std::endl;

                f_param_map.insert( std::make_pair< Expr_ptr, Expr_ptr >
                                    ( formal, actual ));

                ++ fi;
                ++ ai;
            }
        }
    }

    return true;
}

/* This method performs several DFS walks of the model, starting from
   module MAIN. During each walk a different task is executed. Refer to
   analyzer_pass_t enum definition for the exact sequence of actions. */
bool ModelMgr::analyze()
{
    analyzer_pass_t pass
        ((analyzer_pass_t) 0);

    while (pass < MMGR_DONE) {
        DRIVEL
            << "Model analysis (pass " << pass << ")"
            << std::endl ;

        if (! analyze_aux( pass ))
            return false;
        else {
            int tmp = 1 + (int) pass;
            pass = (analyzer_pass_t) tmp;
        }
    }



    TRACE
        << "Ok"
        << std::endl;

    f_analyzed = true;
    return true;
}

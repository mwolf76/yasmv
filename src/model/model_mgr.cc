/**
 * @file model/model_mgr.cc
 * @brief Model management subsystem, ModelMgr class implementation.
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

#include <expr/expr.hh>
#include <expr/expr_mgr.hh>

#include <symb/classes.hh>
#include <symb/typedefs.hh>

#include <model/exceptions.hh>
#include <model/model.hh>
#include <model/model_mgr.hh>
#include <model/module.hh>

#include <common/logging.hh>

namespace model {

    ModelMgr& ModelMgr::INSTANCE()
    {
        if (!f_instance) {
            f_instance = new ModelMgr();
        }

        return (*f_instance);
    }

    // static initialization
    ModelMgr_ptr ModelMgr::f_instance { NULL };

    ModelMgr::ModelMgr()
        : f_model()
        , f_resolver(*this)
        , f_type_checker(*this)
        , f_analyzed(false)
    {}

    Module_ptr ModelMgr::scope(expr::Expr_ptr key)
    {
        ContextMap::const_iterator mi { f_context_map.find(key) };
        assert(f_context_map.end() != mi);

        return mi->second;
    }

    expr::Expr_ptr ModelMgr::rewrite_parameter(expr::Expr_ptr expr)
    {
        ParamMap::const_iterator i { f_param_map.find(expr) };
        assert(f_param_map.end() != i);

        return i->second;
    }

    bool ModelMgr::analyze_aux(analyzer_pass_t pass)
    {
        expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };

	Model& model { f_model };
        Module& main_module { model.main_module() };

        std::stack<boost::tuple<expr::Expr_ptr, Module_ptr, expr::Expr_ptr>> stack;
        stack.push(
	    boost::make_tuple<expr::Expr_ptr, Module_ptr, expr::Expr_ptr>
	    (em.make_empty(), &main_module, em.make_empty()));

        /* walk of var decls, starting from main module */
        while (0 < stack.size()) {
            boost::tuple<expr::Expr_ptr, Module_ptr, expr::Expr_ptr> top { stack.top() };
            stack.pop();

            if (MMGR_BUILD_CTX_MAP == pass) {
                expr::Expr_ptr key { top.get<0>() };
                Module_ptr tgt { top.get<1>() };
                expr::Expr_ptr tgt_name { tgt->name() };

                DRIVEL
                    << "Registering scope "
                    << "`" << key << "`"
                    << " instance of `" << tgt_name << "`"
                    << std::endl;

                f_context_map.insert(std::pair<expr::Expr_ptr, Module_ptr>(key, tgt));
            }

            expr::Expr_ptr curr_ctx { top.get<0>() };
            Module& curr_module { *top.get<1>() };
            expr::Expr_ptr curr_params { top.get<2>() };

            if (MMGR_ANALYZE == pass) {
                const expr::ExprVector& init { curr_module.init() };

                for (expr::ExprVector::const_iterator ii = init.begin();
                     ii != init.end(); ++ii) {

                    expr::Expr_ptr body { *ii };

                    DEBUG
                        << "Analyzing INIT "
                        << curr_ctx << "::" << body
                        << std::endl;

                    try {
                        f_analyzer.process(body, curr_ctx, ANALYZE_INIT);
                    } catch (Exception& ae) {
                        std::string tmp { ae.what() };

                        WARN
                            << tmp
                            << std::endl
                            << "  in INIT "
                            << curr_ctx << "::" << body
                            << std::endl;

                        return false;
                    }
                } // for init

                const expr::ExprVector& invar { curr_module.invar() };
                for (expr::ExprVector::const_iterator ii = invar.begin();
                     ii != invar.end(); ++ii) {

                    expr::Expr_ptr body { *ii };

                    DEBUG
                        << "Analyzing INVAR "
                        << curr_ctx << "::" << body
                        << std::endl;

                    try {
                        f_analyzer.process(body, curr_ctx, ANALYZE_INVAR);
                    } catch (Exception& ae) {
                        std::string tmp { ae.what() };

                        WARN
                            << tmp
                            << std::endl
                            << "  in INVAR "
                            << curr_ctx << "::" << body
                            << std::endl;

                        return false;
                    }
                } // for invar

                const expr::ExprVector& trans { curr_module.trans() };
                for (expr::ExprVector::const_iterator ti = trans.begin();
                     ti != trans.end(); ++ti) {

                    expr::Expr_ptr body { *ti };

                    DEBUG
                        << "Analyzing TRANS "
                        << curr_ctx << "::" << body
                        << std::endl;

                    try {
                        f_analyzer.process(body, curr_ctx, ANALYZE_TRANS);
                    } catch (Exception& ae) {
                        std::string tmp { ae.what() };

                        WARN
                            << tmp
                            << std::endl
                            << "  in TRANS "
                            << curr_ctx << "::" << body
                            << std::endl;

                        return false;
                    }
                } // for trans

                const symb::Defines& defs { curr_module.defs() };
                for (symb::Defines::const_iterator di = defs.begin();
                     di != defs.end(); ++di) {

                    expr::Expr_ptr body { (*di).second->body() };

                    DEBUG
                        << "Analyzing "
                        << curr_ctx << "::" << body
                        << std::endl;

                    try {
                        f_analyzer.process(body, curr_ctx, ANALYZE_DEFINE);
                    } catch (Exception& ae) {
                        std::string tmp { ae.what() };

                        WARN
                            << tmp
                            << std::endl
                            << "  in DEFINE "
                            << curr_ctx << "::" << body
                            << std::endl;

                        return false;
                    }
                } // for defines
            }     /* MMGR_ANALYZE */

            else if (MMGR_TYPE_CHECK == pass) {
                const expr::ExprVector& init { curr_module.init() };
                for (expr::ExprVector::const_iterator ii = init.begin();
                     ii != init.end(); ++ii) {

                    expr::Expr_ptr body { *ii };

                    DEBUG
                        << "Type checking INIT "
                        << curr_ctx << "::" << body
                        << std::endl;

                    try {
                        f_type_checker.process(body, curr_ctx);
                    } catch (Exception& ae) {
                        std::string tmp(ae.what());

                        WARN
                            << tmp
                            << std::endl
                            << "  in INIT "
                            << curr_ctx << "::" << body
                            << std::endl;

                        return false;
                    }
                } // for init

                const expr::ExprVector& invar { curr_module.invar() };
                for (expr::ExprVector::const_iterator ii = invar.begin();
                     ii != invar.end(); ++ii) {

                    expr::Expr_ptr body { *ii };

                    DEBUG
                        << "Type checking INVAR "
                        << curr_ctx << "::" << body
                        << std::endl;

                    try {
                        f_type_checker.process(body, curr_ctx);
                    } catch (Exception& ae) {
                        std::string tmp { ae.what() };

                        WARN
                            << tmp
                            << std::endl
                            << "  in INVAR "
                            << curr_ctx << "::" << body
                            << std::endl;

                        return false;
                    }
                } // for invar

                const expr::ExprVector& trans { curr_module.trans() };
                for (expr::ExprVector::const_iterator ti = trans.begin();
                     ti != trans.end(); ++ti) {

                    expr::Expr_ptr body { *ti };

                    DEBUG
                        << "Type checking TRANS "
                        << curr_ctx << "::" << body
                        << std::endl;

                    try {
                        f_type_checker.process(body, curr_ctx);
                    } catch (Exception& ae) {
                        std::string tmp { ae.what() };

                        WARN
                            << tmp
                            << std::endl
                            << "  in TRANS "
                            << curr_ctx << "::" << body
                            << std::endl;

                        return false;
                    }
                } // for trans

                const symb::Defines& defs { curr_module.defs() };

                for (symb::Defines::const_iterator di = defs.begin();
                     di != defs.end(); ++di) {

                    expr::Expr_ptr body { (*di).second->body() };

                    DEBUG
                        << "Type checking "
                        << curr_ctx << "::" << body
                        << std::endl;

                    try {
                        f_type_checker.process(body, curr_ctx);
                    } catch (Exception& ae) {
                        std::string tmp { ae.what() };

                        WARN
                            << tmp
                            << std::endl
                            << "  in DEFINE "
                            << curr_ctx << "::" << body
                            << std::endl;

                        return false;
                    }
                } // for defines
            }     /* MMGR_TYPE_CHECK */

            symb::Variables attrs { curr_module.vars() };
            symb::Variables::const_iterator vi;

            for (vi = attrs.begin(); attrs.end() != vi; ++vi) {

                expr::Expr_ptr var_name { vi->first };
                type::Type_ptr var_tp { (*vi->second).type() };

                if (var_tp->is_instance()) {
                    type::InstanceType_ptr instance { var_tp->as_instance() };
                    expr::Expr_ptr inner_ctx { em.make_dot(curr_ctx, var_name) };
                    expr::Expr_ptr inner_params { instance->params() };
                    Module& module_ { module(instance->name()) };

                    stack.push(
			boost::make_tuple<expr::Expr_ptr, Module_ptr, expr::Expr_ptr>
			(inner_ctx, &module_, inner_params));
                }
            }

            if (MMGR_BUILD_PARAM_MAP == pass) {
                // analyze_params( curr_module, curr_params );
                std::vector<expr::Expr_ptr> actuals;

                // 1. in-order visit, build fwd expr stack
                std::stack<expr::Expr_ptr> comma_stack;
                comma_stack.push(curr_params);

                while (0 < comma_stack.size()) {
                    expr::Expr_ptr top { comma_stack.top() };
                    comma_stack.pop();

                    if (em.is_params_comma(top)) {
                        comma_stack.push(top->rhs());
                        comma_stack.push(top->lhs());
                        continue;
                    }

                    if (!em.is_empty(top)) {
                        actuals.push_back(em.make_dot(em.make_empty(), top));
                    }
                }

                // 2. good, now associate formals and actuals
                const symb::Parameters& formals { curr_module.parameters() };

                if (actuals.size() != formals.size()) {
                    throw BadParamCount(curr_module.name(), formals.size(), actuals.size());
                }

                symb::Parameters::const_iterator fi { formals.begin() };
                std::vector<expr::Expr_ptr>::const_iterator ai { actuals.begin() };

                while (formals.end() != fi) {
                    expr::Expr_ptr formal { em.make_dot(curr_ctx, ((*fi->second).name())) };
                    expr::Expr_ptr actual { *ai };

                    DEBUG
                        << "Mapping `"
                        << formal
                        << "` to `"
                        << actual << "`"
                        << std::endl;

                    f_param_map.insert(std::pair<expr::Expr_ptr, expr::Expr_ptr>
				       (formal, actual));

                    ++fi;
                    ++ai;
                }
            }
        }

        return true;
    }

    /* This method performs several DFS walks of the model, starting
     * from module MAIN. During each walk a different task is
     * executed. Refer to analyzer_pass_t enum definition for the
     * exact sequence of actions. */
    bool ModelMgr::analyze()
    {
        analyzer_pass_t pass { (analyzer_pass_t) 0 };

        while (pass < MMGR_DONE) {
            DRIVEL
                << "Model analysis (pass " << pass << ")"
                << std::endl;

            if (!analyze_aux(pass)) {
                return false;
            } else {
                int tmp { 1 + (int) pass };
                pass = (analyzer_pass_t) tmp;
            }
        }

        f_analyzed = true;
        f_analyzer.generate_framing_conditions();

        TRACE
            << "Model analysis complete"
            << std::endl;

        return true;
    }

}; // namespace model

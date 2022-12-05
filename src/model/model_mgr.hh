/**
 * @file model_mgr.hh
 * @brief Model module (ModelMgr class)
 *
 * This header file contains the declarations required by the Model
 * Manager class.
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

#ifndef MODEL_MGR_H
#define MODEL_MGR_H

#include <model/model.hh>
#include <model/model_resolver.hh>

#include <expr/preprocessor/preprocessor.hh>

#include <model/analyzer/analyzer.hh>
#include <model/type_checker/type_checker.hh>

#include <type/type_mgr.hh>

namespace model {

    using ContextMap =
	boost::unordered_map<expr::Expr_ptr, Module_ptr, utils::PtrHash, utils::PtrEq>;

    using ParamMap =
	boost::unordered_map<expr::Expr_ptr, expr::Expr_ptr>;

    typedef enum {
        MMGR_BUILD_CTX_MAP,
        MMGR_BUILD_PARAM_MAP,
        MMGR_ANALYZE,
        MMGR_TYPE_CHECK,
        MMGR_DONE
    } analyzer_pass_t;

    typedef class ModelMgr* ModelMgr_ptr;
    class ModelMgr {

    public:
        /* singleton */
        static ModelMgr& INSTANCE();

        inline Model& model()
        {
            return f_model;
        }

        inline Module& module(expr::Expr_ptr module_name)
        {
            return f_model.module(module_name);
        }

        inline symb::Resolver_ptr resolver()
        {
            return &f_resolver;
        }

        // this must be called before any type checking
        bool analyze();

        inline Analyzer& analyzer()
        {
            return f_analyzer;
        }

        // delegated type inference method
        inline type::Type_ptr type(expr::Expr_ptr body,
                                   expr::Expr_ptr ctx = expr::ExprMgr::INSTANCE().make_empty())
        {
            assert(f_analyzed);
            return f_type_checker.type(body, ctx);
        }

        Module_ptr scope(expr::Expr_ptr ctx);

        expr::Expr_ptr rewrite_parameter(expr::Expr_ptr expr);

    protected:
        ModelMgr();
        ~ModelMgr();

        friend class ModelResolver;

        symb::Symbols f_symbols;
        inline symb::Symbols& symbols()
        {
            return f_symbols;
        }

    private:
        static ModelMgr_ptr f_instance;

        /* local data */
        Model f_model;

        // owned
        ModelResolver f_resolver;
        Analyzer f_analyzer;
        TypeChecker f_type_checker;

        ContextMap f_context_map;
        ParamMap f_param_map;

        /* internals */
        bool analyze_aux(analyzer_pass_t pass);
        bool f_analyzed;
    };

} // namespace model

#endif /* MODEL_MGR_H */

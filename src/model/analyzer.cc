/**
 *  @file analyzer.cc
 *  @brief Model analyzer
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

#include <common.hh>

#include <expr.hh>
#include <analyzer.hh>

Analyzer::Analyzer()
    : f_mm(ModelMgr::INSTANCE())
    , f_em(ExprMgr::INSTANCE())
    , f_tm(TypeMgr::INSTANCE())
    , f_inferrer()
{
    TRACE << "Created Analyzer @" << this << endl;
}

Analyzer::~Analyzer()
{ TRACE << "Destroying Analyzer @" << this << endl; }

void Analyzer::process()
{
    Model& model = dynamic_cast <Model&> (*f_mm.model());

    try {
        const Modules& modules = model.modules();

        TRACE << "-- first pass (binding)" << endl;
        // (binding) For each module m in M, A goes deep in the module
        // defs. Every variable decl is resolved either to a native type
        // (boolean, ranged int, ...) or to an instance. Due to (1) all
        // modules are defined so any unresolved symbol at this point is a
        // fatal. Native types are taken care of as well.
        for (Modules::const_iterator mod_eye = modules.begin();
             mod_eye != modules.end(); mod_eye ++ ) {

            Module& module = dynamic_cast <Module&> (*mod_eye->second);
            TRACE << "processing module '" << module << "' " << endl;

            // Remark: ctx name is MODULE name, not instance's
            // rationale: you may have several instances but they
            // all should refer to the same entry on the type map.
            const Expr_ptr ctx = module.expr();

            const Variables vars = module.get_localVars();
            for (Variables::const_iterator var_eye = vars.begin();
                 var_eye != vars.end(); var_eye ++) {

                IVariable_ptr const var = var_eye->second;

                const Expr_ptr varname = var->expr();
                const Type_ptr vartype = var->type();

                TRACE << "processing var " << varname << ": " << vartype << endl;

                // eager binding for module instances
                if (f_tm.is_instance(vartype)) {
                    Instance& instance = dynamic_cast <Instance&> (*vartype);

                    const Expr_ptr module_name = instance.get_module_name();
                    IModule& resolved = model.get_module(module_name);

                    // match number of params
                    int inst_params_num = instance.get_params().size();
                    int modl_params_num = resolved.get_formalParams().size();
                    if ( inst_params_num != modl_params_num ) {
                        throw BadParams(module_name,
                                        modl_params_num,
                                        inst_params_num);
                    }
                }

                f_tm.set_type( FQExpr(ctx, varname), vartype);
            }
        }

        // (typechecking) For each module m in M, A inspects FSM exprs:
        // INVAR, TRANS, FAIRNESS have all to be boolean formulae; ASSIGNs
        // have to match lvalue type. The type for every expression is
        // inferred using the lazy walker strategy.
        TRACE << "-- second pass (type checking)" << endl;
        for (Modules::const_iterator mod_eye = modules.begin();
             mod_eye != modules.end(); mod_eye ++ ) {

            Module& module = dynamic_cast <Module&> (*mod_eye->second);
            TRACE << "processing module '" << module << "' " << endl;

            // Remark: ctx name is MODULE name, not instance's
            // rationale: you may have several instances but they
            // all should refer to the same entry on the type map.
            Expr_ptr ctx = module.expr();

            // const ExprVector params = module.get_formalParams();
            // for (ExprVector::const_iterator param_eye = params.begin();
            //      param_eye != params.end(); param_eye ++) {

            //   Expr_ptr pname = *param_eye;
            //   tm.reset_type(FQExpr(ctx, pname));
            // }

            // TODO: isa decls currently not supported
            const ExprVector isadecls = module.get_isaDecls();
            assert (isadecls.size() == 0);

            // type inference: defines
            const Defines defines = module.get_localDefs();
            for (Defines::const_iterator define_eye = defines.begin();
                 define_eye != defines.end(); define_eye ++) {

                Define& define = dynamic_cast <Define&> (*define_eye->second);

                Expr_ptr dname = define.expr();
                FQExpr fqdn(ctx, dname);

                Expr_ptr dbody = define.body();
                Type_ptr dtype = f_inferrer.process(ctx, dbody);

                Type_ptr type = f_tm.type(fqdn); // previously determined type
                if (type) {
                    if (type != dtype) {
                        throw BadType(type->get_repr(),
                                      dtype->get_repr(),
                                      dbody);
                    }
                } else f_tm.set_type(fqdn, dtype);
            } // for defines

            // type inference: FSM
            const ExprVector init = module.init();
            for (ExprVector::const_iterator init_eye = init.begin();
                 init_eye != init.end(); init_eye ++) {

                Expr_ptr body = (*init_eye);
                TRACE << "processing INIT " << ctx << "::" << body << endl;

                Type_ptr tp = f_inferrer.process(ctx, body);
                if (tp != f_tm.find_boolean())
                    throw BadType(f_tm.find_boolean()->get_repr(),
                                  tp->get_repr(), body);
            } // for init

            const ExprVector invar = module.invar();
            for (ExprVector::const_iterator invar_eye = invar.begin();
                 invar_eye != invar.end(); invar_eye ++) {

                Expr_ptr body = (*invar_eye);
                TRACE << "processing INVAR " << ctx << "::" << body << endl;

                Type_ptr tp = f_inferrer.process(ctx, body);
                if (tp != f_tm.find_boolean()) {
                    throw BadType(f_tm.find_boolean()->get_repr(),
                                  tp->get_repr(), body);
                }
            } // for invar

            const ExprVector trans = module.trans();
            for (ExprVector::const_iterator trans_eye = trans.begin();
                 trans_eye != trans.end(); trans_eye ++) {

                Expr_ptr body = (*trans_eye);
                TRACE << "processing TRANS " << ctx << "::" << body << endl;

                Type_ptr tp = f_inferrer.process(ctx, body);
                if (tp != f_tm.find_boolean()) {
                    throw BadType(f_tm.find_boolean()->get_repr(),
                                  tp->get_repr(), body);
                }
            } // for trans

            const ExprVector fair = module.fairness();
            for (ExprVector::const_iterator fair_eye = fair.begin();
                 fair_eye != fair.end(); fair_eye ++) {

                Expr_ptr body = (*fair_eye);
                TRACE << "processing FAIRNESS " << ctx << "::" << body << endl;

                Type_ptr tp = f_inferrer.process(ctx, body);
                if (tp != f_tm.find_boolean()) {
                    throw BadType(f_tm.find_boolean()->get_repr(),
                                  tp->get_repr(), body);
                }
            } // for fair

            const Assigns assign = module.get_assign();
            for (Assigns::const_iterator assign_eye = assign.begin();
                 assign_eye != assign.end(); assign_eye ++) {

                Define& define = dynamic_cast <Define&> (*assign_eye->second);
                Expr_ptr lvalue = define.expr();
                FQExpr fqdn(ctx, lvalue);

                // TODO: check it's an lvalue
                // if (!lvalue)
                //     throw NotAnLvalue(lvalue);

                Expr_ptr dbody = define.body();
                Type_ptr dtype = f_inferrer.process(ctx, dbody);

                Type_ptr type = f_tm.type(fqdn); // previously determined type
                if (type) {
                    if (type != dtype) {
                        throw BadType(type->get_repr(),
                                      dtype->get_repr(),
                                      dbody);
                    }
                } else f_tm.set_type(fqdn, dtype);
            } // for assign

            const ExprVector ltlspecs = module.ltlspecs();
            for (ExprVector::const_iterator ltl_eye = ltlspecs.begin();
                 ltl_eye != ltlspecs.end(); ltl_eye ++) {

                Expr_ptr body = (*ltl_eye);
                TRACE << "processing LTLSPEC " << ctx << "::" << body << endl;

                Type_ptr tp = f_inferrer.process(ctx, body);
                if (tp != f_tm.find_temporal()) {
                    // throw BadType(LTL_TEMPORAL, tp, body);
                }
            } // for ltlspecs

            const ExprVector ctlspecs = module.ctlspecs();
            for (ExprVector::const_iterator ctl_eye = ctlspecs.begin();
                 ctl_eye != ctlspecs.end(); ctl_eye ++) {

                Expr_ptr body = (*ctl_eye);
                TRACE << "processing CTLSPEC " << ctx << "::" << body << endl;


                Type_ptr tp = f_inferrer.process(ctx, body);
                if (tp != f_tm.find_temporal()) {
                    // throw BadType(CTL_TEMPORAL, tp, body);
                }

            } // for ctlspecs

        } // for modules

    }

    catch (AnalyzerException& ae) {
        cerr << ae.what() << endl;
    }
}

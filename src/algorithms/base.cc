#include <compiler/streamers.hh>
#include <query/source.hh>
#include <query/trace.hh>
/**
 * @file base.cc
 * @brief foundations for all the SAT-based algorithms.
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

// ReSharper disable CppMemberFunctionMayBeConst
// ReSharper disable CppMemberFunctionMayBeStatic
#include <vector>

#include <base.hh>
#include <symb/proxy.hh>

#include <model/model.hh>

#include <env/environment.hh>

#include <utils/misc.hh>

namespace algorithms {
    static const Algorithm* compiled_snapshot = nullptr;
    void Algorithm::reuse(const Algorithm* compiled) { compiled_snapshot = compiled; }

    Algorithm::Algorithm(model::Model& model)
        : f_ok(true)
        , f_model(model)
        , f_mm(model::ModelMgr::INSTANCE())
        , f_bm(enc::EncodingMgr::INSTANCE())
        , f_em(expr::ExprMgr::INSTANCE())
        , f_tm(type::TypeMgr::INSTANCE())
        , f_witness(nullptr)
    {
        f_mm.require_valid();
        if (compiled_snapshot) {
            if (&model != &compiled_snapshot->f_model) throw std::logic_error("Compiled snapshot model mismatch");
            f_init = compiled_snapshot->f_init;
            f_invar = compiled_snapshot->f_invar;
            f_trans = compiled_snapshot->f_trans;
            return;
        }
        /* Force mgr to exist */
        sat::EngineMgr& mgr { sat::EngineMgr::INSTANCE() };
        (void) mgr; /* suppress warning */

        env::Environment& env { env::Environment::INSTANCE() };

        std::stack<std::pair<expr::Expr_ptr, model::Module_ptr>> stack;
        model::Module& main_module { model.main_module() };
        stack.push(std::pair<expr::Expr_ptr, model::Module_ptr>(em().make_empty(), &main_module));

        /* walk of var decls, starting from main module */
        while (0 < stack.size()) {
            const std::pair<expr::Expr_ptr, model::Module_ptr> top { stack.top() };
            stack.pop();

            expr::Expr_ptr ctx { top.first };
            model::Module& module { *top.second };

            f_source_module = module.name();
            /* module INITs */
            const expr::ExprVector& init { module.init() };
            process_init(ctx, init);

            /* module INVARs */
            const expr::ExprVector& invar { module.invar() };
            process_invar(ctx, invar);

            /* module TRANSes */
            const expr::ExprVector& trans { module.trans() };
            process_trans(ctx, trans);

            symb::Variables attrs { module.vars() };
            symb::Variables::const_iterator vi;
            for (vi = attrs.begin(); attrs.end() != vi; ++vi) {
                expr::Expr_ptr id { vi->first };
                expr::Expr_ptr local_ctx { em().make_dot(ctx, id) };

                symb::Variable& var { *vi->second };
                if (const type::Type_ptr var_type { var.type() }; var_type->is_instance()) {
                    type::InstanceType_ptr instance { var_type->as_instance() };
                    model::Module& instance_module { model.module(instance->name()) };
                    stack.push(std::pair<expr::Expr_ptr, model::Module_ptr>(local_ctx, &instance_module));
                }
            }
        } /* while() */

        f_source_module = nullptr;
        /* processing environment extra constraints */
        const expr::ExprVector& extra_init { env.extra_init() };
        process_init(nullptr, extra_init);

        /* environment INVARs */
        const expr::ExprVector& extra_invar { env.extra_invar() };
        process_invar(nullptr, extra_invar);

        /* environment TRANSes */
        const expr::ExprVector& extra_trans { env.extra_trans() };
        process_trans(nullptr, extra_trans);

        if (!ok()) {
            throw FailedSetup();
        }

        TRACE
            << "Base setup completed"
            << std::endl;
    }

    Algorithm::~Algorithm()
    {}

    void Algorithm::process_init(expr::Expr_ptr ctx, const expr::ExprVector& init)
    {
        size_t occurrence_index = 0;
        for (auto body : init) {
            DEBUG
                << "processing INIT "
                << ctx << "::" << body
                << std::endl;

            try {
                auto unit = compiler().process(ctx, body);
                unit.source_ids = {source::occurrence(f_source_module, "init", occurrence_index++, ctx)};
                f_init.push_back(unit);
            } catch (Exception& ae) {
                f_ok = false;

                pconst_char what { ae.what() };
                ERR
                    << what
                    << std::endl
                    << "  in INIT "
                    << ctx << "::" << body
                    << std::endl;
            }
        }
    } /* process_init() */

    void Algorithm::process_invar(expr::Expr_ptr ctx, const expr::ExprVector& invar)
    {
        size_t occurrence_index = 0;
        for (auto body : invar) {
            DEBUG
                << "processing INVAR "
                << ctx << "::" << body
                << std::endl;
            try {
                auto unit = compiler().process(ctx, body);
                unit.source_ids = {source::occurrence(f_source_module, "invar", occurrence_index++, ctx)};
                f_invar.push_back(unit);
            } catch (Exception& ae) {
                f_ok = false;

                pconst_char what { ae.what() };
                ERR
                    << what
                    << std::endl
                    << "  in INVAR "
                    << ctx << "::" << body
                    << std::endl;
            }
        }
    } /* process_invar() */

    void Algorithm::process_trans(expr::Expr_ptr ctx, const expr::ExprVector& trans)
    {
        size_t occurrence_index = 0;
        for (auto body : trans) {
            DEBUG
                << "processing TRANS "
                << ctx << "::" << body
                << std::endl;

            try {
                auto unit = compiler().process(ctx, body);
                unit.source_ids = {source::occurrence(f_source_module, "trans", occurrence_index++, ctx)};
                f_trans.push_back(unit);
            } catch (Exception& ae) {
                f_ok = false;

                pconst_char what { ae.what() };
                ERR
                    << what
                    << std::endl
                    << "  in TRANS "
                    << ctx << "::" << body
                    << std::endl;
            }
        }
    } /* process_trans() */

    void Algorithm::assert_fsm_init(sat::Engine& engine, step_t time, const sat::group_t group)
    {
        const clock_t t0 { clock() };
        const auto count { f_init.size() };

        TRACE
            << "Pushing "
            << count
            << " INIT units"
            << "(time = " << time << ")"
            << std::endl;

        for (const auto& i : f_init) {
            engine.push(i, time, group);
        }

        const clock_t elapsed { clock() - t0 };
        double secs { static_cast<double>(elapsed) / static_cast<double>(CLOCKS_PER_SEC) };

        TRACE
            << "Took "
            << secs
            << " seconds."
            << std::endl;
    }

    void Algorithm::assert_fsm_invar(sat::Engine& engine, step_t time, const sat::group_t group)
    {
        query::trace::allocate_state(engine, time);
        const clock_t t0 { clock() };
        const auto count { f_invar.size() };

        TRACE
            << "Pushing "
            << count
            << " INVAR units "
            << "(time = " << time << ") ..."
            << std::endl;

        for (const auto& i : f_invar) {
            engine.push(i, time, group);
        }

        const clock_t elapsed { clock() - t0 };
        double secs { static_cast<double>(elapsed) / static_cast<double>(CLOCKS_PER_SEC) };

        TRACE
            << "Took "
            << secs
            << " seconds."
            << std::endl;
    }

    void Algorithm::assert_fsm_trans(sat::Engine& engine, step_t time, const sat::group_t group)
    {
        const clock_t t0 { clock() };
        const auto count { f_trans.size() };

        TRACE
            << "Pushing "
            << count
            << " TRANS units"
            << "(time = " << time << ") ..."
            << std::endl;

        for (const auto& f_tran : f_trans) {
            engine.push(f_tran, time, group);
        }

        const clock_t elapsed { clock() - t0 };
        double secs { static_cast<double>(elapsed) / static_cast<double>(CLOCKS_PER_SEC) };

        TRACE
            << "Took "
            << secs
            << " seconds."
            << std::endl;
    }

    void Algorithm::assert_fsm_uniqueness(sat::Engine& engine, step_t j, step_t k, sat::group_t group)
    {
        symb::SymbIter symbols { model() };

        /* this will hold the activation vars for the uniqueness clauses
           defined below */
        sat::VarVector uniqueness_vars;

        while (symbols.has_next()) {
            std::pair<expr::Expr_ptr, symb::Symbol_ptr> pair { symbols.next() };

            expr::Expr_ptr ctx { pair.first };
            symb::Symbol_ptr symbol { pair.second };

            if (symbol->is_variable()) {
                symb::Variable& var { symbol->as_variable() };
                if (var.is_input() || var.is_frozen() || var.is_temp()) {
                    continue;
                }

                expr::Expr_ptr expr { var.name() };
                expr::TimedExpr key { em().make_dot(ctx, expr), 0 };
                enc::Encoding_ptr enc { f_bm.find_encoding(key) };

                if (!enc) {
                    continue;
                }

                dd::DDVector::const_iterator di;
                unsigned ndx;
                for (ndx = 0, di = enc->bits().begin(); enc->bits().end() != di; ++ndx, ++di) {
                    unsigned bit { di->getNode()->index };
                    const enc::UCBI& ucbi { f_bm.find_ucbi(bit) };
                    const enc::TCBI jtcbi { enc::TCBI(ucbi, j) };
                    const enc::TCBI ktcbi { enc::TCBI(ucbi, k) };

                    sat::Var jkne { engine.new_sat_var() };
                    uniqueness_vars.push_back(jkne);

                    const sat::Var jvar { engine.tcbi_to_var(jtcbi) };
                    const sat::Var kvar { engine.tcbi_to_var(ktcbi) };

                    /* for each pair (j, k) we assert two clauses, both
                       activated by jkne. The first clause is satisfied if
                       at least one of the two variables (j, k) is false;
                       the second clause is satisfied if at least one of
                       the two variables is true. As it is impossible for
                       the same variable to be false and true at the same
                       time, this is equivalent to state:

                       jkne -> j xor k */

                    {
                        sat::Lits ps;
                        ps.push_back(sat::mkLit(jkne, true));
                        ps.push_back(sat::mkLit(jvar, true));
                        ps.push_back(sat::mkLit(kvar, true));

                        engine.add_clause(ps);
                    }

                    {
                        sat::Lits ps;
                        ps.push_back(sat::mkLit(jkne, true));
                        ps.push_back(sat::mkLit(jvar, false));
                        ps.push_back(sat::mkLit(kvar, false));

                        engine.add_clause(ps);
                    }
                }
            }
        }

        /* ...  finally, we assert that at least one of the activation
           variables is true */
        {
            sat::Lits ps;
            ps.push_back(sat::mkLit(group, true));

            for (int uniqueness_var : uniqueness_vars) {
                ps.push_back(sat::mkLit(uniqueness_var, false));
            }

            engine.add_clause(ps);
        }
    }

    void Algorithm::assert_time_frame(sat::Engine& engine,
                                      step_t time,
                                      witness::TimeFrame& tf,
                                      sat::group_t group)
    {
        symb::ResolverProxy resolver;

        expr::ExprVector assignments { tf.assignments() };
        unsigned count { 0 };

        expr::ExprVector::const_iterator i { assignments.begin() };
        while (i != assignments.end()) {
            expr::Expr_ptr assignment { *i++ };
            expr::Expr_ptr full { assignment->lhs() };
            symb::Symbol_ptr symbol { resolver.symbol(full) };

            if (symbol->is_variable()) {
                expr::Expr_ptr scope { full->lhs() };
                expr::Expr_ptr expr { em().make_eq(full->rhs(), query::trace::typed_value(symbol->as_variable().type(), assignment->rhs())) };

                DEBUG
                    << expr
                    << std::endl;

                try {
                    ++count;
                    engine.push(compiler().process(scope, expr), time, group);
                }

                catch (Exception& e) {
                    f_ok = false;
                    throw;
                }
            }
        }

        DEBUG
            << "Pushed " << count << " assignments"
            << std::endl;
    }

    void Algorithm::assert_formula(sat::Engine& engine,
                                   step_t time,
                                   const compiler::Unit& term,
                                   sat::group_t group)
    {
        INFO
            << "asserting formula at time "
            << time
            << ": "
            << term
            << std::endl;

        engine.push(term, time, group);
    }

} // namespace algorithms

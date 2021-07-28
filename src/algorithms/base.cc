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

#include <vector>

#include <base.hh>
#include <symb/proxy.hh>

#include <model/model.hh>

#include <env/environment.hh>

#include <utils/misc.hh>

Algorithm::Algorithm(cmd::Command& command, Model& model)
    : f_command(command)
    , f_model(model)
    , f_mm(ModelMgr::INSTANCE())
    , f_bm(enc::EncodingMgr::INSTANCE())
    , f_em(expr::ExprMgr::INSTANCE())
    , f_tm(TypeMgr::INSTANCE())
    , f_witness(NULL)
{}

Algorithm::~Algorithm()
{}

void Algorithm::setup()
{
    f_ok = true;

    /* Force mgr to exist */
    sat::EngineMgr& mgr
        (sat::EngineMgr::INSTANCE());

    /* suppress warning */
    (void) mgr;

    expr::ExprMgr& em
        (expr::ExprMgr::INSTANCE());

    env::Environment& env
        (env::Environment::INSTANCE());

    Model& model
        (f_model);

    Module& main_module
        (model.main_module());

    std::stack< std::pair<expr::Expr_ptr, Module_ptr> > stack;
    stack.push( std::pair<expr::Expr_ptr, Module_ptr >
                (em.make_empty(), &main_module));

    /* walk of var decls, starting from main module */
    while (0 < stack.size()) {

        const std::pair<expr::Expr_ptr, Module_ptr > top
            (stack.top());
        stack.pop();

        expr::Expr_ptr ctx
            (top.first);

        Module& module
            (* top.second);

        /* module INITs */
        const expr::ExprVector& init
            (module.init());
        process_init(ctx, init);

        /* module INVARs */
        const expr::ExprVector& invar
            (module.invar());
        process_invar(ctx, invar);

        /* module TRANSes */
        const expr::ExprVector& trans
            (module.trans());
        process_trans(ctx, trans);

        symb::Variables attrs
            (module.vars());
        symb::Variables::const_iterator vi;
        for (vi = attrs.begin(); attrs.end() != vi; ++ vi) {
            expr::Expr_ptr id
                (vi->first);

            symb::Variable& var
                (* vi->second);

            Type_ptr vtype
                (var.type());

            expr::Expr_ptr local_ctx
                (em.make_dot( ctx, id));

            if (vtype->is_instance()) {

                InstanceType_ptr instance
                    (vtype->as_instance());

                Module&  module
                    (model.module(instance->name()));

                stack.push( std::pair< expr::Expr_ptr, Module_ptr >
                            (local_ctx, &module));
            }
        }
    } /* while() */

    /* processing environment extra constraints */
    const expr::ExprVector& extra_init
        (env.extra_init());
    process_init(NULL, extra_init);

    /* environment INVARs */
    const expr::ExprVector& extra_invar
        (env.extra_invar());
    process_invar(NULL, extra_invar);

    /* environment TRANSes */
    const expr::ExprVector& extra_trans
        (env.extra_trans());
    process_trans(NULL, extra_trans);
}

void Algorithm::process_init(expr::Expr_ptr ctx, const expr::ExprVector& exprs)
{
    Compiler& cmpl
        (compiler()); // just a local ref

    for (expr::ExprVector::const_iterator ii = exprs.begin(); ii != exprs.end(); ++ ii ) {

        expr::Expr_ptr body
            (*ii);

        DEBUG
            << "processing INIT "
            << ctx << "::" << body
            << std::endl;

        try {
            f_init.push_back( cmpl.process(ctx, *ii));
        }
        catch (Exception& ae) {
            f_ok = false;

            pconst_char what
                (ae.what());

            ERR
                << what
                << std::endl
                << "  in INIT "
                << ctx << "::" << body
                << std::endl;

            free ((void *) what);
        }
    }
} /* process_init() */

void Algorithm::process_invar(expr::Expr_ptr ctx, const expr::ExprVector& exprs)
{
    Compiler& cmpl
        (compiler()); // just a local ref

    for (expr::ExprVector::const_iterator ii = exprs.begin(); ii != exprs.end(); ++ ii ) {

            expr::Expr_ptr body
                (*ii);

            DEBUG
                << "processing INVAR "
                << ctx << "::" << body
                << std::endl;
            try {
                f_invar.push_back( cmpl.process(ctx, *ii));
            }
            catch (Exception& ae) {
                f_ok = false;

                pconst_char what
                    (ae.what());

                ERR
                    << what
                    << std::endl
                    << "  in INVAR "
                    << ctx << "::" << body
                    << std::endl;

                free((void *) what);
            }
        }
} /* process_invar() */

void Algorithm::process_trans(expr::Expr_ptr ctx, const expr::ExprVector& exprs)
{
    Compiler& cmpl
        (compiler()); // just a local ref

    for (expr::ExprVector::const_iterator ti = exprs.begin(); ti != exprs.end(); ++ ti ) {

        expr::Expr_ptr body
            (*ti);

        DEBUG
            << "processing TRANS "
            << ctx << "::" << body
            << std::endl;

        try {
            f_trans.push_back( cmpl.process(ctx, *ti));
        }
        catch (Exception& ae) {
            f_ok = false;

            pconst_char what
                (ae.what());

            ERR
                << what
                << std::endl
                << "  in TRANS "
                << ctx << "::" << body
                << std::endl;

            free ((void *) what);
        }
    }
} /* process_trans() */

void Algorithm::assert_fsm_init(sat::Engine& engine, step_t time, sat::group_t group)
{
    for (CompilationUnits::const_iterator i = f_init.begin(); f_init.end() != i; ++ i)
        engine.push( *i, time, group);
}

void Algorithm::assert_fsm_invar(sat::Engine& engine, step_t time, sat::group_t group)
{
    for (CompilationUnits::const_iterator i = f_invar.begin(); f_invar.end() != i; ++ i)
        engine.push( *i, time, group);
}

void Algorithm::assert_fsm_trans(sat::Engine& engine, step_t time, sat::group_t group)
{
    for (CompilationUnits::const_iterator i = f_trans.begin(); f_trans.end() != i; ++ i)
        engine.push( *i, time, group);
}

void Algorithm::assert_fsm_uniqueness(sat::Engine& engine, step_t j, step_t k, sat::group_t group)
{
    symb::SymbIter symbs
        (model());

    /* this will hold the activation vars for the uniqueness clauses
       defined below */
    sat::VarVector uniqueness_vars;

    while (symbs.has_next()) {

        std::pair<expr::Expr_ptr, symb::Symbol_ptr> pair
            (symbs.next());

        expr::Expr_ptr ctx
            (pair.first);

        symb::Symbol_ptr symb
            (pair.second);

        if (symb->is_variable()) {
            symb::Variable& var
                (symb->as_variable());

            if (var.is_input() ||
                var.is_frozen() ||
                var.is_temp())
                continue ;

            expr::Expr_ptr expr
                (var.name());

            expr::TimedExpr key
                (em().make_dot( ctx, expr), 0);

            enc::Encoding_ptr enc
                (f_bm.find_encoding(key));

            if (!enc)
                continue;

            dd::DDVector::const_iterator di;
            unsigned ndx;
            for (ndx = 0, di = enc->bits().begin();
                 enc->bits().end() != di; ++ ndx, ++ di) {

                unsigned bit
                    ((*di).getNode()->index);

                const enc::UCBI& ucbi
                    (f_bm.find_ucbi(bit));

                const enc::TCBI jtcbi
                    (enc::TCBI(ucbi, j));

                const enc::TCBI ktcbi
                    (enc::TCBI(ucbi, k));

                Var jkne
                    (engine.new_sat_var());

                uniqueness_vars.push_back(jkne);

                Var jvar
                    (engine.tcbi_to_var(jtcbi));

                Var kvar
                    (engine.tcbi_to_var(ktcbi));

                /* for each pair (j, k) we assert two clauses, both
                   activated by jkne. The first clause is satisfied if
                   at least one of the two variables (j, k) is false;
                   the second clause is satisified if at least one of
                   the two variables is true. As it is impossibile for
                   the same variable to be false and true at the same
                   time, this is equivalent to state:

                   jkne -> j xor k */

                {
                    vec<Lit> ps;
                    ps.push( mkLit( jkne, true));
                    ps.push( mkLit( jvar, true));
                    ps.push( mkLit( kvar, true));

                    engine.add_clause(ps);
                }

                {
                    vec<Lit> ps;
                    ps.push( mkLit( jkne, true));
                    ps.push( mkLit( jvar, false));
                    ps.push( mkLit( kvar, false));

                    engine.add_clause(ps);
                }
            }
        }
    }

    /* ...  finally, we assert that at least one of the activation
       variables is true */
    {
        vec<Lit> ps;
        ps.push( mkLit( group, true));

        for (sat::VarVector::const_iterator eye = uniqueness_vars.begin();
             eye != uniqueness_vars.end(); ++ eye) {
            ps.push( mkLit( *eye, false));
        }

        engine.add_clause(ps);
    }
}

void Algorithm::assert_time_frame(sat::Engine& engine,
                                  step_t time,
                                  witness::TimeFrame& tf,
                                  sat::group_t group)
{
    expr::ExprMgr& em
        (expr::ExprMgr::INSTANCE());

    Compiler& cmpl
        (compiler()); // just a local ref

    expr::ExprVector assignments
        (tf.assignments());

    expr::ExprVector::const_iterator i
        (assignments.begin());

    symb::ResolverProxy resolver;

    unsigned count (0);
    while (i != assignments.end()) {

        expr::Expr_ptr assignment
            (*i); ++ i;

        expr::Expr_ptr full
            (assignment->lhs());

        symb::Symbol_ptr symb
            (resolver.symbol(full));

        if (symb->is_variable()) {
            expr::Expr_ptr scope
                (full->lhs());

            expr::Expr_ptr expr
                (em.make_eq( full->rhs(),
                             assignment->rhs()));

            DEBUG
                << expr
                << std::endl;

            try {
                ++ count;
                engine.push( cmpl.process(scope, expr), time, group);
            }

            catch (Exception& e) {
                f_ok = false;

                std::cerr
                    << e.what()
                    << std::endl;
            }
        }
    }

    DEBUG
        << "Pushed " << count << " assignments"
        << std::endl;
}

void Algorithm::assert_formula(sat::Engine& engine,
                               step_t time,
                               CompilationUnit& term,
                               sat::group_t group)
{
    INFO
        << "asserting formula at time "
        << time
        << ": "
        << term
        << std::endl;

    engine.push( term, time, group);
}

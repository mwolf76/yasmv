/**
 *  @file Base Algorithm.cc
 *  @brief Base Algorithm
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
#include <vector>

#include <base.hh>
#include <symb/proxy.hh>

#include <model/model.hh>

#include <env/environment.hh>

const char* AlgorithmException::what() const throw()
{
    std::ostringstream oss;
    oss
        << "Failure detected. Operation aborted."
        << std::endl
        ;

    return strdup(oss.str().c_str());
}

Algorithm::Algorithm(Command& command, Model& model)
    : f_command(command)
    , f_model(model)
    , f_mm(ModelMgr::INSTANCE())
    , f_bm(EncodingMgr::INSTANCE())
    , f_em(ExprMgr::INSTANCE())
    , f_tm(TypeMgr::INSTANCE())
    , f_witness(NULL)
{
    const void* instance
        (this);

    set_param("alg_name", "test");
    DEBUG
        << "Creating algorithm instance "
        << get_param("alg_name")
        << " @" << instance
        << std::endl;
}

Algorithm::~Algorithm()
{
    const void* instance
        (this);

    DEBUG
        << "Destroying algorithm instance "
        << get_param("alg_name")
        << " @" << instance
        << std::endl;
}

void Algorithm::set_param(std::string key, Variant value)
{ f_params [ key ] = value; }

Variant& Algorithm::get_param(const std::string key)
{
    const ParametersMap::iterator eye = f_params.find(key);

    if (eye != f_params.end()) {
        return (*eye).second;
    }

    else return NilValue;
}

void Algorithm::setup()
{
    f_ok = true;

    /* Force mgr to exist */
    EngineMgr& mgr
        (EngineMgr::INSTANCE());

    /* suppress warning */
    (void) mgr;

    Compiler& cmpl
        (compiler()); // just a local ref

    ExprMgr& em
        (ExprMgr::INSTANCE());

    Environment& env
        (Environment::INSTANCE());

    Model& model
        (f_model);
    const Modules& modules
        (model.modules());
    Expr_ptr main_module
        (em.make_main());

    Modules::const_iterator main_iter
        (modules.find(main_module));

    if (modules.end() == main_iter)
        throw ModuleNotFound(main_module);

    Module& main_
        (*main_iter -> second);

    std::stack< std::pair<Expr_ptr, Module_ptr> > stack;
    stack.push( std::make_pair< Expr_ptr, Module_ptr >
                (em.make_empty(), &main_));

    /* walk of var decls, starting from main module */
    while (0 < stack.size()) {

        const std::pair< Expr_ptr, Module_ptr > top
            (stack.top());
        stack.pop();

        Expr_ptr ctx
            (top.first);
        Module& module
            (* top.second);

        /* module INITs */
        const ExprVector& init
            (module.init());
        process_init(ctx, init);

        /* module INVARs */
        const ExprVector& invar
            (module.invar());
        process_invar(ctx, invar);

        /* module TRANSes */
        const ExprVector& trans
            (module.trans());
        process_trans(ctx, trans);

        Variables attrs
            (module.vars());
        Variables::const_iterator vi;
        for (vi = attrs.begin(); attrs.end() != vi; ++ vi) {

            Expr_ptr id
                (vi -> first);
            Variable& var
                (* vi -> second);
            Type_ptr vtype
                (var.type());
            Expr_ptr local_ctx
                (em.make_dot( ctx, id));

            if (vtype -> is_instance()) {
                InstanceType_ptr instance
                    (vtype -> as_instance());
                Module&  module
                    (model.module(instance -> name()));

                stack.push( std::make_pair< Expr_ptr, Module_ptr >
                            (local_ctx, &module));
            }
        }
    } /* while() */

    /* processing environment extra constraints */
    const ExprVector& extra_init
        (env.extra_init());
    process_init(NULL, extra_init);

    /* environment INVARs */
    const ExprVector& extra_invar
        (env.extra_invar());
    process_invar(NULL, extra_invar);

    /* environment TRANSes */
    const ExprVector& extra_trans
        (env.extra_trans());
    process_trans(NULL, extra_trans);
}

void Algorithm::process_init(Expr_ptr ctx, const ExprVector& exprs)
{
    Compiler& cmpl
        (compiler()); // just a local ref

    for (ExprVector::const_iterator ii = exprs.begin(); ii != exprs.end(); ++ ii ) {

        Expr_ptr body
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

void Algorithm::process_invar(Expr_ptr ctx, const ExprVector& exprs)
{
    Compiler& cmpl
        (compiler()); // just a local ref

    for (ExprVector::const_iterator ii = exprs.begin(); ii != exprs.end(); ++ ii ) {

            Expr_ptr body
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

void Algorithm::process_trans(Expr_ptr ctx, const ExprVector& exprs)
{
    Compiler& cmpl
        (compiler()); // just a local ref

    for (ExprVector::const_iterator ti = exprs.begin(); ti != exprs.end(); ++ ti ) {
        Expr_ptr body
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

void Algorithm::assert_fsm_init(Engine& engine, step_t time, group_t group)
{
    for (CompilationUnits::const_iterator i = f_init.begin(); f_init.end() != i; ++ i)
        engine.push( *i, time, group);
}

void Algorithm::assert_fsm_invar(Engine& engine, step_t time, group_t group)
{
    for (CompilationUnits::const_iterator i = f_invar.begin(); f_invar.end() != i; ++ i)
        engine.push( *i, time, group);
}

void Algorithm::assert_fsm_trans(Engine& engine, step_t time, group_t group)
{
    for (CompilationUnits::const_iterator i = f_trans.begin(); f_trans.end() != i; ++ i)
        engine.push( *i, time, group);
}

void Algorithm::assert_fsm_uniqueness(Engine& engine, step_t j, step_t k, group_t group)
{
    SymbIter symbs
        (model(), NULL); // no COI support yet

    VarVector uniqueness_vars;

    /* define uniqueness_vars into the solver ... */
    while (symbs.has_next()) {
        std::pair< Expr_ptr, Symbol_ptr> pair( symbs.next());
        Expr_ptr ctx (pair.first);
        Symbol_ptr symb (pair.second);

        if (symb->is_variable()) {

            Variable& var
                (symb->as_variable());

            if (var.is_input() ||
                var.is_frozen() ||
                var.is_temp())
                continue ;

            Expr_ptr expr
                (var.name());

            TimedExpr key
                (em().make_dot( ctx, expr), 0);

            Encoding_ptr enc
                (f_bm.find_encoding(key));

            if (!enc)
                continue;

            DDVector::const_iterator di;
            unsigned ndx;
            for (ndx = 0, di = enc->bits().begin();
                 enc->bits().end() != di; ++ ndx, ++ di) {

                unsigned bit = (*di).getNode()->index;

                const UCBI& ucbi  = f_bm.find_ucbi(bit);
                const TCBI  jtcbi = TCBI(ucbi, j);
                const TCBI  ktcbi = TCBI(ucbi, k);

                Var jkne = engine.new_sat_var();
                uniqueness_vars.push_back(jkne);

                Var jvar = engine.tcbi_to_var(jtcbi);
                Var kvar = engine.tcbi_to_var(ktcbi);

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

    // ... and then assert at least one of them is true
    {
        vec<Lit> ps;
        ps.push( mkLit( group, true));

        for (VarVector::const_iterator eye = uniqueness_vars.begin();
             eye != uniqueness_vars.end(); ++ eye) {
            ps.push( mkLit( *eye, false));
        }

        engine.add_clause(ps);
    }
}

void Algorithm::assert_time_frame(Engine& engine,
                                  step_t time,
                                  TimeFrame& tf,
                                  group_t group)
{
    ExprMgr& em
        (ExprMgr::INSTANCE());
    Compiler& cmpl
        (compiler()); // just a local ref

    ExprVector assignments
        (tf.assignments());
    ExprVector::const_iterator i
        (assignments.begin());

    ResolverProxy resolver;

    unsigned count (0);
    while (i != assignments.end()) {

        Expr_ptr assignment
            (*i); ++ i;

        Expr_ptr full
            (assignment -> lhs());

        Symbol_ptr symb
            (resolver.symbol(full));

        if (symb -> is_variable()) {

            Expr_ptr scope
                (full -> lhs());

            Expr_ptr expr
                (em.make_eq( full -> rhs(),
                             assignment -> rhs()));

            try {
                ++ count;
                engine.push( cmpl.process(scope, expr), time, group);
            }

            catch (Exception& ae) {
                f_ok = false;

                pconst_char what
                    (ae.what());

                std::cerr
                    << what
                    << std::endl;

                free((void *) what);
                assert(false); // XXX
            }
        }
    }

    DEBUG
        << "Pushed " << count << " assignments"
        << std::endl;
}

void Algorithm::assert_formula(Engine& engine,
                               step_t time,
                               CompilationUnit& term,
                               group_t group)
{
    engine.push( term, time, group);
}

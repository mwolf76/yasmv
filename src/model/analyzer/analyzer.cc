/**
 * @file analyzer.cc
 * @brief Semantic analyzer module
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

#include <common/common.hh>

#include <expr/expr.hh>
#include <type/type.hh>
#include <symb/proxy.hh>

#include <sat/sat.hh>

#include <model/module.hh>
#include <model/analyzer/analyzer.hh>
#include <model/compiler/compiler.hh>

#include <utils/misc.hh>

Analyzer::Analyzer(ModelMgr& owner)
    : f_ctx_stack()
    , f_owner(owner)
{
    const void *instance
        (this);

    DRIVEL
        << "Created Analyzer @"
        << instance
        << std::endl;
}

Analyzer::~Analyzer()
{
    const void *instance
        (this);

    DRIVEL
        << "Destroying Analyzer @"
        << instance
        << std::endl;
}

void Analyzer::process(expr::Expr_ptr expr, expr::Expr_ptr ctx, analyze_section_t section)
{
    assert(section == ANALYZE_INIT  ||
           section == ANALYZE_INVAR ||
           section == ANALYZE_TRANS ||
           section == ANALYZE_DEFINE);

    // this needs to be set only once
    f_section = section;

    // remove previous results
    f_expr_stack.clear();
    f_ctx_stack.clear();

    // walk body in given ctx
    f_ctx_stack.push_back(ctx);

    // invoke walker on the body of the expr to be processed
    (*this)(expr);
    assert(! f_expr_stack.size());
}

void Analyzer::generate_framing_conditions()
{
    DEBUG
        << "Generating framing conditions ..."
        << std::endl ;

    /* identifer -> list of guards */
    typedef boost::unordered_map<expr::Expr_ptr, expr::ExprVector, utils::PtrHash, utils::PtrEq> ProcessingMap;

    expr::ExprMgr& em
        (owner().em());

    ProcessingMap map;

    /* pass 1: build a scheleton map */
    for (DependencyTrackingMap::const_iterator i = f_dependency_tracking_map.begin();
         i != f_dependency_tracking_map.end(); ++ i) {

        expr::Expr_ptr ident
            (i->second);

        ProcessingMap::const_iterator pmi
            (map.find(ident));

        if (map.end() == pmi)
            map.insert(
                std::pair<expr::Expr_ptr, expr::ExprVector>
                (ident, expr::ExprVector()));
    }

    /* pass 2: group together all guards associated with each var identifier */
    for (DependencyTrackingMap::const_iterator i = f_dependency_tracking_map.begin();
         i != f_dependency_tracking_map.end(); ++ i) {

        expr::Expr_ptr guard
            (i->first);

        expr::Expr_ptr ident
            (i->second);

        ProcessingMap::iterator pmi
            (map.find(ident));

        /* right? */
        assert(map.end() != pmi);

        expr::ExprVector& ev
            (pmi->second);

        ev.push_back(guard);
    }

    /* pass 3: for each group of clauses, for each pair <p, q>, p and q must be
       mutually exclusive (i.e. `p ^ q` must be UNSAT). */
    for (ProcessingMap::iterator i = map.begin();
         i != map.end(); ++ i) {

        expr::Expr_ptr ident
            (i->first);

        const expr::ExprVector& ev
            (i->second);

        unsigned input_length
            (ev.size());

        if (2 <= input_length) {
            for (unsigned i = 0; i < input_length - 1; ++ i) {
                expr::Expr_ptr p
                    (ev[i]);

                for (unsigned j = i + 1; j < input_length; ++ j) {
                    expr::Expr_ptr q
                        (ev[j]);

                    if (! mutually_exclusive(p, q)) {
                        INFO
                            << "Found two guards that could be NOT mutually exclusive for identifier `"
                            << ident
                            << "`: `"
                            << p
                            << "` and `"
                            << q
                            << "`"
                            << std::endl;
                    }
                }
            }
        }
    }

    /* pass 4: for each expr vector, build the conjunction of all (mutually
       exclusive) negated guards and associate it to the variable identifier.
       The resulting expr will be used as guard for a newly generated TRANS of
       the form: <guard> -> <var> := var. */
    Module& main
        (owner().model().main_module());

    for (ProcessingMap::iterator i = map.begin();
         i != map.end(); ++ i) {

        expr::Expr_ptr ident
            (i->first);

        expr::ExprVector& ev
            (i->second);

        expr::Expr_ptr guard
            (NULL);

        for (expr::ExprVector::const_iterator j = ev.begin();
             j != ev.end(); ++ j) {

            expr::Expr_ptr expr
                (*j);

            guard = (guard)
                ? em.make_and(guard, em.make_not(expr))
                : em.make_not(expr)
                ;
        }

        /* synthetic TRANS will be added to the module. */
        expr::Expr_ptr synth_trans
            (em.make_implies(guard,
                             em.make_eq(em.make_next(ident),
                                        ident)));
        INFO
            << "Adding inertial INVAR: "
            << synth_trans
            << std::endl;

        main.add_trans(synth_trans);
    }
}

// under model invariants
bool Analyzer::mutually_exclusive(expr::Expr_ptr p, expr::Expr_ptr q)
{
    DEBUG
        << "Testing `"
        << p
        << "` && `"
        << q
        << "` for unsatisfiability ..."
        << std::endl ;

    expr::ExprMgr& em
        (owner().em());

    Engine engine
        ("Analyzer");

    Compiler compiler;

    expr::Expr_ptr ctx
        (em.make_empty());

    /* adding INVARs @0 and @1 from main module */
    const expr::ExprVector& invar
        (ModelMgr::INSTANCE().model().main_module().invar());
    for (expr::ExprVector::const_iterator ii = invar.begin();
         ii != invar.end(); ++ ii ) {

        expr::Expr_ptr body
            (*ii);

        DEBUG
            << "Pushing INVAR "
            << ctx << "::" << body
            << std::endl;

        engine.push(compiler.process(ctx, body), 0);
        engine.push(compiler.process(ctx, body), 1);
    }

    engine.push(compiler.process(ctx, p), 0);
    engine.push(compiler.process(ctx, q), 0);

    status_t status
        (engine.solve());

    return status == STATUS_UNSAT;
}

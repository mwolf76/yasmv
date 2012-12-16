/**
 *  @file MC Algorithm.hh
 *  @brief K-Induction mc algorithm
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
#include <kind/kind.hh>
using namespace Minisat;

KInduction::KInduction(IModel& model, Expr_ptr property)
    : MCAlgorithm(model, property)
{
    prepare();
}

KInduction::~KInduction()
{}

void KInduction::prepare()
{
    const Modules& modules = model().modules();
    for (Modules::const_iterator m = modules.begin();
         m != modules.end(); ++ m) {

        Module& module = dynamic_cast <Module&> (*m->second);

        /* INIT */
        const ExprVector init = module.init();
        for (ExprVector::const_iterator init_eye = init.begin();
             init_eye != init.end(); ++ init_eye) {

            Expr_ptr ctx = module.expr();
            Expr_ptr body = (*init_eye);

            f_not_init_adds.push_back(compiler().process(ctx,
                                                         em().make_not(body)));
        }
    }
}

void KInduction::assert_fsm_not_init(step_t time, group_t group, color_t color)
{
    clock_t t0 = clock();
    unsigned n = f_not_init_adds.size();
    TRACE << "CNFizing NOT INITs @" << time
          << "... (" << n << " formulas)"
          << endl;

    ADDVector::iterator i;
    for (i = f_not_init_adds.begin(); f_not_init_adds.end() != i; ++ i) {
        engine().push( *i, time, group, color);
    }

    clock_t elapsed = clock() - t0;
    double secs = (double) elapsed / (double) CLOCKS_PER_SEC;
    TRACE << "Done. (took " << secs << " seconds)" << endl;
}

void KInduction::process()
{
    step_t k; // to infinity...
    bool leave = false; // TODO: somebody telling us to stop

    assert_fsm_init(0);
    assert_fsm_trans(0);
    assert_invariant(0);

    assert_fsm_not_init(1);
    assert_violation(1, engine().new_group());

    TRACE << "Trying to prove invariant using K-induction, k = 1..." << endl;
    if (STATUS_SAT == engine().solve()) {

        k = 1; do {

            /* disable last violation */
            engine().toggle_last_group();

            assert_fsm_trans(k);
            assert_invariant(k);

            ++ k;
            assert_fsm_not_init(k);
            assert_violation(k, engine().new_group());

            TRACE << "Trying to prove invariant using K-induction, k = "
                  << k << "..."
                  << endl;

        } while ((STATUS_SAT == engine().solve()) && !leave);
    }

    if (STATUS_UNSAT == engine().status()) {
        TRACE << "Found K-induction proof (k = " << k
              << "), invariant is TRUE." << endl;
        set_status(MC_TRUE);
    }

    TRACE << "Done." << endl;
}

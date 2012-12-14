/**
 *  @file MC Algorithm.hh
 *  @brief SAT BMC Algorithm
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
#include <bmc.hh>
using namespace Minisat;

SATBMCFalsification::SATBMCFalsification(IModel& model,
                                         Expr_ptr property)
    : MCAlgorithm(model, property)
    , f_factory(CuddMgr::INSTANCE().dd())
    , f_engine(f_factory)
    , f_compiler()
{}

SATBMCFalsification::~SATBMCFalsification()
{}

void SATBMCFalsification::prepare()
{
    f_init_adds.clear();
    const Modules& modules = f_model.modules();
    for (Modules::const_iterator m = modules.begin();
         m != modules.end(); ++ m) {

        Module& module = dynamic_cast <Module&> (*m->second);

        /* INIT */
        const ExprVector init = module.init();
        for (ExprVector::const_iterator init_eye = init.begin();
             init_eye != init.end(); ++ init_eye) {

            Expr_ptr ctx = module.expr();
            Expr_ptr body = (*init_eye);

            /* Compiler produces an ADD */
            f_init_adds.push_back(f_compiler.process(ctx, body));
        }

        /* TRANS */
        const ExprVector trans = module.trans();
        for (ExprVector::const_iterator trans_eye = trans.begin();
             trans_eye != trans.end(); ++ trans_eye) {

            Expr_ptr ctx = module.expr();
            Expr_ptr body = (*trans_eye);

            /* Compiler produces an ADD */
            f_trans_adds.push_back(f_compiler.process(ctx, body));
        }

        /* Violation (negation of ASSERT) */
        f_violation_add = f_compiler.process( f_em.make_main(),
                                              f_em.make_not(f_property));
    }
}

void SATBMCFalsification::assert_fsm_init()
{
    clock_t t0 = clock();
    unsigned n = f_init_adds.size();
    TRACE << "CNFizing INITs ... ("
          << n << " formulas)"
          << endl;

    ADDVector::iterator i;
    for (i = f_init_adds.begin(); f_init_adds.end() != i; ++ i) {
        f_engine.push( *i, 0, MAINGROUP, BACKGROUND);
    }

    clock_t elapsed = clock() - t0;
    double secs = (double) elapsed / (double) CLOCKS_PER_SEC;
    TRACE << "Done. (took " << secs << " seconds)" << endl;
}

void SATBMCFalsification::assert_fsm_trans(step_t time)
{
    clock_t t0 = clock();
    unsigned n = f_trans_adds.size();

    TRACE << "CNFizing TRANSes @" << time
          << "... (" << n << " formulas)"
          << endl;

    ADDVector::iterator i;
    for (i = f_trans_adds.begin(); f_trans_adds.end() != i; ++ i) {
        f_engine.push( *i, time, MAINGROUP, BACKGROUND);
    }

    clock_t elapsed = clock() - t0;
    double secs = (double) elapsed / (double) CLOCKS_PER_SEC;
    TRACE << "Done. (took " << secs << " seconds)" << endl;
}

void SATBMCFalsification::assert_violation(step_t time)
{
    clock_t t0 = clock();
    TRACE << "CNFizing Violation @"
          << time << endl;

    f_engine.push( f_violation_add, time,
                   f_engine.new_group(), BACKGROUND);

    clock_t elapsed = clock() - t0;
    double secs = (double) elapsed / (double) CLOCKS_PER_SEC;
    TRACE << "Done. (took " << secs << " seconds)" << endl;
}

void SATBMCFalsification::process()
{
    step_t i, k = 20; // TODO

    prepare();
    assert_fsm_init();
    assert_violation(0);

    TRACE << "Looking for a BMC CEX of length 0" << endl;

    if (STATUS_UNSAT == f_engine.solve()) {

        i = 0; do {
            /* disable last violation */
            (*f_engine.groups().rbegin()) *= -1;

            assert_fsm_trans(i ++);
            assert_violation(i);

            TRACE << "Looking for a BMC CEX of length "
                  << i << endl;

        } while ((STATUS_UNSAT == f_engine.solve()) && (i < k));
    }

    if (STATUS_SAT == f_engine.status()) {
        f_status = MC_FALSE;

        /* cex extraction */
        ostringstream oss; oss << "CEX for '" << f_property << "'";
        Witness& cex = * new BMCCounterExample(f_property, model(), f_engine, i, false);

        // TODO: register
    }

    TRACE << "Done." << endl;
}

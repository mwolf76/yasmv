/**
 *  @file MC Algorithm.hh
 *  @brief SAT Simulation Algorithm
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
#include <sim/simulation.hh>

Simulation::Simulation(IModel& model,
                       Expr_ptr halt_cond,
                       Expr_ptr resume_id,
                       ExprVector& constraints)
    : Algorithm()
    , f_model(model)
    , f_witness(NULL)
    , f_halt_cond(halt_cond)
    , f_constraints(constraints)
{
    if (resume_id) {
        Witness& w = WitnessMgr::INSTANCE().witness( resume_id );
        set_witness(w);
    }
}

Simulation::~Simulation()
{}

void Simulation::set_status(simulation_status_t status)
{ f_status = status; }

void Simulation::set_witness(Witness& witness)
{
    if (f_witness) {
        delete f_witness;
    }

    f_witness = & witness;
}

void Simulation::process()
{
    /* ensure internal structures are empty */
    assert( 0 == f_init_adds.size());
    assert( 0 == f_invar_adds.size());
    assert( 0 == f_trans_adds.size());

    Compiler& cmpl(compiler());
    for (int pass = 0; pass < 2; ++ pass) {
        bool first_pass = (0 == pass);

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

                cmpl.process(ctx, body, first_pass);
                if (! first_pass) {
                    while (cmpl.has_next()) {
                        f_init_adds.push_back(cmpl.next());
                    }
                }
            }

            /* INVAR */
            const ExprVector invar = module.invar();
            for (ExprVector::const_iterator invar_eye = invar.begin();
                 invar_eye != invar.end(); ++ invar_eye) {

                Expr_ptr ctx = module.expr();
                Expr_ptr body = (*invar_eye);

                cmpl.process(ctx, body, first_pass);
                if (! first_pass) {
                    while (cmpl.has_next()) {
                        f_invar_adds.push_back(cmpl.next());
                    }
                }
            }

            /* TRANS */
            const ExprVector trans = module.trans();
            for (ExprVector::const_iterator trans_eye = trans.begin();
                 trans_eye != trans.end(); ++ trans_eye) {

                Expr_ptr ctx = module.expr();
                Expr_ptr body = (*trans_eye);

                cmpl.process(ctx, body, first_pass);
                if (! first_pass) {
                    while (cmpl.has_next()) {
                        f_trans_adds.push_back(cmpl.next());
                    }
                }
            }
        }
    }

    ExprMgr& em = ExprMgr::INSTANCE();
    WitnessMgr& wm = WitnessMgr::INSTANCE();

    bool halt = false; sigint_caught = 0;
    step_t k  = 0;

    set_status( SIMULATION_SAT ); // optimic assumption

    // if a witness is already there, we're resuming a previous
    // simulation. Hence, no need for initial states.
    if (! has_witness()) {
        assert_fsm_init(0);
        assert_fsm_invar(0);
        TRACE << "Starting simulation..." << endl;
    }
    else {
        // here we need to push all the values for variables in the
        // last state of resuming witness. A complete assignment to
        // all state variables ensures full deterministic behavior.

        k = witness().size() -1;
        assert( false) ; // TODO
        TRACE << "Resuming simulation..." << endl;
    }

    if (STATUS_SAT == engine().solve()) {
        Witness_ptr w = new SimulationWitness( model(), engine(), k);

        if (! has_witness()) {
            set_witness(*w);
        }
        else {
            witness().extend(*w);
        }

        halt = wm.eval ( witness(), em.make_main(), f_halt_cond, k);
        if (!halt) {
            do {
                assert_fsm_trans(k ++);
                assert_fsm_invar(k);
                os () << "-- completed step " << k << endl;

                if (STATUS_SAT == engine().solve()) {
                    Witness_ptr w = new SimulationWitness( model(), engine(), k);

                    // SymbIter vars( model(), NULL );
                    // bool first = true;
                    // while (vars.has_next()) {
                    //     ISymbol_ptr symb = vars.next();
                    //     FQExpr key(symb->ctx(), symb->expr(), k-1);

                    //     if (first) {
                    //         os() << "-- " << k << " --" << endl;
                    //         first = false;
                    //     }
                    //     os() << symb->expr() << "=" << w->value(key)
                    //          << endl;
                    // }

                    witness().extend(*w);

                    /* eval halt condition */
                    halt = sigint_caught || wm.eval ( witness(), em.make_main(), f_halt_cond, k);
                }
            } while (STATUS_SAT == engine().status() && ! halt);
        }
        else {
            TRACE << "Inconsistency detected in transition relation at step " << k
                  << ". Simulation aborted."
                  << endl;

            set_status( SIMULATION_UNSAT );
        }
    }
    else {
        TRACE << "Inconsistency detected in initial states. Simulation aborted."
              << endl;

        set_status( SIMULATION_UNSAT );
    }

    if (halt) {
        TRACE << "Simulation reached HALT condition"
              << endl;
    }

    TRACE << "Done." << endl;
}

void Simulation::assert_fsm_init(step_t time, group_t group, color_t color)
{
    clock_t t0 = clock();
    unsigned n = f_init_adds.size();
    TRACE << "CNFizing INITs @" << time
          << "... (" << n << " formulas)"
          << endl;

    ADDVector::iterator i;
    for (i = f_init_adds.begin(); f_init_adds.end() != i; ++ i) {
        engine().push( *i, time, group, color);
    }

    clock_t elapsed = clock() - t0;
    double secs = (double) elapsed / (double) CLOCKS_PER_SEC;
    TRACE << "Done. (took " << secs << " seconds)" << endl;
}

void Simulation::assert_fsm_invar(step_t time, group_t group, color_t color)
{
    clock_t t0 = clock();
    unsigned n = f_invar_adds.size();
    TRACE << "CNFizing INVARs @" << time
          << "... (" << n << " formulas)"
          << endl;

    ADDVector::iterator i;
    for (i = f_invar_adds.begin(); f_invar_adds.end() != i; ++ i) {
        engine().push( *i, time, group, color);
    }

    clock_t elapsed = clock() - t0;
    double secs = (double) elapsed / (double) CLOCKS_PER_SEC;
    TRACE << "Done. (took " << secs << " seconds)" << endl;
}

void Simulation::assert_fsm_trans(step_t time, group_t group, color_t color)
{
    clock_t t0 = clock();
    unsigned n = f_trans_adds.size();

    TRACE << "CNFizing TRANSes @" << time
          << "... (" << n << " formulas)"
          << endl;

    ADDVector::iterator i;
    for (i = f_trans_adds.begin(); f_trans_adds.end() != i; ++ i) {
        engine().push( *i, time, group, color);
    }

    clock_t elapsed = clock() - t0;
    double secs = (double) elapsed / (double) CLOCKS_PER_SEC;
    TRACE << "Done. (took " << secs << " seconds)" << endl;
}

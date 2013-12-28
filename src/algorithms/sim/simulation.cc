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
    : Algorithm(model)
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

void Simulation::process()
{
    clock_t t0 = clock(), t1;
    double secs;

    /* ensure internal structures are empty */
    assert( 0 == f_init_adds.size());
    assert( 0 == f_invar_adds.size());
    assert( 0 == f_trans_adds.size());

    TRACE << "Phase 1" << endl;
    prepare();

    TRACE << "Phase 2" << endl;
    compile();

    TRACE << "Phase 3" << endl;
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
        t1 = clock(); secs = (double) (t1 - t0) / (double) CLOCKS_PER_SEC;
        os () << "-- simulation initialized, took " << secs
              << " seconds" << endl;
        t0 = t1; // resetting clock

        Witness_ptr w = new SimulationWitness( model(), engine(), k);
        if (! has_witness()) {
            set_witness(*w);
        }
        else {
            witness().extend(*w);
        }

        /* HALT condition can either be:
           1. a boolean formula; (halts when true)
           2. a non-negative integer constant; (number of steps to be executed)
           3. NULL (no halt condition)
        */
        if (sigint_caught) {
            halt = true;
        }
        else if (NULL != f_halt_cond) {
            if ( em.is_constant( f_halt_cond)) {
                halt = (0 == f_halt_cond->value());
                f_halt_cond = em.make_const( f_halt_cond->value() -1);
            }
            else {
                halt = wm.eval ( witness(), em.make_main(), f_halt_cond, k);
            }
        }
        if (!halt) {

            do {
                t1 = clock(); secs = (double) (t1 - t0) / (double) CLOCKS_PER_SEC;
                os () << "-- completed step " << 1 + k
                      << ", took " << secs << " seconds"
                      << endl;
                t0 = t1; // resetting clock

                assert_fsm_trans(k ++);
                assert_fsm_invar(k);

                if (STATUS_SAT == engine().solve()) {
                    Witness_ptr w = new SimulationWitness( model(), engine(), k);
                    witness().extend(*w);

                    if (sigint_caught) {
                        halt = true;
                    }
                    if (NULL != f_halt_cond) {
                        if ( em.is_constant( f_halt_cond)) {
                            halt = (0 == f_halt_cond->value());
                            f_halt_cond = em.make_const( f_halt_cond->value() -1);
                        }
                        else {
                            halt = wm.eval ( witness(), em.make_main(), f_halt_cond, k);
                        }
                    }
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

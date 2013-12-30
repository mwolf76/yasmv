/**
 *  @file simulation.cc
 *  @brief SAT-based BMC simulation algorithm
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
                       Expr_ptr condition,
                       Expr_ptr resume_id,
                       ExprVector& constraints)
    : Algorithm(model)
    , f_halt_cond( NULL )
    , f_nsteps( NULL )
    , f_constraints(constraints)
{
    ExprMgr& em (ExprMgr::INSTANCE());
    if (NULL != condition) {
        if (em.is_constant( condition)) {
            f_nsteps = condition;
        }
        else {
            f_halt_cond = condition;
        }
    }
    if (resume_id) {
        Atom wid (resume_id->atom());
        Witness& w = WitnessMgr::INSTANCE().witness(wid);
        set_witness(w);
    }
}

Simulation::~Simulation()
{}

void Simulation::process()
{
    clock_t t0 = clock(), t1;
    double secs;

    TRACE << "Phase 1" << endl;
    prepare();

    TRACE << "Phase 2" << endl;
    compile();

    TRACE << "Phase 3" << endl;
    ExprMgr& em = ExprMgr::INSTANCE();
    WitnessMgr& wm = WitnessMgr::INSTANCE();

    sigint_caught = 0;
    step_t k  = 0;

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
        // *all* state variables ensures full deterministic behavior
        // (cfr. simulation restart).
#if 0
        k = witness().size() -1;
        assert( false) ; // TODO
        TRACE << "Resuming simulation..." << endl;
#else
        assert(0); // not now
#endif
    }

    if (STATUS_SAT == engine().solve()) {
        t1 = clock(); secs = (double) (t1 - t0) / (double) CLOCKS_PER_SEC;
        os () << "-- simulation initialized, took " << secs
              << " seconds" << endl;
        t0 = t1; // resetting clock

        if (! has_witness()) {
            Witness_ptr w = new SimulationWitness( model(), engine(), k, true);
            wm.register_witness(*w);
            set_witness(*w);
        }
        else {
            Witness_ptr w = new SimulationWitness( model(), engine(), k);
            witness().extend(*w);
        }

        /* halt simulation? */
        if (sigint_caught) {
            f_status = SIMULATION_INTERRUPTED;
            return;
        }
        else if (NULL != f_halt_cond && wm.eval ( witness(),
                                                  em.make_main(),
                                                  f_halt_cond, k)) {
            f_status = SIMULATION_HALTED;
            return;
        }
        else if (NULL != f_nsteps) {
            if (0 == f_nsteps->value()) {
                f_status = SIMULATION_DONE;
                return;
            }
            f_nsteps = em.make_const( f_nsteps->value() -1);
        }

        while (true) {
            t1 = clock(); secs = (double) (t1 - t0) / (double) CLOCKS_PER_SEC;
            os () << "-- completed step " << 1 + k
                  << ", took " << secs << " seconds"
                  << endl;
            t0 = t1; // resetting clock

            // one more cup of coffe for the road
            // TODO: SAT restart after a given number of steps (e.g. 10) would help
            // preventing performance degradation as k grows larger.
            assert_fsm_trans(k ++);
            assert_fsm_invar(k);

            if (STATUS_SAT == engine().solve()) {
                Witness_ptr w = new SimulationWitness( model(), engine(), k);
                witness().extend(*w);

                if (sigint_caught) {
                    f_status = SIMULATION_INTERRUPTED;
                    return;
                }
                else if (NULL != f_halt_cond && wm.eval ( witness(),
                                                          em.make_main(),
                                                          f_halt_cond, k)) {
                    f_status = SIMULATION_HALTED;
                    return;
                }
                else if (NULL != f_nsteps) {
                    if (0 == f_nsteps->value()) {
                        f_status = SIMULATION_DONE;
                        return;
                    }
                    f_nsteps = em.make_const( f_nsteps->value() -1);
                }
            }
            else {
                TRACE << "Inconsistency detected in transition relation at step " << k
                      << endl;
                f_status = SIMULATION_DEADLOCKED;
                return;
            }
        }
    }
    else {
        TRACE << "Inconsistency detected in initial states"
              << endl;
        f_status = SIMULATION_DEADLOCKED;
    }
}

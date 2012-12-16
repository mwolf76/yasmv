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

Simulation::Simulation(IModel& model, int resume,
                       int nsteps, ExprVector& constraints)
    : Algorithm(model)
    , f_resume(resume)
    , f_nsteps(nsteps)
    , f_constraints(constraints)
{}

Simulation::~Simulation()
{}

simulation_status_t Simulation::status() const
{ return f_status; }

void Simulation::set_status(simulation_status_t status)
{ f_status = status; }

void Simulation::process()
{
    step_t k = 0; // to infinity...
    bool leave = false; // TODO: somebody telling us to stop

    assert_fsm_init(0);
    TRACE << "Starting simulation..." << endl;

    if (STATUS_SAT == engine().solve()) {

        do {
            assert_fsm_trans(k); ++ k;
            TRACE << "Simulating step " << k << endl;
        } while (STATUS_SAT == engine().solve() && ! leave);

        if (STATUS_SAT == engine().status()) {

            TRACE << "Extracting simulation witness (k = " << k << ")."
                  << endl;

            set_status( SIMULATION_SAT );

            // /* CEX extraction */
            // ostringstream oss; oss << "CEX for '" << f_property << "'";
            // Witness& witness = * new SimulationWitness(f_property, model(),
            //                                            engine(), k, false);

            // TODO: register
        }

        else {
            TRACE << "Inconsistency detected in TRANS, step " << k
                  << ". Simulation aborted."
                  << endl;

            set_status( SIMULATION_UNSAT );
        }
    }

    else {
        TRACE << "Inconsistency detected in INIT. Simulation aborted."
              << endl;

        set_status( SIMULATION_UNSAT );
    }

    TRACE << "Done." << endl;
}

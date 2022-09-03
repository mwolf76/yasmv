/**
 * @file simulation.hh
 * @brief SAT-based BMC simulation algorithm
 *
 * This header file contains the declarations required to implement
 * the FSM simulation algorithm.
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

#ifndef SIMULATION_ALGORITHM_H
#define SIMULATION_ALGORITHM_H

#include <algorithms/base.hh>

#include <witness/witness.hh>
#include <witness/witness_mgr.hh>

#include <cmd/command.hh>

namespace sim {

    typedef enum {
        SIMULATION_DONE,
        SIMULATION_DEADLOCKED,
        SIMULATION_INTERRUPTED,
        SIMULATION_UNKNOWN,
    } simulation_status_t;

    class Simulation: public algorithms::Algorithm {

    public:
        Simulation(cmd::Command& command, model::Model& model);
        ~Simulation();

        // returns the number of enumerated states
        value_t pick_state(expr::ExprVector constraints, bool all_sat, bool count, value_t limit);

        // returns the status of the simulation
        simulation_status_t simulate(expr::ExprVector constraints, pconst_char trace_uid);

    private:
        expr::ExprVector f_constraints;

        void extract_witness(sat::Engine& engine, bool select_current_witness);
        void exclude_state(sat::Engine& engine);
    };

    class SimulationWitness: public witness::Witness {

    public:
        SimulationWitness(model::Model& model, sat::Engine& engine, step_t k);
    };

} // namespace sim

#endif /* SIMULATION_ALGORITHM_H */

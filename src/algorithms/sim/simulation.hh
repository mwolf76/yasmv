/**
 *  @file Simulation Algorithm.hh
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

#ifndef SIMULATION_ALGORITHM_H
#define SIMULATION_ALGORITHM_H

#include <base.hh>
#include <witness.hh>

typedef enum {
    SIMULATION_UNSAT,
    SIMULATION_SAT,
    SIMULATION_UNKNOWN,
} simulation_status_t;

class Simulation : public Algorithm {

public:
    Simulation(IModel& model, int resume,
               int nsteps, ExprVector& constraints);

    ~Simulation();

    void process();

    inline simulation_status_t status() const
    { return f_status; }

    inline IModel& model()
    { return f_model; }

private:
    IModel& f_model;

    int f_resume;
    int f_nsteps;
    ExprVector f_constraints;

    simulation_status_t f_status;
    void set_status(simulation_status_t status);

    ADDVector f_init_adds;
    ADDVector f_trans_adds;

    void assert_fsm_init (step_t time,
                          group_t group = MAINGROUP,
                          color_t color = BACKGROUND);

    void assert_fsm_trans(step_t time,
                          group_t group = MAINGROUP,
                          color_t color = BACKGROUND);

};

class SimulationWitness : public Witness {
public:
    SimulationWitness(IModel& model, SAT& engine, unsigned k);
};

#endif

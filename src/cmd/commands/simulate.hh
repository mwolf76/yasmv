/*
 * @file simulate.hh
 * @brief Command-interpreter subsystem related classes and definitions.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/
#ifndef SIMULATE_H_CMD
#define SIMULATE_H_CMD

#include <cmd/command.hh>
#include <algorithms/sim/simulation.hh>

class Simulate : public Command {
public:
    Simulate(Interpreter& owner, Expr_ptr phi);
    virtual ~Simulate();

    Variant virtual operator()();

private:
    /* Optional propositional constraints */
    Expr_ptr f_phi;

    /* Simulation machinery */
    Simulation f_sim;

    Variant run();
};

#endif

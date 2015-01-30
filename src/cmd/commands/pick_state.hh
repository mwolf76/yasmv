/*
 * @file pick_state.hh
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
#ifndef PICK_STATE_CMD_H
#define PICK_STATE_CMD_H

#include <cmd/command.hh>
#include <algorithms/sim/simulation.hh>

class PickState : public Command {
public:
    PickState(Interpreter& owner);
    virtual ~PickState();

    Variant virtual operator()();

    void set_init_condition(Expr_ptr init_condition);
    inline Expr_ptr init_condition() const
    { return f_init_condition; }

    void set_trace_uid(Expr_ptr trace_uid);
    inline Expr_ptr trace_uid() const
    { return f_trace_uid; }

private:
    Expr_ptr f_init_condition;
    Expr_ptr f_trace_uid;

    // Simulation machinery
    Simulation f_sim;

    Variant run();
};

#endif

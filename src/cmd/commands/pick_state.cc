/*
 * @file pick_state.cc
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
#include <cmd/commands/pick_state.hh>

PickState::PickState(Interpreter& owner)
    : Command(owner)
    , f_init_condition(NULL)
    , f_trace_uid(NULL)
    , f_sim(*this, ModelMgr::INSTANCE().model())
{}

PickState::~PickState()
{}

void PickState::set_init_condition(Expr_ptr init_condition)
{ f_init_condition = init_condition; }

void PickState::set_trace_uid(Expr_ptr trace_uid)
{ f_trace_uid = trace_uid; }

Variant PickState::operator()()
{ return run(); }

Variant PickState::run()
{
    std::ostringstream tmp;

    f_sim.pick_state(f_init_condition, f_trace_uid);

    switch (f_sim.status()) {
    case SIMULATION_DONE:
        tmp << "Simulation done";
        break;
    case SIMULATION_INITIALIZED:
        tmp << "Simulation initialized";
        break;
    case SIMULATION_DEADLOCKED:
        tmp << "Simulation deadlocked";
        break;
    case SIMULATION_INTERRUPTED:
        tmp << "Simulation interrupted";
        break;
    default: assert( false ); /* unreachable */
    } /* switch */
    if (f_sim.has_witness()) {
        tmp
            << ", registered witness `"
            << f_sim.witness().id() << "`";
    }
    else {
        tmp
            << "(no witness available)";
    }
    return Variant(tmp.str());
}

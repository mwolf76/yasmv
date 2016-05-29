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
{}

PickState::~PickState()
{
    free(f_trace_uid);
    f_trace_uid = NULL;
}

void PickState::set_init_condition(Expr_ptr init_condition)
{
    f_init_condition = init_condition;
}

void PickState::set_trace_uid(pconst_char trace_uid)
{
    free(f_trace_uid);
    f_trace_uid = strdup(trace_uid);
}

Variant PickState::operator()()
{
    std::ostringstream tmp;

    Simulation sim
        (*this, ModelMgr::INSTANCE().model());

    sim.pick_state(f_init_condition, f_trace_uid);

    switch (sim.status()) {
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
    if (sim.has_witness()) {
        tmp
            << ", registered witness `"
            << sim.witness().id() << "`";
    }
    else {
        tmp
            << "(no witness available)";
    }
    return Variant(tmp.str());
}

void PickState::usage()
{
    std::cout
        << "pick-state [ -c <expr> ] - Initializes a new simulation."
        << std::endl
        << std::endl
        << "options:"
        << std::endl
        << "  -c <expr>, specifies an additional constraint (INIT)."
        << std::endl
        << std::endl
        << "Creates a new trace and selects it as current." ;
}


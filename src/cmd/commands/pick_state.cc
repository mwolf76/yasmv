/**
 * @file pick_state.cc
 * @brief Command `pick-state` class implementation.
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

#include <cmd/commands/commands.hh>
#include <cmd/commands/pick_state.hh>

PickState::PickState(Interpreter& owner)
    : Command(owner)
    , f_allsat(false)
    , f_limit(-1)
{}

PickState::~PickState()
{}

void PickState::set_allsat(bool allsat)
{
    f_allsat = allsat;
}

void PickState::set_limit(value_t limit)
{
    f_limit = limit;
}

Variant PickState::operator()()
{
    OptsMgr& om { OptsMgr::INSTANCE() };
    std::ostream& out { std::cout };
    bool res { false };

    Simulation sim
        (*this, ModelMgr::INSTANCE().model());

    sim.pick_state(f_allsat, f_limit);

    switch (sim.status()) {
    case SIMULATION_DONE:
        res = true;
        if (! om.quiet())
            out
                << outPrefix;
        out
            << "Simulation done";

        assert (sim.has_witness());
        out
            << ", registered witness `"
            << sim.witness().id()
            << "`"
            << std::endl;
        break;

    case SIMULATION_INITIALIZED:
        res = true;
        if (! om.quiet())
            out
                << outPrefix;
        out
            << "Simulation initialized" ;

        assert (sim.has_witness());
        out
            << ", registered witness `"
            << sim.witness().id()
            << "`"
            << std::endl;
        break;

    case SIMULATION_DEADLOCKED:
        if (! om.quiet())
            out
                << wrnPrefix;
        out
            << "Simulation deadlocked"
            << std::endl;
        break;

    case SIMULATION_INTERRUPTED:
        if (! om.quiet())
            out
                << wrnPrefix;
        out
            << "Simulation interrupted"
            << std::endl;
        break;

    default: assert( false ); /* unreachable */
    }

    return Variant(res ? okMessage : errMessage);
}

PickStateTopic::PickStateTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

PickStateTopic::~PickStateTopic()
{
    TRACE
        << "Destroyed pick-state topic"
        << std::endl;
}

void PickStateTopic::usage()
{
    std::cout
        << "pick-state [ -a | -l <limit> ] - Initializes a new simulation.\n\n"
        << "options:\n"
        << "  -a, requires an ALLSAT enumeration of all feasible initial states.\n"
        << "  -l <limit>, limits the number of enumerated solutions. Default is infinity.\n\n"
        << "Creates a new trace and selects it as current. If -a is used a number of traces\n"
        << "will be created, according to the number of distinct feasible initial states for\n"
        << "for the simulation.\n" ;
}

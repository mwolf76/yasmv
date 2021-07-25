/*
 * @file simulate.cc
 * @brief Command `simulate` class implementation.
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

#include <cstdlib>
#include <cstring>

#include <cmd/commands/commands.hh>
#include <cmd/commands/simulate.hh>

Simulate::Simulate(Interpreter& owner)
    : Command(owner)
    , f_out(std::cout)
    , f_invar_condition(NULL)
    , f_until_condition(NULL)
    , f_k(1)
    , f_trace_uid(NULL)
{}


Simulate::~Simulate()
{
    free(f_trace_uid);
    f_trace_uid = NULL;
}

void Simulate::set_invar_condition(Expr_ptr invar_condition)
{
    f_invar_condition = invar_condition;

    ERR
        << "Additional constraint: "
        << invar_condition
        << std::endl;
}

void Simulate::set_until_condition(Expr_ptr until_condition)
{
    f_until_condition = until_condition;
}

void Simulate::set_trace_uid(pconst_char trace_uid)
{
    free(f_trace_uid);
    f_trace_uid = strdup(trace_uid);
}

void Simulate::set_k(step_t k)
{
    f_k = k;
}

Variant Simulate::operator()()
{
    OptsMgr& om
        (OptsMgr::INSTANCE());

    ModelMgr& mm
        (ModelMgr::INSTANCE());

    sim::Simulation simulation
        (*this, mm.model());

    bool res { false };

    ExprVector f_constraints;
    simulation.simulate(f_invar_condition,
                 f_until_condition,
                 f_constraints,
                 f_k, f_trace_uid);

    switch (simulation.status()) {
    case sim::simulation_status_t::SIMULATION_DONE:
        res = true;
        if (! om.quiet())
            f_out
                << outPrefix;
        f_out
            << "Simulation done";
        break;

    case sim::simulation_status_t::SIMULATION_INITIALIZED:
        if (! om.quiet())
            f_out
                << outPrefix;
        f_out
            << "Simulation initialized"
            << std::endl;
        break;

    case sim::simulation_status_t::SIMULATION_DEADLOCKED:
        if (! om.quiet())
            f_out
                << wrnPrefix;
        f_out
            << "Simulation deadlocked"
            << std::endl;
        break;

    case sim::simulation_status_t::SIMULATION_INTERRUPTED:
        if (! om.quiet())
            f_out
                << wrnPrefix;
        f_out
            << "Simulation interrupted"
            << std::endl;
        break;

    default: assert( false ); /* unreachable */
    }

    if (simulation.has_witness()) {
        if (! om.quiet())
            f_out
                << outPrefix;
        f_out
            << "Registered witness `"
            << simulation.witness().id()
            << "`"
            << std::endl;
    }
    else {
        if (! om.quiet())
            f_out
                << wrnPrefix;
        f_out
            << "(no witness available)"
            << std::endl;
    }

    return Variant(res ? okMessage : errMessage);
}

SimulateTopic::SimulateTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

SimulateTopic::~SimulateTopic()
{
    TRACE
        << "Destroyed simulate topic"
        << std::endl;
}

void SimulateTopic::usage()
{ display_manpage("simulate"); }


// void SimulateTopic::usage()
// {
//     std::cout
//         << "simulate [ -c <expr> ] [ -u <expr> | -k <#steps> ] - Performs BMC simulation.\n"
//         << "[ Requires model ]\n\n"
//         << "options:\n"
//         << "  -c <expr>, specifies an additional state constraint.\n"
//         << "  -u <expr>, specifies an until condition.\n"
//         << "  -k <steps>, the number of steps to simulate.\n"
//         << "  -t <trace-uid>, the simulation trace UID.\n\n"
//         << "Extends an existing trace with simulated steps. The simulation will follow\n"
//         << "any additional constraint and will terminate due to (a) having reached\n"
//         << "the until condition; or (b) having reached the specified number of steps.\n"
//         << "If neither -k nor -u is used, -k 1 is assumed.\n" ;
// }

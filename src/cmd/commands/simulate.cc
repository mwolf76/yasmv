/*
 * @file simulate.cc
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
#include <cstdlib>
#include <cstring>

#include <cmd/commands/simulate.hh>

Simulate::Simulate(Interpreter& owner)
    : Command(owner)
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
    Simulation sim
        (*this, ModelMgr::INSTANCE().model());

    sim.simulate(f_invar_condition,
                 f_until_condition,
                 f_k, f_trace_uid);

    std::ostringstream tmp;
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

void Simulate::usage()
{
    std::cout
        << "simulate [ -c <expr> ] [ -u <expr> | -k <#steps> ] - Performs BMC simulation."
        << std::endl
        << std::endl
        << "options:"
        << std::endl
        << "  -c <expr>, specifies an additional state constraint."
        << std::endl
        << "  -u <expr>, specifies an until condition."
        << std::endl
        << "  -k <steps>, the number of steps to simulate."
        << std::endl
        << "  -t <trace-uid>, the simulation trace UID."
        << std::endl
        << std::endl
        << "Extends an existing trace with simulated steps. The simulation will follow"
        << std::endl
        << "any additional constraint and will terminate due to (a) having reached"
        << "the until condition; or (b) having reached the specified number of steps."
        << std::endl
        << "If neither -k nor -u is used, -k 1 is assumed." ;
}


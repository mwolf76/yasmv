/*
 * @file reach.cc
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

#include <cmd/commands/reach.hh>

Reach::Reach(Interpreter& owner)
    : Command(owner)
    , f_target(NULL)
{}

Reach::~Reach()
{}

void Reach::set_target(Expr_ptr target)
{
    f_target = target;
}

Variant Reach::operator()()
{
    if (! f_target)
        return Variant("No property given. Aborting...");

    BMC bmc
        (*this, ModelMgr::INSTANCE().model());

    bmc.process(f_target);

    std::ostringstream tmp;
    switch (bmc.status()) {
    case MC_FALSE:
        tmp << "Target is reachable";
        break;

    case MC_TRUE:
        tmp << "Target is unreachable";
        break;

    case MC_UNKNOWN:
        tmp << "Reachability could not be decided";
        break;
    case MC_ERROR:
        tmp << "Error";
        break;
    default: assert( false ); /* unreachable */
    } /* switch */

    if (bmc.has_witness()) {
        Witness& w
            (bmc.witness());

        tmp
            << ", registered CEX witness `"
            << w.id()
            << "`, "
            << w.size()
            << " steps.";
    }

    return Variant(tmp.str());
}

ReachTopic::ReachTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

ReachTopic::~ReachTopic()
{
    TRACE
        << "Destroyed check-target topic"
        << std::endl;
}

void ReachTopic::usage()
{
    std::cout
        << "check-target [ -D < id := value > ; ]* < expression > - Checks targetiant property on a given expression.\n\n"
        << "If the targetiant expression holds no trace is generated. Otherwise, a BMC counterexample\n"
        << "witness trace for the given property is generated. -D can be used multiple times to override \n"
        << "existing model defines with input values." ;
}

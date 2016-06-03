/*
 * @file check_invar.cc
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

#include <cmd/commands/check_invar.hh>

CheckInvar::CheckInvar(Interpreter& owner)
    : Command(owner)
    , f_invar(NULL)
{}

CheckInvar::~CheckInvar()
{}

void CheckInvar::set_invar(Expr_ptr invar)
{
    f_invar = invar;
}

Variant CheckInvar::operator()()
{
    if (! f_invar)
        return Variant("No property given. Aborting...");

    BMC bmc
        (*this, ModelMgr::INSTANCE().model());

    bmc.process(f_invar);

    std::ostringstream tmp;
    switch (bmc.status()) {
    case MC_FALSE:
        tmp << "Property is FALSE";
        break;
    case MC_TRUE:
        tmp << "Property is TRUE";
        break;
    case MC_UNKNOWN:
        tmp << "Property could not be decided";
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

CheckInvarTopic::CheckInvarTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

CheckInvarTopic::~CheckInvarTopic()
{
    TRACE
        << "Destroyed check-invar topic"
        << std::endl;
}

void CheckInvarTopic::usage()
{
    std::cout
        << "check-invar [ -D < id := value > ; ]* < expression > - Checks invariant property on a given expression.\n\n"
        << "If the invariant expression holds no trace is generated. Otherwise, a BMC counterexample\n"
        << "witness trace for the given property is generated. -D can be used multiple times to override \n"
        << "existing model defines with input values." ;
}

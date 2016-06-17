/*
 * @file check_init.cc
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

#include <cmd/commands/check_init.hh>

CheckInit::CheckInit(Interpreter& owner)
    : Command(owner)
    , f_init(NULL)
    , f_allsat(false)
{}

CheckInit::~CheckInit()
{
    free(f_init);
    f_init = NULL;
}

void CheckInit::set_init(Expr_ptr init)
{
    free(f_init);
    f_init = init;
}

void CheckInit::set_allsat(bool allsat)
{
    f_allsat = allsat;
}

Variant CheckInit::operator()()
{
    /* if no INIT formula is given, proceed with trivial truth */
    if (! f_init)
        f_init = ExprMgr::INSTANCE().make_true();

    BMC bmc
        (*this, ModelMgr::INSTANCE().model());

    bmc.process( f_init );

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

CheckInitTopic::CheckInitTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

CheckInitTopic::~CheckInitTopic()
{
    TRACE
        << "Destroyed check-init topic"
        << std::endl;
}

void CheckInitTopic::usage()
{
    std::cout
        << "check-init [ -a ] <expression> - Checks propositional satisfiability for given expression at initial time.\n\n"
        << "If no inconsistency is found one INIT state witness trace is generated.\n"
        << "If -a is specified all witness traces are generated (ALLSAT). Fails if no initial state exists.";
}

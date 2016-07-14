/*
 * @file add_invar.cc
 * @brief Command-interpreter subsystem related classes and definvarions.
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

#include <cmd/commands/add_invar.hh>

AddInvar::AddInvar(Interpreter& owner)
    : Command(owner)
    , f_invar(NULL)
    , f_allsat(false)
{}

AddInvar::~AddInvar()
{
    free(f_invar);
    f_invar = NULL;
}

void AddInvar::set_invar(Expr_ptr invar)
{
    free(f_invar);
    f_invar = invar;
}

void AddInvar::set_allsat(bool allsat)
{
    f_allsat = allsat;
}

Variant AddInvar::operator()()
{
    /* if no INVAR formula is given, proceed with trivial truth */
    if (! f_invar)
        f_invar = ExprMgr::INSTANCE().make_true();

    /* TODO: turn this into CONSISTENCY */
    BMC bmc
        (*this, ModelMgr::INSTANCE().model());

    bmc.process( f_invar );

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

AddInvarTopic::AddInvarTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

AddInvarTopic::~AddInvarTopic()
{
    TRACE
        << "Destroyed add-invar topic"
        << std::endl;
}

void AddInvarTopic::usage()
{
    std::cout
        << "add-invar [ -a ] <expression> - Adds propositional satisfiability for given expression at invarial time.\n\n"
        << "If no inconsistency is found one INVAR state witness trace is generated.\n"
        << "If -a is specified all witness traces are generated (ALLSAT). Fails if no invarial state exists.";
}

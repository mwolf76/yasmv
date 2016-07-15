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
#include <algorithms/fsm/fsm.hh>


CheckInit::CheckInit(Interpreter& owner)
    : Command(owner)
{}

CheckInit::~CheckInit()
{}

Variant CheckInit::operator()()
{
    CheckInitConsistency algorithm
        (*this, ModelMgr::INSTANCE().model());

    algorithm.process();

    std::ostringstream tmp;
    switch (algorithm.status()) {
    case FSM_CONSISTENCY_OK:
        tmp << "INIT is consistent";
        break;

    case FSM_CONSISTENCY_KO:
        tmp << "INIT is inconsistent";
        break;

    case FSM_CONSISTENCY_UNDECIDED:
        tmp << "Consistency could not be decided";
        break;

    default: assert( false ); /* unreachable */
    } /* switch */

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
        << "check-init [ -a ] <expression> - Checks propositional satisfiability for INIT formulas.\n\n";
}

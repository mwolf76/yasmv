/**
 * @file check_init.cc
 * @brief Command `check-init` class implementation.
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
#include <cmd/commands/check_init.hh>

#include <algorithms/fsm/fsm.hh>


CheckInit::CheckInit(Interpreter& owner)
    : Command(owner)
{}

CheckInit::~CheckInit()
{}

Variant CheckInit::operator()()
{
    Variant res = Variant(errMessage);

    /* FIXME: implement stream redirection for std{out,err} */
    std::ostream& out { std::cout };

    CheckInitConsistency algorithm { *this, ModelMgr::INSTANCE().model() };
    algorithm.process();

    switch (algorithm.status()) {
    case FSM_CONSISTENCY_OK:
        out
            << outPrefix
            << "Initial states consistency check ok."
            << std::endl;

        res = Variant(okMessage);
        break;

    case FSM_CONSISTENCY_KO:
        out
            << outPrefix
            << "Initial states consistency check failed."
            << std::endl;

    case FSM_CONSISTENCY_UNDECIDED:
        out
            << outPrefix
            << "Could not decide initial states consistency check."
            << std::endl;
        break;

    default: assert( false ); /* unreachable */
    } /* switch */

    return res;
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
        << "check-init - Checks propositional satisfiability for INIT formulas.\n\n"
        << "Initial states are checked for consistency. Returns `OK` if initial\n"
        << "states are consistent, `KO` if initial are found to be inconsistent.\n"
        << "If no decision could be made returns `??`."
        << std::endl;
}

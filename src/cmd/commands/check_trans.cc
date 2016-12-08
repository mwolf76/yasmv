/**
 * @file check_trans.cc
 * @brief Command `check-trans` class implementation.
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

#include <cmd/commands/check_trans.hh>
#include <algorithms/fsm/fsm.hh>


CheckTrans::CheckTrans(Interpreter& owner)
    : Command(owner)
{}

CheckTrans::~CheckTrans()
{}

Variant CheckTrans::operator()()
{
    CheckTransConsistency algorithm
        (*this, ModelMgr::INSTANCE().model());

    algorithm.process();

    std::ostringstream tmp;
    switch (algorithm.status()) {
    case FSM_CONSISTENCY_OK:
        tmp << "TRANS is consistent";
        break;

    case FSM_CONSISTENCY_KO:
        tmp << "TRANS is inconsistent";
        break;

    case FSM_CONSISTENCY_UNDECIDED:
        tmp << "Consistency could not be decided";
        break;

    default: assert( false ); /* unreachable */
    } /* switch */

    return Variant(tmp.str());
}

CheckTransTopic::CheckTransTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

CheckTransTopic::~CheckTransTopic()
{
    TRACE
        << "Destroyed check-trans topic"
        << std::endl;
}

void CheckTransTopic::usage()
{
    std::cout
        << "check-trans [ -a ] <expression> - Checks propositional satisfiability for TRANS formulas.\n\n";
}

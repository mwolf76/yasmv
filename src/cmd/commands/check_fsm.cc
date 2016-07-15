
/*
 * @file check_trans.cc
 * @brief Command-interpreter subsystem related classes and deffsmions.
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

#include <cmd/commands/check_trans.hh>

CheckFsm::CheckFsm(Interpreter& owner)
    : Command(owner)
{}

CheckFsm::~CheckFsm()
{}

Variant CheckFsm::operator()()
{
    assert(false); /* not yet implemented */
    return Variant("Not yet implemented");
}

CheckFsmTopic::CheckFsmTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

CheckFsmTopic::~CheckFsmTopic()
{
    TRACE
        << "Destroyed check-fsm topic"
        << std::endl;
}

void CheckFsmTopic::usage()
{
    std::cout
        << "check-fsm - Checks propositional satisfiability for initial states and transition relation.\n";
}

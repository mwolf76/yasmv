/**
 * @file last.cc
 * @brief Command `last` class implementation.
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

#include <cmd/interpreter.hh>

#include <cmd/commands/last.hh>
#include <cmd/commands/commands.hh>

#include <iomanip>

Last::Last(Interpreter& owner)
    : Command(owner)
    , f_message(NULL)
{}

Last::~Last()
{
}

Variant Last::operator()()
{
    return Interpreter::INSTANCE().last_result();
}

LastTopic::LastTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

LastTopic::~LastTopic()
{
    TRACE
        << "Destroyed last topic"
        << std::endl;
}

void LastTopic::usage()
{
    std::cout
        << "last - yields the result of last command." ;
}

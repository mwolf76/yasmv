/**
 * @file time.cc
 * @brief Command `time` class implementation.
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

#include <iomanip>

#include <utils/clock.hh>

#include <cmd/interpreter.hh>

#include <cmd/commands/commands.hh>
#include <cmd/commands/time.hh>

Time::Time(Interpreter& owner)
    : Command(owner)
{}

Time::~Time()
{}

Variant Time::operator()()
{
    std::ostream& out = std::cout;

    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);

    struct timespec epoch { Interpreter::INSTANCE().epoch() };
    out
        << "Session time: "
        << elapsed_repr(epoch, now)
        << "."
        << std::endl;

    return Variant(okMessage);
}

TimeTopic::TimeTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

TimeTopic::~TimeTopic()
{
    TRACE
        << "Destroyed time topic"
        << std::endl;
}

void TimeTopic::usage()
{
    std::cout
        << "time - retrieves current running time in seconds" ;
}

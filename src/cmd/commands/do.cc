/*
 * @file do.cc
 * @brief Command `do` class implementation.
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
#include <cmd/commands/do.hh>

#include <cmd/cmd.hh>

Do::Do(Interpreter& owner)
    : Command(owner)
    , f_commands()
{}

Do::~Do()
{
    f_commands.clear();
}

Variant Do::operator()()
{
    CommandMgr& cm { CommandMgr::INSTANCE() };

    Variant res;
    Commands::iterator i = f_commands.begin();
    while (i != f_commands.end()) {
        Command_ptr c { *i };
        assert(NULL != c);

        res = (*c)();
        if (cm.is_failure(res))
            break;

        ++ i;
    }

    return res;
}

void Do::add_command(Command_ptr c)
{
    f_commands.push_back(c);
}

DoTopic::DoTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

DoTopic::~DoTopic()
{
    TRACE
        << "Destroyed do topic"
        << std::endl;
}

void DoTopic::usage()
{
    std::cout
        << "do [ <command> ';' ... ] done - Builds a sequence of commands\n";
}

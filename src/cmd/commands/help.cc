/*
 * @file help.cc
 * @brief Command `help` class implementation.
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
#include <cmd/commands/help.hh>

Help::Help(Interpreter& owner)
    : Command(owner)
    , f_topic(NULL)
{}

Help::~Help()
{
    if (f_topic)
        delete f_topic;

    f_topic = NULL;
}

void Help::set_topic(CommandTopic_ptr topic)
{
    f_topic = topic;
}

/*
- add-init
- add-invar
- add-trans
- check-init
- check-trans
- clear
- dump-model
- dump-trace
- dup-trace
- get
- help
- list-traces
- pick-state
- quit
- reach
- read-model
- set
- simulate
- time
*/

Variant Help::operator()()
{
    if (f_topic)
        f_topic->usage();

    else
        std::cout
            << "Available topics: " << std::endl
            << "- add-init" << std::endl
            << "- add-invar" << std::endl
            << "- add-trans" << std::endl
            << "- check-init" << std::endl
            << "- check-trans" << std::endl
            << "- clear" << std::endl
            << "- dump-model" << std::endl
            << "- dump-trace" << std::endl
            << "- dup-trace" << std::endl
            << "- get" << std::endl
            << "- help" << std::endl
            << "- list-traces" << std::endl
            << "- pick-state" << std::endl
            << "- quit" << std::endl
            << "- reach" << std::endl
            << "- read-model" << std::endl
            << "- set" << std::endl
            << "- simulate" << std::endl
            << "- time" << std::endl
            << std::endl;

    return Variant(okMessage);
}

HelpTopic::HelpTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

HelpTopic::~HelpTopic()
{
    TRACE
        << "Destroyed help topic"
        << std::endl;
}

void HelpTopic::usage()
{
    std::cout
        << "help <command> - shows a topic from the internal help system\n";
}

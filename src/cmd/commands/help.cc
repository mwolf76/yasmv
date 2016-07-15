/*
 * @file help.cc
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

Variant Help::operator()()
{
    if (f_topic)
        f_topic->usage();

    else
        std::cout << "Available topics: " << std::endl
                  << "- help" << std::endl
                  << "- time" << std::endl
                  << "- get" << std::endl
                  << "- set" << std::endl
                  << "- clear" << std::endl
                  << "- read-model" << std::endl
                  << "- write-model" << std::endl
                  << "- add-init" << std::endl
                  << "- add-invar" << std::endl
                  << "- add-trans" << std::endl
                  << "- pick-state" << std::endl
                  << "- simulate" << std::endl
                  << "- check-fsm" << std::endl
                  << "- check-init" << std::endl
                  << "- check-invar" << std::endl
                  << "- list-traces" << std::endl
                  << "- dump-trace" << std::endl
                  << "- dup-trace" << std::endl
                  << "- quit" << std::endl
                  << std::endl;

    return Variant("Ok");
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

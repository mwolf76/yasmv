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

void Help::set_topic(Command_ptr topic)
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
                  << "- read_model" << std::endl
                  << "- write_model" << std::endl
                  << "- pick_state" << std::endl
                  << "- simulate" << std::endl
                  << "- check_init" << std::endl
                  << "- check_invar" << std::endl
                  << "- list_traces" << std::endl
                  << "- dump_trace" << std::endl
                  << "- dup_trace" << std::endl
                  << "- quit" << std::endl
                  << std::endl;

    return Variant("Ok");
}

void Help::usage()
{
    std::cout
        << "help <command> - shows a topic from the internal help system"
        << std::endl;
}


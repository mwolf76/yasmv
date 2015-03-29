/*
 * @file quit.cc
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
#include <cmd/commands/quit.hh>
#include <cmd/interpreter.hh>

Quit::Quit(Interpreter& owner)
    : Command(owner)
    , f_retcode(0)
{}

Quit::~Quit()
{}

void Quit::set_retcode(int retcode)
{
    f_retcode = retcode;
}

// sends a signal to the owner
Variant Quit::operator()()
{
    f_owner.quit(f_retcode);
    return Variant("BYE");
}

void Quit::usage()
{
    std::cout
        << "quit - Leave interactive shell"
        << std::endl;
}


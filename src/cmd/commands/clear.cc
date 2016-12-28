/**
 * @file clear.cc
 * @brief Command `clear` class implementation.
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
#include <cmd/commands/clear.hh>

#include <expr/expr.hh>
#include <expr/expr_mgr.hh>

#include <witness/witness.hh>
#include <witness/witness_mgr.hh>

Clear::Clear(Interpreter& owner)
    : Command(owner)
    , f_identifier(NULL)
{}

Clear::~Clear()
{}

void Clear::set_identifier(Expr_ptr id)
{
    f_identifier = id;
}

Variant Clear::operator()()
{
    return Variant(okMessage);
}

ClearTopic::ClearTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

ClearTopic::~ClearTopic()
{
    TRACE
        << "Destroyed clear topic"
        << std::endl;
}

void ClearTopic::usage()
{
    std::cout <<
        "clear [ <identifier> ] - Clears current value of <identifier>.\n\n"
        "All assignments in the current environment are cleared if no argument is given." ;
}

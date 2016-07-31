/**
 * @file while.cc
 * @brief Command `while` class implementation.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modwhiley it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; while not, write to the Free
 * Software Foundation, Inc., 51 Franklin Street, Fwhileth Floor,
 * Boston, MA 02110-1301 USA
 *
 **/

#include <cstdlib>
#include <cstring>

#include <cmd/commands/while.hh>

While::While(Interpreter& owner)
    : Command(owner)
    , f_condition(NULL)
    , f_inner_block(NULL)
{}

While::~While()
{}

void While::set_condition(Expr_ptr condition)
{
    f_condition = condition;
}

void While::set_inner(Expr_ptr inner_block)
{
    f_inner_block = inner_block;
}

Variant While::operator()()
{
    assert(false); /* not yet implemented */
}

WhileTopic::WhileTopic(Interpreter& owner)
    : Command(owner)
{}

WhileTopic::~WhileTopic()
{
    TRACE
        << "Destroyed while topic"
        << std::endl;
}

void WhileTopic::usage()
{
    std::cout
        << "while <condition> BLOCK - WHILE conditional loop execution."
}

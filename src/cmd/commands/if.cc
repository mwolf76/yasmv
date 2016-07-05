/*
 * @file if.cc
 * @brief Command-interpreter subsystem related classes and then_blocks.
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

#include <cmd/commands/if.hh>

If::If(Interpreter& owner)
    : Command(owner)
    , f_condition(NULL)
    , f_then_block(NULL)
{}

If::~If()
{}

void If::set_condition(Expr_ptr condition)
{
    f_condition = condition;
}

void If::set_then(Expr_ptr then_block)
{
    f_then_block = then_block;
}

void If::set_else(Expr_ptr else_block)
{
    f_else_block = else_block;
}

Variant If::operator()()
{
    assert(false); /* not yet implemented */
}

IfTopic::IfTopic(Interpreter& owner)
    : Command(owner)
{}

IfTopic::~IfTopic()
{
    TRACE
        << "Destroyed if topic"
        << std::endl;
}

void IfTopic::usage()
{
    std::cout
        << "if <condition> then <then-block> [ else <else-block> - ITE conditional execution."
}

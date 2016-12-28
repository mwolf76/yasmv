/**
 * @file add_init.cc
 * @brief Command `add-init` class implementation.
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
#include <cmd/commands/add_init.hh>

#include <env/environment.hh>

AddInit::AddInit(Interpreter& owner)
    : Command(owner)
    , f_constraint(NULL)
{}

AddInit::~AddInit()
{
    free(f_constraint);
    f_constraint = NULL;
}

void AddInit::set_constraint(Expr_ptr constraint)
{
    f_constraint = constraint;
}

Variant AddInit::operator()()
{
    Environment& env
        (Environment::INSTANCE());

    assert(f_constraint);
    env.add_extra_init(f_constraint);

    return Variant(okMessage);
}

AddInitTopic::AddInitTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

AddInitTopic::~AddInitTopic()
{
    TRACE
        << "Destroyed add-init topic"
        << std::endl;
}

void AddInitTopic::usage()
{
    std::cout
        << "add-init [ -a ] <expression> - Adds propositional satisfiability for given expression at initial time.\n\n"
        << "If no inconsistency is found one INIT state witness trace is generated.\n"
        << "If -a is specified all witness traces are generated (ALLSAT). Fails if no initial state exists.";
}

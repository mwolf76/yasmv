/*
 * @file set.cc
 * @brief Command `set` class implementation.
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
#include <cmd/commands/set.hh>

#include <expr/expr.hh>
#include <expr/expr_mgr.hh>

#include <witness/witness.hh>
#include <witness/witness_mgr.hh>

Set::Set(Interpreter& owner)
    : Command(owner)
    , f_identifier(NULL)
    , f_value(NULL)
{}

Set::~Set()
{}

void Set::set_identifier(expr::Expr_ptr id)
{
    DEBUG
        << "Id"
        << std::endl;

    f_identifier = id;
}

void Set::set_value(expr::Expr_ptr value)
{
    DEBUG
        << "Val"
        << std::endl;

    f_value = value;
}

utils::Variant Set::operator()()
{
    env::Environment& env
        (env::Environment::INSTANCE());

    if (NULL == f_identifier || NULL == f_value) {
        SetTopic(f_owner)
            .usage();
    }
    else
        env.set(f_identifier, f_value);

    return utils::Variant(okMessage);
}

SetTopic::SetTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

SetTopic::~SetTopic()
{
    TRACE
        << "Destroyed set topic"
        << std::endl;
}

void SetTopic::usage()
{ display_manpage("set"); }

/*
 * @file get.cc
 * @brief Command `get` class implementation.
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
#include <cmd/commands/get.hh>

#include <expr/expr.hh>
#include <expr/expr_mgr.hh>

#include <witness/witness.hh>
#include <witness/witness_mgr.hh>

Get::Get(Interpreter& owner)
    : Command(owner)
    , f_identifier(NULL)
{}

Get::~Get()
{}

void Get::set_identifier(Expr_ptr id)
{
    f_identifier = id;
}

Variant Get::operator()()
{
    Environment& env
        (Environment::INSTANCE());

    if (NULL == f_identifier) {
        const ExprSet& identifiers
            (env.identifiers());

        for (ExprSet::const_iterator i = identifiers.begin();
             i != identifiers.end(); ++ i) {

            Expr_ptr id
                (*i);

            Expr_ptr value
                (env.get(id));

            std::cout
                << "-- "
                << id
                << " := "
                << value
                << std::endl;
        }

        return Variant(okMessage);
    }
    else {
        try {
            Expr_ptr value
                (env.get(f_identifier));

            std::cout
                << "-- "
                << f_identifier
                << " := "
                << value
                << std::endl;

            return Variant(okMessage);
        }
        catch (NoSuchIdentifier nsi) {
            const char *tmp
                (nsi.what());

            std::cerr
                << tmp
                << std::endl;
        }
    }

    return Variant("ERR");
}

GetTopic::GetTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

GetTopic::~GetTopic()
{
    TRACE
        << "Destroyed get topic"
        << std::endl;
}

void GetTopic::usage()
{
    std::cout <<
        "get [ <identifier> ] - Dumps current value of <identifier>.\n\n"
        "All assignments in the current environment are dumped if no argument is given." ;
}

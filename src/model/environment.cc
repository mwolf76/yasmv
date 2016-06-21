/**
 *  @file environment.cc
 *
 *  Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU Lesser General Public
 *  License as published by the Free Software Foundation; either
 *  version 2.1 of the License, or (at your option) any later version.
 *
 *  This library is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public
 *  License along with this library; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/
#include <algorithm>
#include <utility>
#include <model.hh>

std::ostream& operator<<(std::ostream& os, Environment& environment)
{ return os << environment.name(); }

Environment::Environment(const Expr_ptr name)
{}

Environment::~Environment()
{}

void Environment::add_value(Expr_ptr symbol, Expr_ptr value)
{
  f_localValues.insert(std::make_pair<Expr_ptr, Expr_ptr>
                       (symbol, value))
}

Expr_ptr& Model::value(Expr_ptr key)
{
    Values::const_iterator i
      (f_localValues.find());

    if (i == f_localValues.end())
        throw UndefinedIdentifier(key);

    return *(i -> second);
}

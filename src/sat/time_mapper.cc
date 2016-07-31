/**
 * @file time_mapper.cc
 * @brief SAT interface implementation, Time Mapper subsystem implementation.
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
#include <utility>
#include <sat.hh>

/**
 * This module defines the services that implement the Time
 * Mapper. This service is used to keep a bidirectional mapping
 * between Timed Canonical Bit Identifiers (or TCBIs) and actual
 * Minisat Variables.
 */

TimeMapper::TimeMapper(Engine& owner)
    : f_owner(owner)
{}

TimeMapper::~TimeMapper()
{}

Var TimeMapper::var(const TCBI& tcbi)
{
    Var var;
    const TCBI2VarMap::iterator eye = f_tcbi2var_map.find(tcbi);

    if (f_tcbi2var_map.end() != eye) {
        var = eye->second;
    }
    else {
        /* generate a new var and book it. Newly created var is not eliminable. */
        var = f_owner.new_sat_var(true);

        DRIVEL
            << "Adding VAR " << var
            << " for " << tcbi
            << std::endl;

        f_tcbi2var_map.insert( std::make_pair<TCBI, Var>(tcbi, var));
        f_var2tcbi_map.insert( std::make_pair<Var, TCBI>(var, tcbi));
    }

    return var;
}

const TCBI& TimeMapper::tcbi(Var var)
{
    const Var2TCBIMap::iterator eye = f_var2tcbi_map.find(var);

    /* TCBI *has* to be there already. */
    if (f_var2tcbi_map.end() == eye) {
        assert (false); /* unexpected */
    }

    return eye->second;
}


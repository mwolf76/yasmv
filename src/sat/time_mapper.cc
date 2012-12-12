/**
 *  @file time_mapper.cc
 *  @brief SAT interface implementation (Time Mapper sub-component)
 *
 *  This module contains the interface for services that implement a
 *  bidirectional mapping between TCBI (Timed Canonical Bit
 *  Identifiers) and proper Minisat Vars.
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
#include <sat.hh>

namespace Minisat {

    TimeMapper::TimeMapper(SAT& owner)
        : f_owner(owner)
    {}

    TimeMapper::~TimeMapper()
    {}

    Var TimeMapper::var( TCBI& tcbi )
    {
        Var res;
        const TCBI2VarMap::iterator eye = f_tcbi2var_map.find(tcbi);

        if (eye != f_tcbi2var_map.end()) {
            res = eye->second;
        }
        else {
            /* generate a new var and book it. */
            res = f_owner.new_sat_var();
            DRIVEL << "Adding VAR " << res
                   << " for " << tcbi
                   << endl;

            f_tcbi2var_map.insert( make_pair<TCBI, Var>(tcbi, res));
        }

        return res;
    }


    TCBI& TimeMapper::tcbi( Var var )
    {
    }
};

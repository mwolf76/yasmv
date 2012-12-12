/**
 *  @file sat.cc
 *  @brief SAT interface implementation
 *
 *  This module contains the interface for services that implement an
 *  CNF clauses generation in a form that is suitable for direct
 *  injection into the SAT solver.
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
#include <dd_walker.hh>

namespace Minisat {

    Lit SAT::cnf_find_group_lit(group_t group)
    {
        Var v;
        const Group2VarMap::iterator eye = f_groups_map.find(group);

        if (eye != f_groups_map.end()) {
            v = eye->second;
        }
        else {
            v = f_solver.newVar();
            // DRIVEL << "Adding VAR " << v
            //        << " for group " << group << endl;

            f_groups_map.insert( make_pair<group_t, Var>(group, v));
        }

        return mkLit(v, true); // g -> ...
    }

    // memoize only positive terms

    // Var SAT::cnf_find_index_var(int index)
    // {
    //     Var res;
    //     const Index2VarMap::iterator eye = f_index2var_map.find(index);

    //     if (eye != f_index2var_map.end()) {
    //         res = eye->second;
    //     }
    //     else {
    //         /* generate new var and book it. */
    //         res = f_solver.newVar();
    //         // DRIVEL << "Adding VAR " << res
    //         //        << " for DD (index = " << index << ") " << endl;

    //         f_index2var_map.insert( make_pair<int, Var>(index, res));
    //     }

    //     return res;
    // }

    /* TODO: inline */
    void SAT::push(Term term, step_t time, group_t group, color_t color)
    { cnf_push_single_cut(term, time, group, color); }
};

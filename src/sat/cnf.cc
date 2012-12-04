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
            DRIVEL << "Adding VAR " << v
                   << " for group " << group << endl;

            f_groups_map.insert( make_pair<group_t, Var>(group, v));
        }

        return mkLit(v, true); // g -> ...
    }

    Var SAT::cnf_new_cnf_var()
    {
        Var v = f_solver.newVar();
        DRIVEL << "Adding VAR " << v << " for CNF" << endl;

        return v;
    }

    // memoize only positive terms

    Lit SAT::cnf_find_index_lit(int index, bool is_cmpl)
    {
        Var v;
        const Index2VarMap::iterator eye = f_index2var_map.find(index);

        if (eye != f_index2var_map.end()) {
            v = eye->second;
        }
        else {
            // generate new var and book it
            v = f_solver.newVar();
            DRIVEL << "Adding VAR " << v
                   << " for Term (index = " << index << ") " << endl;

            f_index2var_map.insert( make_pair<int, Var>(index, v));
            // f_var2index_map.insert( make_pair<Var, int>(v, index));
        }

        return mkLit(v, is_cmpl);
    }

    void SAT::push(Term term, group_t group, color_t color)
    {
#if 0
        cnf_push_single_cut(term, group, color);
#else
        cnf_push_no_cut(term, group, color);
#endif
    }
};

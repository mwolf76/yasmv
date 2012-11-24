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

    class CNFBuilder : public DDWalker {
    public:
        CNFBuilder(CuddMgr& mgr, SAT& sat)
            : DDWalker(mgr)
            , f_sat(sat)
        {}

        ~CNFBuilder()
        {}

        bool condition(const DdNode *node)
        {
            DdNode *N = Cudd_Regular(node);
            assert( cuddIsConstant(N) );

            /* take into account arithmetical zeroes */
            if (node == f_owner.dd().getManager()->zero) {
                return true;
            }

            return false;
        }

        virtual void action(value_t value)
        {
            // FIXME...
            group_t group = MAINGROUP;
            color_t color = BACKGROUND;

            vec<Lit> ps; ps.push(f_sat.cnf_find_group_lit(group));

            unsigned i, size = f_owner.dd().getManager()->size;
            int v;
            for (i = 0; i < size; ++ i) {
                v = f_data[i];

                if (v == 0) {
                    ps.push(f_sat.cnf_find_index_lit(i, false));
                }
                else if (v == 1) {
                    ps.push(f_sat.cnf_find_index_lit(i, true));
                }
                else {
                    // it's a don't care, but we need the variable for
                    // mapback REVIEW: it could be an interesting tweak to
                    // do with options, to allow the user to prevent don't
                    // care vars to make their way to minisat.
                    f_sat.cnf_find_index_lit(i, false);
                }
            }

            DRIVEL << ps << endl;
            f_sat.f_solver.addClause_(ps, color);
        }

    private:
        SAT& f_sat;
    };

    void SAT::cnf_push_no_cut(Term phi, const group_t group, const color_t color)
    { CNFBuilder builder(CuddMgr::INSTANCE(), *this); builder(phi); }

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

    Lit SAT::cnf_new_solver_lit(bool inv)
    {
        Var v = f_solver.newVar();
        DRIVEL << "Adding VAR " << v << " for CNF" << endl;

        return mkLit(v, inv);
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
            f_var2index_map.insert( make_pair<Var, int>(v, index));
        }

        return mkLit(v, is_cmpl);
    }
};

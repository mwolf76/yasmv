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

    class CNFBuilderNoCut : public DDLeafWalker {
    public:
        CNFBuilderNoCut(CuddMgr& mgr, SAT& sat)
            : DDLeafWalker(mgr)
            , f_sat(sat)
        {}

        ~CNFBuilderNoCut()
        {}

        bool condition(const DdNode *node)
        {
            /* if it's a zero leaf */
            return (node == f_owner.dd().getManager()->zero);
        }

        void action(const DdNode *node)
        {
            value_t value = Cudd_V(node);

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

                    // REVIEW
                    // f_sat.cnf_find_index_lit(i, false);
                }
            }
#if 0
            DRIVEL << ps << endl;
#endif
            f_sat.f_solver.addClause_(ps, color);
        }

    private:
        SAT& f_sat;
    };

    void SAT::cnf_push_no_cut(Term phi, const group_t group, const color_t color)
    { CNFBuilderNoCut builder(CuddMgr::INSTANCE(), *this); builder(phi); }

};

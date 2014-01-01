/**
 *  @file sat.cc
 *  @brief SAT interface implementation
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
#if 0

    class CNFBuilderNoCut : public ADDWalker {
    public:
        CNFBuilderNoCut(SAT& sat, step_t time, group_t group, color_t color)
            : f_sat(sat)
            // , f_time(time),
            // , f_group(group)
            // , f_color(color)
            , f_owner(CuddMgr::INSTANCE())
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

            vec<Lit> ps; ps.push( f_sat.cnf_find_group_lit( group));
            unsigned i, size = f_owner.dd().getManager()->size;
            for (i = 0; i < size; ++ i) {

                if (value == 0) {
                    ps.push( mkLit( f_sat.cnf_find_index_var(i), false));
                }
                else if (value == 1) {
                    ps.push( mkLit( f_sat.cnf_find_index_var(i), true));
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
            f_sat.f_solver.addClause_(ps, color);
        }

    private:
        SAT& f_sat;
        CuddMgr& f_owner;
    };

    void SAT::cnf_push_no_cut(Term phi, step_t time, const group_t group, const color_t color)
    {
        CNFBuilderNoCut builder(*this, time, group, color);
        builder(phi);
    }
#endif
};


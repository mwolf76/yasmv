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

    class CNFBuilderSingleCut : public DDNodeWalker {
    public:
        CNFBuilderSingleCut(CuddMgr& mgr, SAT& sat)
            : DDNodeWalker(mgr)
            , f_sat(sat)
            , f_topset(false)
        {}

        ~CNFBuilderSingleCut()
        {}


        bool condition(const DdNode *node)
        {
            /* not visited */
            return (f_seen.find(node) == f_seen.end());
        }

        void post_hook()
        {
            // FIXME...
            group_t group = MAINGROUP;
            color_t color = BACKGROUND;

            Lit gl = f_sat.cnf_find_group_lit(group);

            /* build and push clause toplevel */
            vec<Lit> ps;

            ps.push(gl);

            assert ( f_topset );
            ps.push( f_toplevel );

            DRIVEL << ps << endl;
            f_sat.f_solver.addClause_(ps, color);
        }

        /* internal service for action */
        void push_clause(color_t color, Lit vl,
                         const DdNode* F, bool fpol,
                         const DdNode* K, bool kpol)
        {
            assert(! Cudd_IsConstant(Cudd_Regular(F)));
            bool false_konst = false; /* include k in the clause? */

            if (Cudd_IsConstant(Cudd_Regular(K))) {
                value_t value = Cudd_V(K);
                assert(0 == value || 1 == value);

                /* True const? clause is trivially satisfied, skip it. */
                if ((0 == value) && kpol ||
                    (0 != value) && (! kpol))
                    return;

                false_konst = true;
            }

            /* build and push clause */
            vec<Lit> ps;
            ps.push(vl);

            // memoize toplevel literal
            if (! f_topset) {
                f_topset = true;
                f_toplevel = f_sat.cnf_find_index_lit(Cudd_NodeReadIndex(const_cast <DdNode*>(F)),
                                                      false);
            }

            ps.push(f_sat.cnf_find_index_lit(Cudd_NodeReadIndex(const_cast <DdNode*>(F)),
                                             fpol));
            if (! false_konst) {
                ps.push(f_sat.cnf_find_index_lit(Cudd_NodeReadIndex(const_cast <DdNode*>(K)), kpol));
            }

            DRIVEL << ps << endl;
            f_sat.f_solver.addClause_(ps, color);
        }

        void action(const DdNode *node)
        {
            /* mark as visited */
            f_seen.insert(node);

            // FIXME...
            group_t group = MAINGROUP;
            color_t color = BACKGROUND;

            Lit gl = f_sat.cnf_find_group_lit(group);

            DdNode *N, *Nv, *Nnv;
            N = Cudd_Regular(node);

            if (Cudd_IsComplement(node)) {
                Nv  = Cudd_Not(cuddT(N));
                Nnv = Cudd_Not(cuddE(N));
            }
            else {
                Nv  = cuddT(N);
                Nnv = cuddE(N);
            }

            // if (! Cudd_IsConstant(Cudd_Regular(Nv)) ||
            //     ! Cudd_IsConstant(Cudd_Regular(Nnv))) {
            {
                Var v = f_sat.cnf_new_cnf_var();

                // group -> v, !f, e
                push_clause(color, mkLit( v, false), node, true, Nnv, false);

                // group -> v, f, !e
                push_clause(color, mkLit( v, false), node, false, Nnv, true);

                // group -> !v, !f, t
                push_clause(color, mkLit( v, true), node, true, Nv, false);

                // group -> !v, f, !t
                push_clause(color, mkLit( v, true), node, false, Nv, true);
            }
        }

    private:
        SAT& f_sat;
        unordered_set<const DdNode *> f_seen;

        bool f_topset;
        Lit f_toplevel;
    };

    void SAT::cnf_push_single_cut(Term phi, const group_t group, const color_t color)
    { CNFBuilderSingleCut builder(CuddMgr::INSTANCE(), *this); builder(phi); }

};

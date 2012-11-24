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
        {}

        ~CNFBuilderSingleCut()
        {}

        bool condition(const DdNode *node)
        {
            /* not visited */
            return (f_seen.find(node) == f_seen.end());
        }

        void action(const DdNode *node)
        {
            /* mark as visited */
            f_seen.insert(node);

            // FIXME...
            group_t group = MAINGROUP;
            color_t color = BACKGROUND;

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

            Var v = f_sat.cnf_new_cnf_var();
            int f = node->index;
            int t = Nv->index;
            int e = Nnv->index;

            { // group -> !f, v, e
                vec<Lit> ps;

                ps.push(f_sat.cnf_find_group_lit(group));
                ps.push(f_sat.cnf_find_index_lit(f, true));
                ps.push(mkLit(v, false));
                ps.push(f_sat.cnf_find_index_lit(e, false));

                DRIVEL << ps << endl;
                f_sat.f_solver.addClause_(ps, color);
             }

            { // group -> f, v, !e
                vec<Lit> ps;

                ps.push(f_sat.cnf_find_group_lit(group));
                ps.push(f_sat.cnf_find_index_lit(f, false));
                ps.push(mkLit(v, false));
                ps.push(f_sat.cnf_find_index_lit(e, true));

                DRIVEL << ps << endl;
                f_sat.f_solver.addClause_(ps, color);
            }

            { // group -> !f, !v, t
                vec<Lit> ps;

                ps.push(f_sat.cnf_find_group_lit(group));
                ps.push(f_sat.cnf_find_index_lit(f, true));
                ps.push(mkLit(v, true));
                ps.push(f_sat.cnf_find_index_lit(t, false));

                DRIVEL << ps << endl;
                f_sat.f_solver.addClause_(ps, color);
            }

            { // group -> f, !v, !t
                vec<Lit> ps;

                ps.push(f_sat.cnf_find_group_lit(group));
                ps.push(f_sat.cnf_find_index_lit(f, false));
                ps.push(mkLit(v, true));
                ps.push(f_sat.cnf_find_index_lit(t, true));

                DRIVEL << ps << endl;
                f_sat.f_solver.addClause_(ps, color);
            }
        }

    private:
        SAT& f_sat;
        unordered_set<const DdNode *> f_seen;
    };

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

            DRIVEL << ps << endl;
            f_sat.f_solver.addClause_(ps, color);
        }

    private:
        SAT& f_sat;
    };

    void SAT::cnf_push_single_cut(Term phi, const group_t group, const color_t color)
    { CNFBuilderSingleCut builder(CuddMgr::INSTANCE(), *this); builder(phi); }

    void SAT::cnf_push_no_cut(Term phi, const group_t group, const color_t color)
    { CNFBuilderNoCut builder(CuddMgr::INSTANCE(), *this); builder(phi); }

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
};

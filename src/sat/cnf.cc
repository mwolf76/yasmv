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

namespace Minisat {
    void bdd_0minterm_bridge(void *obj, int *list, int size)
    {
        assert(obj);
        SAT* inst = reinterpret_cast<SAT *>(obj); // the SAT instance
        inst->cnf_push_no_cut_callback(list, size);
    }

    void SAT::cnf_push_no_cut(Term phi, const group_t group, const color_t color)
    { f_factory.walk_zeroes(phi, this, bdd_0minterm_bridge); }

    void SAT::cnf_push_no_cut_callback(int *list, int size)
    {
        // FIXME...
        group_t group = MAINGROUP;
        color_t color = BACKGROUND;
        int i, v;
        vec<Lit> ps; ps.push(cnf_find_group_lit(group));

        for (i = 0; i < size; i++) {
            v = list[i];

            if (v == 0) {
                ps.push(cnf_find_term_lit(i, false));
            }
            else if (v == 1) {
                ps.push(cnf_find_term_lit(i, true));
            }
            else {
                // it's a don't care, but we need the variable for
                // mapback REVIEW: it could be an interesting tweak to
                // do with options, to allow the user to prevent don't
                // care vars to make their way to minisat.
                cnf_find_term_lit(i, false);
            }
        }

        DEBUG << ps << endl;
        f_solver.addClause_(ps, color);
    }

    // FIXME: recursive implementation, very inefficient
    // void SAT::cnf_push_single_node_cut(Term phi, const group_t group, const color_t color)
    // {
    //     Lit g = cnf_find_group_lit(group);
    //     Lit a = cnf_push_single_node_cut_aux(phi, group, color);

    //     { // activating clause: g -> f
    //         vec<Lit> ps;
    //         ps.push(g); ps.push(a);
    //         TRACE << ps << endl;
    //         f_solver.addClause_(ps, color);
    //     }
    // }

    // Lit SAT::cnf_push_single_node_cut_aux(Term phi, const group_t group, const color_t color)
    // {
    //     // if constant or already seen, return
    //     if (f_factory.is_false(phi)) {
    //         return mkLit(0, true); // false
    //     }

    //     if (f_factory.is_true(phi)) {
    //         return mkLit(0, false); // true
    //     }

    //     Term2VarMap::iterator eye = f_term2var_map.find(phi);
    //     if (eye != f_term2var_map.end()) {
    //         Var v = eye->second;
    //         return mkLit(v, Cudd_IsComplement(phi.getNode()));
    //     }

    //     cnf_push_single_node_cut_aux(f_factory.make_then(phi), group, color);
    //     cnf_push_single_node_cut_aux(f_factory.make_else(phi), group, color);

    //     return cnf_write(phi, group, color);
    // }

    Lit SAT::cnf_find_group_lit(group_t group)
    {
        Var v;
        const Group2VarMap::iterator eye = f_groups_map.find(group);

        if (eye != f_groups_map.end()) {
            v = eye->second;
        }
        else {
            v = f_solver.newVar();
            DEBUG << "Adding VAR " << v << " for group " << group << endl;
            f_groups_map.insert( make_pair<group_t, Var>(group, v));
        }

        return mkLit(v, true); // g -> ...
    }

    Lit SAT::cnf_new_solver_lit(bool inv)
    {
        Var v = f_solver.newVar();
        DEBUG << "Adding VAR " << v << " for CNF" << endl;
        return mkLit(v, inv);
    }

    // memoize only positive terms
    Lit SAT::cnf_find_term_lit(int index, bool is_cmpl)
    {
        Var v;
        const Term2VarMap::iterator eye = f_term2var_map.find(index);

        if (eye != f_term2var_map.end()) {
            v = eye->second;
        }
        else {
            // generate new var and book it
            v = f_solver.newVar();
            DEBUG << "Adding VAR " << v << " for Term (index = " << index << ") " << endl;

            f_term2var_map.insert( make_pair<int, Var>(index, v));
            f_var2term_map.insert( make_pair<Var, int>(v, index));
            // f_terms.push_back(phi);
        }

        return mkLit(v, is_cmpl);
    }

    // Lit SAT::cnf_write(Term phi, const group_t group, const color_t color)
    // {
    //     /* Minisat lits */
    //     Lit g, f, v, t, e;

    //     // CNF var
    //     g = cnf_find_group_lit(group);
    //     f = cnf_new_solver_lit(Cudd_IsComplement(phi.getNode()));

    //     // node variable, Then/Else branches vars
    //     v = cnf_find_term_lit(phi); // this will be a new one by construction
    //     t = cnf_find_term_lit(f_factory.make_then(phi));
    //     e = cnf_find_term_lit(f_factory.make_else(phi));

    //     { // group -> !f, v, e
    //         vec<Lit> ps;
    //         ps.push(g);
    //         ps.push(~ f);
    //         ps.push(  v);
    //         ps.push(  e);
    //         TRACE << ps << endl;
    //         f_solver.addClause_(ps, color);
    //     }

    //     { // group -> f, v, !e
    //         vec<Lit> ps;
    //         ps.push(g);
    //         ps.push(  f);
    //         ps.push(  v);
    //         ps.push(~ e);
    //         TRACE << ps << endl;
    //         f_solver.addClause_(ps, color);
    //     }

    //     { // group -> !f, !v, t
    //         vec<Lit> ps;
    //         ps.push(g);
    //         ps.push(~ f);
    //         ps.push(~ v);
    //         ps.push(  t);
    //         TRACE << ps << endl;
    //         f_solver.addClause_(ps, color);
    //     }

    //     { // group -> f, !v, !t
    //         vec<Lit> ps;
    //         ps.push(g);
    //         ps.push(  f);
    //         ps.push(~ v);
    //         ps.push(~ t);
    //         TRACE << ps << endl;
    //         f_solver.addClause_(ps, color);
    //     }

    //     return f;
    // } // write_cnf()

};

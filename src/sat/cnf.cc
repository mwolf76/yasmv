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

    // FIXME: recursive implementation, very inefficient
    void SAT::cnf_push_single_node_cut(Term phi, const group_t group, const color_t color)
    {
        // if constant or already seen, return
        if (f_factory.is_false(phi) ||
            f_factory.is_true(phi) ||
            f_term2var_map.find(phi) != f_term2var_map.end()) return;

        cnf_push_single_node_cut(f_factory.make_then(phi), group, color);
        cnf_push_single_node_cut(f_factory.make_else(phi), group, color);

        cnf_write(phi, group, color);
    }

    Var SAT::cnf_find_group_var(group_t group)
    {
        const Group2VarMap::iterator eye = f_groups_map.find(group);
        if (eye != f_groups_map.end()) {
            return (*eye).second;
        }

        Var res = f_solver.newVar();
        DEBUG << "Adding VAR " << res << " for group " << group << endl;
        f_groups_map.insert( make_pair<group_t, Var>(group, res));

        return res;
    }

    Var SAT::cnf_new_solver_var()
    {
        Var res = f_solver.newVar();
        DEBUG << "Adding VAR " << res << " for CNF" << endl;
        return res;
    }

    Var SAT::cnf_find_term_var(Term phi)
    {
        const Term2VarMap::iterator eye = f_term2var_map.find(phi);
        if (eye != f_term2var_map.end()) {
            return (*eye).second;
        }

        // generate new var and book it
        Var res = f_solver.newVar();
        DEBUG << "Adding VAR " << res << " for Term " << phi << endl;
        f_term2var_map.insert( make_pair<ADD, Var>(phi, res));
        f_var2term_map.insert( make_pair<Var, ADD>(res, phi));
        return res;
    }

    void SAT::cnf_write(Term phi, const group_t group, const color_t color)
    {
        // DEBUG
        phi.PrintMinterm();

        /* Minisat vars */
        Var g, f, v, t, e;

        // CNF var
        g = cnf_find_group_var(group);
        f = cnf_new_solver_var();

        // node variable, Then/Else branches vars
        v = cnf_find_term_var(phi); // this will be a new one by construction
        t = cnf_find_term_var(f_factory.make_then(phi));
        e = cnf_find_term_var(f_factory.make_else(phi));

        { // group -> !f, v, e
            vec<Lit> ps;
            ps.push(mkLit(g, true));
            ps.push(mkLit(f, true));
            ps.push(mkLit(v, false));
            ps.push(mkLit(e, false));
            TRACE << ps << endl;
            f_solver.addClause_(ps, color);
        }

        { // group -> f, v, !e
            vec<Lit> ps;
            ps.push(mkLit(g, true));
            ps.push(mkLit(f, false));
            ps.push(mkLit(v, false));
            ps.push(mkLit(e, false));
            TRACE << ps << endl;
            f_solver.addClause_(ps, color);
        }

        { // group -> !f, !v, t
            vec<Lit> ps;
            ps.push(mkLit(g, true));
            ps.push(mkLit(f, true));
            ps.push(mkLit(v, true));
            ps.push(mkLit(t, false));
            TRACE << ps << endl;
            f_solver.addClause_(ps, color);
        }

        { // group -> f, !v, !t
            vec<Lit> ps;
            ps.push(mkLit(g, true));
            ps.push(mkLit(f, false));
            ps.push(mkLit(v, true));
            ps.push(mkLit(t, false));
            TRACE << ps << endl;
            f_solver.addClause_(ps, color);
        }
    } // write_cnf()

};

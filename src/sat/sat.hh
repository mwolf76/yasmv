/**
 *  @file sat.hh
 *  @brief SAT interface
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
#ifndef SAT_H
#define SAT_H

// general purpose decls
#include "satdefs.hh"
#include "terms/ddterms.hh"
#include "proof/proof.hh"
#include "cuddObj.hh"

#include <Map.hh>
#include <Set.hh>
#include <Vec.hh>

// the glorious Minisat SAT solver
#include "core/Solver.hh"
#include "core/SolverTypes.hh"

namespace Minisat {

    class SAT : public IObject {
    public:
        /**
         * @brief Adds a new formula group to the SAT instance.
         */
        inline group_t new_group()
        {
            group_t res = ++ f_next_group;
            f_groups.insert(res);

            return res;
        }

        /**
         * @brief Returns the complete set of defined SAT groups.
         */
        inline const Groups& groups() const
        { return f_groups; }

        /**
         * @brief Adds a new interpolation color to the SAT instance.
         */
        inline color_t new_color()
        {
            color_t res = ++ f_next_color;
            f_colors.insert(res);

            return res;
        }

        /**
         * @brief Returns the complete set of defined interpolation
         * colors.
         */
        inline const Colors& colors() const
        { return f_colors; }

        /**
         * @brief add a formula with a given group and color to the
         * SAT instance.
         */
        inline void push(Term term,
                         group_t group = MAINGROUP,
                         color_t color = BACKGROUND)
        { cnf_push_single_node_cut(term, group, color); }

        /**
         * @brief Solve all groups.
         */
        inline status_t solve()
        { return sat_solve_groups(f_groups); }

        /**
         * @brief Solve only given groups.
         */
        inline status_t solve(const Groups& groups)
        { return sat_solve_groups(groups); }

        /**
         * @brief Last solving status
         */
        inline status_t status() const
        { return f_status; }

        /**
         * @brief Retrieve an interpolant model from the SAT
         * instance. Remark: current status must be STATUS_UNSAT. An
         * exception will be raised otherwise.
         */
        inline Term interpolant(const Colors& a)
        {
            assert (f_status == STATUS_UNSAT);
            return itp_build_interpolant(a);
        }

        /**
         * @brief SAT instancte ctor
         */
        SAT(DDTermFactory& factory)
            : f_factory(factory)
            , f_solver()
            , f_next_group(0)
            , f_next_color(0)
        { TRACE << "Initialized SAT instance @" << this << endl; }

        /**
         * @brief SAT instance dctor
         */
        ~SAT()
        { TRACE << "Destroyed SAT instance@" << this << endl; }

    private:
        // Term factory
        DDTermFactory& f_factory;

        // SAT solver
        Solver f_solver;

        // SAT groups
        Groups f_groups;
        group_t f_next_group;

        // ITP groups (colors)
        Colors f_colors;
        color_t f_next_color;

        status_t f_status;

        // -- CNF ------------------------------------------------------------
        Term2VarMap f_term2var_map;
        inline Var term2var(Term t)
        {
            Term2VarMap::const_iterator eye = f_term2var_map.find(t);
            if (eye != f_term2var_map.end()) {
                return (*eye).second;
            }

            assert(0);
        }

        Var2TermMap f_var2term_map;
        inline Term var2term(Var v)
        {
            Var2TermMap::const_iterator eye = f_var2term_map.find(v);
            if (eye != f_var2term_map.end()) {
                return (*eye).second;
            }

            assert(0);
        }

        Group2VarMap f_groups_map;

        // -- Interpolator -----------------------------------------------------
        typedef struct ptr_hasher<InferenceRule*> InferenceRuleHasher;
        typedef Map< InferenceRule* , Term, InferenceRuleHasher> R2T_Map;

        // The set of clauses belonging to A (B is the complement)
        Set<CRef> a_clauses;

        // The set of variables belonging to A
        Set<Var> a_variables;
        Set<Var> b_variables;

        // [AG] here the definition of "local" is that given by McMillan:
        // for a pair of formulas (A, B), an atom x is local if it
        // contains a variable or uninterpreted function symbol not in B
        // and global otherwise.
        inline bool atom_is_A_local(Var atom) const
        { return !atom_is_of_B(atom); }

        inline bool var_is_A_local(Var var) const
        { return atom_is_A_local(var); }

        inline bool lit_is_A_local(Lit lit) const
        { return atom_is_A_local(var(lit)); }

        inline bool var_is_of_B(Var var) const
        { return atom_is_of_B(var); }

        inline bool lit_is_of_B(Lit lit) const
        { return atom_is_of_B(var(lit)); }

        inline bool var_is_of_A(Var var) const
        { return atom_is_of_A(var); }

        inline bool lit_is_of_A(Lit lit) const
        { return atom_is_of_A(var(lit)); }

        inline bool atom_is_of_A(Var atom) const
        { return a_variables.has(atom); }

        inline bool atom_is_of_B(Var atom) const
        { return b_variables.has(atom); }

        inline bool clause_is_of_A(CRef cr) const
        { return a_clauses.has(cr); }

        // -- Low level services -----------------------------------------------
        Var cnf_new_solver_var();
        Var cnf_find_group_var(group_t group);
        Var cnf_find_term_var(Term phi);
        void cnf_push_single_node_cut(Term phi, const group_t group,
                                      const color_t color);
        void cnf_write(Term phi, const group_t group, const color_t color);

        Term itp_build_interpolant(const Colors& a);
        void itp_init_interpolation(const Colors& ga);

        status_t sat_solve_groups(const Groups& groups);
    }; // SAT instance

}; // minisat

#endif

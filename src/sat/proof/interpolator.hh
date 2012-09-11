/**
 *  @file interpolator.hh
 *  @brief Craig interpolation
 *
 *  This module contains the definitions for Craig
 *  interpolation-related interfaces and classes.
 *
 *  Authors: Alberto Griggio, Marco Pensallorto
 *  Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the addterms of the GNU Lesser General Public
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
#ifndef INTERPOLATOR_H_INCLUDED
#define INTERPOLATOR_H_INCLUDED

// TODO: move this to build system
#define INTERPOLATOR_DEBUG

#include <Map.hh>
#include <Set.hh>
#include <Vec.hh>

#include "proof.hh"
#include "terms/terms.hh"
#include "defs.hh"

namespace Minisat {

    template<class Term>
    class SAT;

    // move me!
    template<class K>
    struct ptr_hasher  {
        uint32_t operator()(const K& k) const {
            return (uint32_t)(reinterpret_cast<size_t>(k));
        }
    };

    template <class Term>
    class Interpolator {

    public:
        Interpolator(SAT<Term>& owner)
            : f_owner(owner)
        {}

        // [MP] uses the Term Factory to build the interpolant. Input
        // unsat proof comes from the associated solver's Proof Manager.
        Term interpolant(int *groups_of_a, unsigned na);

    protected:
        typedef struct ptr_hasher<InferenceRule*> InferenceRuleHasher;
        typedef Map< InferenceRule* , Term, InferenceRuleHasher> R2T_Map;

        // The set of clauses belonging to A (B is the complement)
        Set<CRef> a_clauses;

        // The set of variables belonging to A
        Set<Var> a_variables;
        Set<Var> b_variables;

        // owner instance
        SAT<Term>& f_owner;

        void init_interpolation(int* groups_of_a, unsigned n);

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
    };

}

#endif // INTERPOLATOR_H_INCLUDED

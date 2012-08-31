// -*- C++ -*-
// interpolator.h: Craig interpolation-related interfaces and classes
// Author: Alberto Griggio
//         Marco Pensallorto

#ifndef INTERPOLATOR_H_INCLUDED
#define INTERPOLATOR_H_INCLUDED

#define INTERPOLATOR_DEBUG

#include <Map.hh>
#include <Set.hh>
#include <Vec.hh>

#include "proof.hh"
#include "terms.hh"

namespace Minisat {

  class Interpolator {

    template<class K>
    struct ptr_hasher  {
      uint32_t operator()(const K& k) const {
        return (uint32_t)(reinterpret_cast<size_t>(k));
      }
    };

    typedef struct ptr_hasher<InferenceRule*> InferenceRuleHasher;
    typedef Map< InferenceRule* , Term, InferenceRuleHasher> R2T_Map;

    // Minisat instance
    Solver& f_owner;

    // The term factory used to build the interpolant formula
    TermFactory& f_factory;

  public:
    Interpolator(Solver& owner, TermFactory& factory);
    ~Interpolator();

    // [MP] uses the Term Factory to build the interpolant. Input
    // unsat proof comes from the associated solver's Proof Manager.
    Term interpolant(int *groups_of_a, unsigned na);

  private:

    // The set of clauses belonging to A (B is the complement)
    Set<CRef> a_clauses;

    // The set of variables belonging to A
    Set<Var> a_variables;
    Set<Var> b_variables;

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

/**
 *  @file satdefs.hh
 *  @brief SAT interface
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
#ifndef DEFS_H
#define DEFS_H

#include <common.hh>
#include <pool.hh>

#include <dd.hh>

// the Minisat SAT solver
#include <minisat/core/Solver.h>
#include <minisat/simp/SimpSolver.h>

#include <minisat/core/SolverTypes.h>

using Minisat::Lit;
using Minisat::mkLit;
using Minisat::Var;
using Minisat::lbool;
using Minisat::vec;

using Minisat::Solver;
using Minisat::SimpSolver;

// for microcode
typedef vector<Lit> Lits;
typedef vector<Lits> LitsVector;

typedef unsigned id_t;

typedef enum {
    STATUS_SAT,
    STATUS_UNSAT,
    STATUS_UNKNOWN,
} status_t;

// streaming for various SAT related types
ostream &operator<<(ostream &os, const Minisat::Lit &lit);
ostream &operator<<(ostream &os, const vec<Lit> &lits);
ostream &operator<<(ostream &os, const status_t &status);
ostream &operator<<(ostream &os, const lbool &value);

// move me!
template<class K>
struct ptr_hasher  {
    uint32_t operator()(const K& k) const {
        return (uint32_t)(reinterpret_cast<size_t>(k));
    }
};

typedef Var group_t;
const group_t MAINGROUP(0);

typedef vector<group_t> Groups;

typedef unordered_map<int, Var, IntHash, IntEq> Index2VarMap;

struct VarHash {
    inline long operator() (Var v) const
    { return (long) (v); }
};
struct VarEq {
    inline bool operator() (const Var x,
                            const Var y) const
    { return x == y; }
};
typedef unordered_map<Var, int, VarHash, VarEq> Var2IndexMap;

struct GroupHash {
    inline long operator() (group_t group) const
    { return (long) (group); }
};
struct GroupEq {
    inline bool operator() (const group_t x,
                            const group_t y) const
    { return x == y; }
};
typedef unordered_map<group_t, Var, GroupHash, GroupEq> Group2VarMap;


#endif

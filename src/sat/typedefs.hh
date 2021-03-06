/**
 * @file sat/typedefs.hh
 * @brief SAT module, module-specific type definitions.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA
 *
 **/

#ifndef SAT_TYPEDEFS_H
#define SAT_TYPEDEFS_H

#include <common/common.hh>

#include <dd/dd.hh>

/* decls from the Minisat SAT solver */
#include <minisat/core/Solver.h>
#include <minisat/simp/SimpSolver.h>
#include <minisat/core/SolverTypes.h>

#include <utils/pool.hh>

using Minisat::Lit;
using Minisat::mkLit;
using Minisat::Var;
using Minisat::lbool;
using Minisat::vec;

#include <vector>
typedef std::vector<Var> VarVector;

#include <boost/unordered_map.hpp>
#include <boost/unordered_set.hpp>

using Minisat::Solver;
using Minisat::SimpSolver;

// Engine mgmt
typedef class Engine* Engine_ptr;
typedef class EngineMgr* EngineMgr_ptr;
typedef boost::unordered_set<Engine_ptr> EngineSet;

// for microcode
typedef std::vector<Lit> Lits;
typedef std::vector<Lits> LitsVector;

typedef unsigned id_t;

typedef enum {
    STATUS_SAT,
    STATUS_UNSAT,
    STATUS_UNKNOWN,
} status_t;

#include <enc/tcbi.hh>
typedef boost::unordered_map<TCBI, Var, TCBIHash, TCBIEq> TCBI2VarMap;
typedef boost::unordered_map<Var, TCBI, IntHash, IntEq> Var2TCBIMap;

struct TimedVar {
public:
    TimedVar(Var var, step_t time)
        : f_var(var)
        , f_time(time)
    {}

    inline Var var() const
    { return f_var; }

    inline step_t time() const
    { return f_time; }

    // The CNF var
    Var f_var;

    // expression time (default is 0)
    step_t f_time;
};

struct TimedVarHash {
    inline long operator() (const TimedVar& k) const
    { return 0L; }
};

struct TimedVarEq {
    inline bool operator() (const TimedVar& x, const TimedVar& y) const
    { return (x.var() == y.var() && x.time() == y.time()); }
};

typedef boost::unordered_map<TimedVar, Var, TimedVarHash, TimedVarEq> RewriteMap;

struct TimedDD {
public:
  TimedDD(DdNode *node, step_t time)
    : f_node(node)
    , f_time(time)
  {}

  inline DdNode* node() const
  { return f_node; }

  inline step_t time() const
  { return f_time; }

  // The DdNode node
  DdNode* f_node;

  // expression time (default is 0)
  step_t f_time;
};

struct TimedDDHash {
  inline long operator() (const TimedDD& k) const
  { PtrHash hasher; return hasher( reinterpret_cast<void *> (k.node())); }
};

struct TimedDDEq {
  inline bool operator() (const TimedDD& x, const TimedDD& y) const
  { return (x.node() == y.node() && x.time() == y.time()); }
};

typedef boost::unordered_map<TimedDD, Var, TimedDDHash, TimedDDEq> TDD2VarMap;

// move me!
#if 0
template<class K>
struct ptr_hasher  {
    uint32_t operator()(const K& k) const {
        return (uint32_t)(reinterpret_cast<size_t>(k));
    }
};
#endif

typedef Var group_t;
const group_t MAINGROUP(0);

typedef vec<group_t> Groups;

#include <boost/unordered_map.hpp>
#include <utils/pool.hh>

typedef boost::unordered_map<int, Var, IntHash, IntEq> Index2VarMap;

struct VarHash {
    inline long operator() (Var v) const
    { return (long) (v); }
};

struct VarEq {
    inline bool operator() (const Var x,
                            const Var y) const
    { return x == y; }
};

typedef boost::unordered_map<Var, int, VarHash, VarEq> Var2IndexMap;

struct GroupHash {
    inline long operator() (group_t group) const
    { return (long) (group); }
};

struct GroupEq {
    inline bool operator() (const group_t x,
                            const group_t y) const
    { return x == y; }
};

typedef boost::unordered_map<group_t, Var, GroupHash, GroupEq> Group2VarMap;

#endif /* SAT_TYPDEFS_H */

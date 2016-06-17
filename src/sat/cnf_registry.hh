/**
 *  @file cnf_registry.hh
 *  @brief Engine interface (CNF registry sub-component)
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
#ifndef SAT_CNF_REGISTRY_H
#define SAT_CNF_REGISTRY_H

#include <common.hh>

#include <boost/unordered_map.hpp>

#include <expr/expr.hh>

#include <enc/tcbi.hh>

class Engine; // fwd decl

typedef boost::unordered_map<TCBI, Var, TCBIHash, TCBIEq> TCBI2VarMap;
typedef boost::unordered_map<Var, TCBI, IntHash, IntEq> Var2TCBIMap;

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

class CNFRegistry {

    /* ctor and dctor are available only to SAT owner */
    friend class Engine;

public:

// services for CNF builder
Var find_dd_var(const DdNode* node, step_t time);
Var find_dd_var(int node_index, step_t time);

Var find_cnf_var(const DdNode* node, step_t time);

// services for CNF injector
void clear_cnf_map();
Var rewrite_cnf_var(Var index, step_t time);

private:
    CNFRegistry(Engine& sat);
    ~CNFRegistry();

    Engine& f_sat;

    TDD2VarMap f_tdd2var_map;
    RewriteMap f_rewrite_map;
};

#endif

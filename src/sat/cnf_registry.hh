/**
 *  @file cnf_registry.hh
 *  @brief SAT interface (Time Mapper sub-component)
 *
 *  This module contains the interface for services that implement the
 *  Time Mapper. This service is used to keep a bidirectional mapping
 *  between Timed Canonical Bit Identifiers (or TCBIs) and actual
 *  Minisat Variables.
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

#include <expr.hh>
#include <pool.hh>

#include <common.hh>

class SAT; // fwd decl

typedef unordered_map<TCBI, Var, TCBIHash, TCBIEq> TCBI2VarMap;
typedef unordered_map<Var, TCBI, IntHash, IntEq> Var2TCBIMap;

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

typedef unordered_map<TimedDD, Var, TimedDDHash, TimedDDEq> TDD2VarMap;

class CNFRegistry : public IObject {

    /* ctor and dctor are available only to SAT owner */
    friend class SAT;

public:

Var find_dd_var(const DdNode* node, step_t time);

// DDNode* variant
Var find_cnf_var(const DdNode* node, step_t time);

// Integer variant
Var find_cnf_var(int index, step_t time);

private:
    CNFRegistry(SAT& sat);
    ~CNFRegistry();

    SAT& f_sat;

    TDD2VarMap f_tdd2var_map;
};

#endif

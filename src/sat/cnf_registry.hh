/**
 * @file cnf_registry.hh
 * @brief Engine interface (CNF registry sub-component)
 *
 * This header file contains the declarations required to implement
 * the SAT CNF registry component.
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

#ifndef SAT_CNF_REGISTRY_H
#define SAT_CNF_REGISTRY_H

#include <common/common.hh>

#include <expr/expr.hh>
#include <dd/cudd-2.5.0/obj/cuddObj.hh>
#include <dd/cudd_mgr.hh>

#include <boost/unordered_map.hpp>

#include <sat/typedefs.hh>
#include <sat/inlining.hh>

class Engine;
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

#endif /* SAT_CNF_REGISTRY_H */

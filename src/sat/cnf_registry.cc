/**
 *  @file cnf_registry.cc
 *  @brief SAT interface implementation - CNF Registry
 *
 *  This module contains the interface for services that implement the
 *  CNF Registry. This components is used to keep a central registry
 *  of CNF variables, that both CNF builders and CNF injectors need to
 *  perform their work.
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
#include <utility>

#include <sat.hh>

CNFRegistry::CNFRegistry(Engine& owner)
    : f_sat(owner)
{}

CNFRegistry::~CNFRegistry()
{}

Var CNFRegistry:: find_dd_var(const DdNode* node, step_t time)
{
    assert (NULL != node && ! Cudd_IsConstant(node));
    const UCBI& ucbi
        (f_sat.find_ucbi(node->index));
    const TCBI tcbi
        (ucbi, time);
    return f_sat.tcbi_to_var(tcbi);
}

Var CNFRegistry::find_cnf_var(const DdNode* node, step_t time)
{
    Var res;

    assert (NULL != node);
    TimedDD timed_node (const_cast<DdNode*> (node), time);

    TDD2VarMap::const_iterator eye = \
        f_tdd2var_map.find( timed_node );

    if (f_tdd2var_map.end() == eye) {
        res = f_sat.new_sat_var();

        /* Insert into tdd2var map */
        f_tdd2var_map.insert( std::make_pair<TimedDD, Var>
                              (timed_node, res));
    }
    else {
        res = (*eye).second;
    }
    return res;
}

void CNFRegistry::clear_cnf_map()
{
    f_rewrite_map.clear();
}

Var CNFRegistry::rewrite_cnf_var(Var v, step_t time)
{
    Var res;

    TimedVar timed_var (v, time);
    RewriteMap::const_iterator eye = \
        f_rewrite_map.find( timed_var );

    if (f_rewrite_map.end() == eye) {
        res = f_sat.new_sat_var();

        /* Insert into tvv2var map */
        f_rewrite_map.insert( std::make_pair<TimedVar, Var>
                              (timed_var, res));
    }
    else {
        res = (*eye).second;
    }
    return res;
}


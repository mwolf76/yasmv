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

#include <sat/satdefs.hh>

#include <dd/cudd-2.5.0/obj/cuddObj.hh>
#include <dd/cudd_mgr.hh>

#include <enc/enc_mgr.hh>

#include <model/compiler/unit.hh>

#include <sat/cnf_registry.hh>
#include <sat/time_mapper.hh>

#include <sat/helpers.hh>

std::ostream &operator<<(std::ostream &out, const Lit &lit);
std::ostream &operator<<(std::ostream &out, const vec<Lit> &lits);

class Engine {

public:
    /**
     * @brief Adds a new formula group to the SAT instance.
     */
    inline group_t new_group()
    {
        group_t res = new_sat_var();
        f_groups.push(res);

        return res;
    }

    /**
     * @brief Returns the complete set of defined SAT groups.
     *
     * A positive value of the i-th element of this array enables the
     * i-th group, whereas a negative value disables it.
     */
    inline Groups& groups()
    { return f_groups; }

    /**
     * @brief add a formula to the SAT problem instance.
     */
    void push(CompilationUnit cu, step_t time, group_t group = MAINGROUP);

    /**
     * @brief Enables lazy loading of inlined operator CNF clauses
     */
    MicroLoader& require(const InlinedOperatorSignature& triple);

    /**
     * @brief Invoke Minisat
     */
    inline status_t solve()
    { return sat_solve_groups(f_groups); }

    /**
     * @brief Last solving status
     */
    inline status_t status() const
    { return f_status; }

    /**
     * @brief Fetch variable value from Minisat model
     */
    inline int value(Var var)
    {
        assert (STATUS_SAT == f_status);
        return 0 == Minisat::toInt(f_solver.modelValue(var));
    }

    /**
     * @brief TCBI -> Minisat variable mapping
     */
    inline Var tcbi_to_var(const TCBI& tcbi)
    { return f_mapper.var(tcbi); }

    /**
     * @brief Minisat variable -> TCBI mapping
     */
    inline const TCBI& var_to_tcbi(Var var)
    { return f_mapper.tcbi(var); }

    /**
     * @brief DD index -> UCBI mapping
     */
    inline const UCBI& find_ucbi(int index)
    { return f_enc_mgr.find_ucbi(index); }

    /**
     * @brief Timed model DD nodes to Minisat variable mapping
     */
    inline Var find_dd_var(const DdNode* node, step_t time)
    { return f_registry.find_dd_var(node, time); }

    /**
     * @brief Artifactory DD nodes to Minisat variable mapping
     */
    inline Var find_cnf_var(const DdNode* node, step_t time)
    { return f_registry.find_cnf_var(node, time);  }

    /**
     * @brief CNF registry for injection CNF var
     */
    inline void clear_cnf_map()
    { f_registry.clear_cnf_map(); }

    inline Var rewrite_cnf_var(Var var, step_t time)
    { return f_registry.rewrite_cnf_var(var, time); }

    /**
     * @brief a new Minisat variable
     */
    inline Var new_sat_var() // proxy
    { return f_solver.newVar(); }

    /**
     * @brief add a CNF clause
     */
    inline void add_clause(vec<Lit>& ps) // proxy
    { f_solver.addClause_(ps); }

    /**
     * @brief SAT instance ctor
     */
    Engine();

    /**
     * @brief SAT instance dctor
     */
    ~Engine() {}

private:
    EncodingMgr& f_enc_mgr;

    // TCBI <-> var mapping
    TimeMapper& f_mapper;

    // CNF registry,
    CNFRegistry f_registry;

    // SAT solver, currently Minisat
    Solver f_solver;

    // used to partition the formula to be solved
    Groups f_groups;

    // last solve() status
    status_t f_status;

    // -- CNF ------------------------------------------------------------
    Index2VarMap f_index2var_map;
    inline Var index2var(int index)
    {
        Index2VarMap::const_iterator eye = f_index2var_map.find(index);
        if (eye != f_index2var_map.end()) {
            return (*eye).second;
        }

        return -1; /* cnf var */
    }

    Var2IndexMap f_var2index_map;
    inline int var2index(Var v)
    {
        Var2IndexMap::const_iterator eye = f_var2index_map.find(v);
        if (eye != f_var2index_map.end()) {
            return (*eye).second;
        }

        return -1; /* cnf var */
    }

    Group2VarMap f_groups_map;

    // -- Low level services -----------------------------------------------
    Lit cnf_find_group_lit(group_t group, bool enabled = true);

    status_t sat_solve_groups(const Groups& groups);

    /* CNFization algorithms */
    void cnf_push_no_cut(ADD add, step_t time, const group_t group);
    void cnf_push_single_cut(ADD add, step_t time, const group_t group);
};

#endif

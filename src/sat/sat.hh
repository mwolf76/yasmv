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

#include <satdefs.hh>
#include <cuddObj.hh>

#include <cudd_mgr.hh>
#include <enc_mgr.hh>

#include <micro.hh>

#include <time_mapper.hh>

using std::ostream;

ostream &operator<<(ostream &out, const Lit &lit);
ostream &operator<<(ostream &out, const Clause *clause);
ostream &operator<<(ostream &out, const Clause &clause);
ostream &operator<<(ostream &out, const vec<Lit> &lits);

class SAT : public IObject {
    friend class CNFBuilderSingleCut;
    friend class CNFBuilderNoCut;

public:
    /**
     * @brief Adds a new formula group to the SAT instance.
     */
    inline group_t new_group()
    {
        group_t res = new_sat_var();
        f_groups.push_back(res);

        return res;
    }

    /**
     * @brief Returns the complete set of defined SAT groups.
     */
    inline Groups& groups()
    { return f_groups; }

    /**
     * @brief add a formula to the SAT problem instance.
     */
    inline void push(Term term, step_t time, group_t group = MAINGROUP)
    {
        unsigned n, m;

        // push DDs
        const DDVector& dv( term.formula()); n = dv.size();
        TRACE << "CNFizing "<< n << " fragments" << endl;

        DDVector::const_iterator i;
        for (i = dv.begin(); dv.end() != i; ++ i) {
            // TODO: additional CNF algorithms
            cnf_push_single_cut( *i, time, group );
        }

        const MicroDescriptors& descriptors (term.descriptors()); m = descriptors.size();
        TRACE << "Injecting " << m << " microcode descriptors" << endl;

        MicroDescriptors::const_iterator j;
        for (j = descriptors.begin(); descriptors.end() != j; ++ j)  {
            cnf_inject_microcode( *j, time, group );
        }
    }

    /* shortcut */
    inline void toggle_last_group()
    { (*f_groups.rbegin()) *= -1; }

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

    inline int value(Var var)
    {
        assert (STATUS_SAT == f_status);
        return 0 == Minisat::toInt(f_solver.modelValue(var));
    }

    inline Var tcbi_to_var(const TCBI& tcbi)
    { return f_mapper.var(tcbi); }

    inline const TCBI& var_to_tcbi(Var var)
    { return f_mapper.tcbi(var); }

    /**
     * @brief SAT instancte ctor
     */
    SAT(/* DDTermFactory& factory */)
        // : f_factory(factory)
        : f_enc_mgr(EncodingMgr::INSTANCE())
        , f_mapper(* new TimeMapper(*this))
        , f_solver()
    {
        f_groups.push_back(new_sat_var()); // MAINGROUP is already there.
        // DEBUG << "Initialized SAT instance @" << this << endl;
    }

    /**
     * @brief SAT instance dctor
     */
    ~SAT() {}

    /* Internal services */
    inline Var new_sat_var() // proxy
    { return f_solver.newVar(); }

    inline const UCBI& find_ucbi(int index) // proxy
    { return f_enc_mgr.find_ucbi(index); }

private:
    // // Term factory
    // DDTermFactory& f_factory;

    // Enc Mgr
    EncodingMgr& f_enc_mgr;

    // TimeMapper
    TimeMapper& f_mapper;

    // SAT solver
    Solver f_solver;

    // SAT groups (just ordinary Minisat Vars)
    Groups f_groups;

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

    // CNFization algorithms
    void cnf_push_no_cut(ADD add, step_t time, const group_t group);
    void cnf_push_single_cut(ADD add, step_t time, const group_t group);
    void cnf_inject_microcode(MicroDescriptor md, step_t time, const group_t group);
}; // SAT instance

#endif

/**
 * @file sat/engine.hh
 * @brief SAT interface, Engine class declaration.
 *
 * This module contains the interface for services that implement an
 * CNF clauses generation in a form that is suitable for direct
 * injection into the SAT solver.
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

#ifndef SAT_ENGINE_H
#define SAT_ENGINE_H

#include <enc/enc_mgr.hh>

#include <compiler/typedefs.hh>

#include <sat/typedefs.hh>

#include <utils/logging.hh>

#include <algorithm>
#include <unordered_set>
#include <vector>

namespace sat {

    class Engine {
    public:
        /**
	 * @brief Adds a new formula group to the SAT instance.
	 */
        inline group_t new_group()
        {
            group_t res(new_sat_var());

            f_groups.push(res);

            DEBUG
                << "Created new group var "
                << res
                << std::endl;

            return res;
        }

        /**
	 * @brief Invert last group for the SAT instance.
	 */
        inline void invert_last_group()
        {
            f_groups.last() *= -1;
        }

        /**
	 * @brief Returns the complete set of defined SAT groups.
	 *
	 * A positive value of the i-th element of this array enables the
	 * i-th group, whereas a negative value disables it.
	 */
        inline Groups& groups()
        {
            return f_groups;
        }

        /**
	 * @brief add a formula to the SAT problem instance.
	 */
        void push(compiler::Unit cu, step_t time, group_t group = MAINGROUP);

        /**
	 * @brief Invoke Minisat
	 */
        inline status_t solve()
        {
            return sat_solve_groups(f_groups);
        }
	
        /**
	 * @brief Interrupt Minisat
	 */
        inline void interrupt()
        {
            f_solver.interrupt();
        }

        /**
	 * @brief Configure Minisat
	 */
        inline void configure(int64_t conf_budget, int64_t prop_budget)
        {
            f_solver.setConfBudget(conf_budget);
            f_solver.setPropBudget(prop_budget);
        }

        /**
	 * @brief Last solving status
	 */
        inline status_t status() const
        {
            return f_status;
        }

        /**
	 * @brief Fetch variable value from Minisat model
	 */
        inline int value(Var var)
        {
            assert(STATUS_SAT == f_status);
            return 0 == Minisat::toInt(f_solver.modelValue(var));
        }

        /**
	 * @brief TCBI -> Minisat variable mapping
	 */
        Var tcbi_to_var(const enc::TCBI& tcbi);

        /**
	 * @brief Minisat variable -> TCBI mapping
	 */
        enc::TCBI& var_to_tcbi(Var var);

        /**
	 * @brief DD index -> UCBI mapping
	 */
        const enc::UCBI& find_ucbi(int index)
        {
            return f_enc_mgr.find_ucbi(index);
        }

        /**
	 * @brief Timed model DD nodes to Minisat variable mapping
	 */
        Var find_dd_var(const DdNode* node, step_t time);

        /**
	 * @brief Timed model DD nodes to Minisat variable mapping
	 */
        Var find_dd_var(int node_index, step_t time);

        /**
	 * @brief Artifactory DD nodes to Minisat variable mapping
	 */
        Var find_cnf_var(const DdNode* node, step_t time);

        /**
	 * @brief CNF registry for injection CNF var
	 */
        void clear_cnf_map();

        /**
	 * @brief Rewrites a CNF var
	 */
        Var rewrite_cnf_var(Var var, step_t time);

        /**
	 * @brief a new Minisat variable
	 */
        inline Var new_sat_var(bool frozen = false) // proxy
        {
            Var var(f_solver.newVar());

            f_solver.setFrozen(var, frozen);

            return var;
        }
	
        /**
	 * @brief add a CNF clause
	 */
        inline void add_clause(vec<Lit>& ps) // proxy
        {
            if (f_cnf_optimization_enabled && !f_optimization_in_progress) {
                // Store clause for later optimization
                std::vector<Lit> clause_copy;
                clause_copy.reserve(ps.size());
                for (int i = 0; i < ps.size(); ++i) {
                    clause_copy.push_back(ps[i]);
                }
                f_pending_clauses.push_back(std::move(clause_copy));
            } else {
                // Direct addition to solver
                f_solver.addClause_(ps);
            }
        }
        
        /**
         * @brief Enable/disable CNF optimization
         */
        void enable_cnf_optimization(bool enable = true);
        
        /**
         * @brief Optimize pending clauses and commit to solver
         */
        void optimize_and_commit();

        /**
	 * @brief SAT instance ctor
	 */
        Engine(const char* instance_name);

        /**
	 * @brief SAT instance dctor
	 */
        ~Engine();

        inline enc::EncodingMgr& enc() const
        {
            return f_enc_mgr;
        }

    private:
        const char* f_instance_name;

        enc::EncodingMgr& f_enc_mgr;

        // CNF registry
        TDD2VarMap f_tdd2var_map;
        RewriteMap f_rewrite_map;

        // Bidirectional time mapping
        TCBI2VarMap f_tcbi2var_map;
        Var2TCBIMap f_var2tcbi_map;

        // SAT solver, currently Minisat
        SimpSolver f_solver;

        // used to partition the formula to be solved using assumptions
        Groups f_groups;

        // last solve() status
        status_t f_status;

        // -- CNF ------------------------------------------------------------
        Index2VarMap f_index2var_map;
        inline Var index2var(int index)
        {
            Index2VarMap::const_iterator eye(f_index2var_map.find(index));

            if (eye != f_index2var_map.end())
                return (*eye).second;

            return -1; /* cnf var */
        }

        Var2IndexMap f_var2index_map;
        inline int var2index(Var v)
        {
            Var2IndexMap::const_iterator eye(f_var2index_map.find(v));

            if (eye != f_var2index_map.end())
                return (*eye).second;

            return -1; /* cnf var */
        }

        Group2VarMap f_groups_map;
        
        // -- CNF Optimization ------------------------------------------------
        bool f_cnf_optimization_enabled;
        bool f_optimization_in_progress;
        // Store clauses as std::vector of Lit to avoid MiniSat vec copy issues
        std::vector<std::vector<Lit>> f_pending_clauses;
        
        // Optimization statistics
        struct OptimizationStats {
            size_t original_clauses;
            size_t removed_tautologies;
            size_t removed_duplicates;
            size_t removed_subsumed;
            size_t final_clauses;
            
            void reset() {
                original_clauses = 0;
                removed_tautologies = 0;
                removed_duplicates = 0;
                removed_subsumed = 0;
                final_clauses = 0;
            }
        } f_opt_stats;
        
        // Optimization methods
        void remove_tautologies();
        void remove_duplicates();
        void subsumption_elimination();
        void optimize_cnf();
        
        // Helper methods for optimization
        static inline Lit negate_literal(Lit lit) {
            // In MiniSat, negation is done by XOR with 1
            return lit ^ 1;
        }
        
        static inline bool are_complementary(Lit lit1, Lit lit2) {
            return lit1 == ~lit2;
        }
        
        bool has_tautology(const std::vector<Lit>& clause);
        bool is_subsumed(const std::vector<Lit>& clause1, const std::vector<Lit>& clause2);

        // -- Low level services -----------------------------------------------
        Lit cnf_find_group_lit(group_t group, bool enabled = true);

        status_t sat_solve_groups(const Groups& groups);

        /* CNFization algorithms */
        void cnf_push(ADD add, step_t time, const group_t group);

        friend std::ostream& operator<<(std::ostream& os, const Engine& engine);
    };

    std::ostream& operator<<(std::ostream& os, const Engine& engine);

}; // namespace sat

#endif /* SAT_ENGINE_H */

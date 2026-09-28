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
#include <functional>
#include <memory>
#include <query/runtime.hh>

namespace sat {

    class Engine;
    // Optional algorithm seam for deterministic solver-status tests.
    using SolveCallback = std::function<status_t(Engine&)>;

    class Engine {
    public:
        /**
	 * @brief Adds a new formula group to the SAT instance.
	 */
        inline group_t new_group()
        {
            group_t res(new_sat_var(true));

            f_groups.push_back(res);

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
            invalidate_result();
            f_groups.back() *= -1;
        }

        /**
	 * @brief Returns the complete set of defined SAT groups.
	 *
	 * A positive value of the i-th element of this array enables the
	 * i-th group, whereas a negative value disables it.
	 */
        inline Groups& groups()
        {
            invalidate_result();
            return f_groups;
        }
        const Groups& groups() const { return f_groups; }

        /**
	 * @brief add a formula to the SAT problem instance.
	 */
        void push(compiler::Unit cu, step_t time, group_t group = MAINGROUP);

        /**
	 * @brief Invoke SAT
	 */
        std::vector<group_t> failed_groups() const;

        inline status_t solve()
        {
            return sat_solve_groups(f_groups);
        }
	
        /**
	 * @brief Interrupt SAT
	 */
        void interrupt();

        /**
	 * @brief Configure SAT
	 */
        void configure(int64_t conf_budget, int64_t prop_budget);

        /**
	 * @brief Last solving status
	 */
        inline status_t status() const
        {
            return f_status;
        }

        /**
	 * @brief Fetch variable value from SAT model
	 */
        bool assigned(Var var);
        int value(Var var);
        Var existing_var(const enc::TCBI& tcbi) const;
        static const char* solver_version();
        static const char* solver_signature();

        /**
	 * @brief TCBI -> SAT variable mapping
	 */
        Var tcbi_to_var(const enc::TCBI& tcbi);

        /**
	 * @brief SAT variable -> TCBI mapping
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
	 * @brief Timed model DD nodes to SAT variable mapping
	 */
        Var find_dd_var(const DdNode* node, step_t time);

        /**
	 * @brief Timed model DD nodes to SAT variable mapping
	 */
        Var find_dd_var(int node_index, step_t time);

        /**
	 * @brief Artifactory DD nodes to SAT variable mapping
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
	 * @brief a new SAT variable
	 */
        Var new_sat_var(bool frozen = false);
	
        /**
	 * @brief add a CNF clause
	 */
        void add_clause(const Lits& literals);
        
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

        // Keep solver headers and native types behind the implementation boundary.
        class Backend;
        std::unique_ptr<Backend> f_solver;
        void commit_clause(const Lits& literals);
        void invalidate_result();

        // used to partition the formula to be solved using assumptions
        Groups f_groups;

        // last solve() status
        status_t f_status = STATUS_UNKNOWN;
        std::vector<group_t> f_failed_groups;

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
        LitsVector f_pending_clauses;
        
        // Optimization statistics
        struct OptimizationStats {
            size_t original_clauses;
            size_t removed_tautologies;
            size_t removed_duplicates;
            size_t removed_subsumed;
            size_t removed_by_var_elim;
            size_t removed_by_self_subsumption;
            size_t removed_blocked;
            size_t final_clauses;
            
            // Timing information (in milliseconds)
            double total_time_ms;
            double tautology_time_ms;
            double duplicate_time_ms;
            double subsumption_time_ms;
            double var_elim_time_ms;
            double self_subsumption_time_ms;
            double blocked_clause_time_ms;
            
            void reset() {
                original_clauses = 0;
                removed_tautologies = 0;
                removed_duplicates = 0;
                removed_subsumed = 0;
                removed_by_var_elim = 0;
                removed_by_self_subsumption = 0;
                removed_blocked = 0;
                final_clauses = 0;
                total_time_ms = 0.0;
                tautology_time_ms = 0.0;
                duplicate_time_ms = 0.0;
                subsumption_time_ms = 0.0;
                var_elim_time_ms = 0.0;
                self_subsumption_time_ms = 0.0;
                blocked_clause_time_ms = 0.0;
            }
        } f_opt_stats;
        
        // Optimization methods
        void remove_tautologies();
        void remove_duplicates();
        void subsumption_elimination();
        void variable_elimination();
        void self_subsuming_resolution();
        void blocked_clause_elimination();
        void optimize_cnf();
        
        // Helper methods for optimization
        static inline Lit negate_literal(Lit lit) {
            return ~lit;
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

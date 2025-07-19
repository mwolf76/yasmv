/**
 * @file sat/engine.cc
 * @brief SAT interface subsystem, Engine class implementation.
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

#include <cstdlib>
#include <set>
#include <sat.hh>

namespace sat {

    /**
 * @brief SAT instancte ctor
 */
    Engine::Engine(const char* instance_name)
        : f_instance_name(instance_name)
        , f_enc_mgr(enc::EncodingMgr::INSTANCE())
        , f_cnf_optimization_enabled(true)  // Enable by default
        , f_optimization_in_progress(false)
    {
        const void* instance { this };

        /* Default configuration */
        f_solver.random_var_freq = .1;
        // f_solver.ccmin_mode = 0;
        // f_solver.phase_saving = 0;
        f_solver.rnd_init_act = true;
        f_solver.garbage_frac = 0.50;

        /* MAINGROUP (=0) is already there. */
        f_groups.push(new_sat_var());

        EngineMgr::INSTANCE()
            .register_instance(this);

        DEBUG
            << "Initialized Engine instance @"
            << instance
            << std::endl;
    }

    Engine::~Engine()
    {
        EngineMgr::INSTANCE()
            .unregister_instance(this);
    }

    status_t Engine::sat_solve_groups(const Groups& groups)
    {
        // Optimize pending clauses before solving
        optimize_and_commit();
        
        vec<Lit> assumptions;

        clock_t t0 { clock() };
        for (int i = 0; i < groups.size(); ++i) {
            Var grp { groups[i] };

            /* Assumptions work like "a -> phi". Here we use both
             * polarities of the implication, that is a positive group
             * var asserts the formulas in the group whereas a
             * negative group var asserts the negation of those
             * formulas. */
            assumptions.push(mkLit(abs(grp), grp < 0));
        }

        DEBUG
            << "Solving ..."
            << std::endl;

        Minisat::lbool status { f_solver.solveLimited(assumptions) };
        if (status == l_True) {
            f_status = STATUS_SAT;
        } else if (status == l_False) {
            f_status = STATUS_UNSAT;
        } else if (status == l_Undef) {
            f_status = STATUS_UNKNOWN;
        } else {
            assert(false); /* unreachable */
        }

        clock_t elapsed { clock() - t0 };
        double secs { (double) elapsed / (double) CLOCKS_PER_SEC };

        DEBUG
            << "Took "
            << secs
            << " seconds. Status is "
            << f_status << "."
            << std::endl;

        return f_status;
    }

    void Engine::push(compiler::Unit cu, step_t time, group_t group)
    {
        /**
         * 1. Pushing DDs
         */
        {
            const dd::DDVector& dv { cu.dds() };
            dd::DDVector::const_iterator i;
            for (i = dv.begin(); dv.end() != i; ++i) {
                cnf_push_single_cut(*i, time, group);
                // cnf_push_no_cut( *i, time, group );
            }
        }

        /**
         * 2. Pushing CNF for inlined operators
         */
        {
            const compiler::InlinedOperatorDescriptors& inlined_operator_descriptors {
                cu.inlined_operator_descriptors()
            };

            compiler::InlinedOperatorDescriptors::const_iterator i;
            for (i = inlined_operator_descriptors.begin();
                 inlined_operator_descriptors.end() != i; ++i) {

                CNFOperatorInliner worker { *this, time, group };
                worker(*i);
            }
        }

        /**
         * 3. Pushing ITE MUXes
         */
        {
            const compiler::Expr2BinarySelectionDescriptorsMap& binary_selection_descriptors_map {
                cu.binary_selection_descriptors_map()
            };

            compiler::Expr2BinarySelectionDescriptorsMap::const_iterator mmi {
                binary_selection_descriptors_map.begin()
            };

            while (binary_selection_descriptors_map.end() != mmi) {
                expr::Expr_ptr toplevel { mmi->first };

                compiler::BinarySelectionDescriptors descriptors { mmi->second };

                compiler::BinarySelectionDescriptors::const_iterator i;
                for (i = descriptors.begin(); descriptors.end() != i; ++i) {
                    CNFBinarySelectionInliner worker { *this, time, group };
                    worker(*i);
                }

                ++mmi;
            }
        }

        /**
         * 4. Pushing ARRAY MUXes
         */
        {
            const compiler::MultiwaySelectionDescriptors& muxes {
                cu.array_mux_descriptors()
            };
            compiler::MultiwaySelectionDescriptors::const_iterator i;
            for (i = muxes.begin(); muxes.end() != i; ++i) {
                CNFMultiwaySelectionInliner worker { *this, time, group };
                worker(*i);
            }
        }
    }

    Var Engine::find_dd_var(const DdNode* node, step_t time)
    {
        assert(NULL != node && !Cudd_IsConstant(node));
        const enc::UCBI& ucbi { find_ucbi(node->index) };
        const enc::TCBI tcbi { ucbi, time };
        return tcbi_to_var(tcbi);
    }

    Var Engine::find_dd_var(int node_index, step_t time)
    {
        const enc::UCBI& ucbi { find_ucbi(node_index) };
        const enc::TCBI tcbi { ucbi, time };
        return tcbi_to_var(tcbi);
    }

    Var Engine::find_cnf_var(const DdNode* node, step_t time)
    {
        Var res;

        assert(NULL != node);
        TimedDD timed_node { const_cast<DdNode*>(node), time };

        TDD2VarMap::const_iterator eye { f_tdd2var_map.find(timed_node) };
        if (f_tdd2var_map.end() == eye) {
            res = new_sat_var();

            /* Insert into tdd2var map */
            f_tdd2var_map.insert(std::pair<TimedDD, Var>(timed_node, res));

#if 0
            DRIVEL
                << "Created cnf var "
                << res
                << " for DD node "
                << node
                << std::endl;
#endif
        } else {
            res = (*eye).second;
        }
        return res;
    }

    void Engine::clear_cnf_map()
    {
        f_rewrite_map.clear();
    }

    Var Engine::rewrite_cnf_var(Var v, step_t time)
    {
        Var res;

        TimedVar timed_var(v, time);
        RewriteMap::const_iterator eye {
            f_rewrite_map.find(timed_var)
        };

        if (f_rewrite_map.end() == eye) {
            res = new_sat_var();

            /* Insert into tvv2var map */
            f_rewrite_map.insert(std::pair<TimedVar, Var>(timed_var, res));

#if 0
            DRIVEL
                << "Rewrote microcode cnf var "
                << v << "@" << time
                << " as "
                << res
                << std::endl;
#endif
        } else {
            res = (*eye).second;
        }
        return res;
    }

    Var Engine::tcbi_to_var(const enc::TCBI& tcbi)
    {
        Var var;
        const TCBI2VarMap::iterator eye {
            f_tcbi2var_map.find(tcbi)
        };

        if (f_tcbi2var_map.end() != eye) {
            var = eye->second;
        } else {
            /* generate a new var and book it. Newly created var is not eliminable. */
            var = new_sat_var(true);

            DRIVEL
                << "Adding model var " << var
                << " for " << tcbi
                << std::endl;

            f_tcbi2var_map.insert(std::pair<enc::TCBI, Var>(tcbi, var));
            f_var2tcbi_map.insert(std::pair<Var, enc::TCBI>(var, tcbi));
        }

        return var;
    }

    enc::TCBI& Engine::var_to_tcbi(Var var)
    {
        const Var2TCBIMap::iterator eye {
            f_var2tcbi_map.find(var)
        };

        /* TCBI *has* to be there already. */
        assert(f_var2tcbi_map.end() != eye);

        return eye->second;
    }
    
    // -- CNF Optimization Implementation -------------------------------------
    
    void Engine::enable_cnf_optimization(bool enable)
    {
        f_cnf_optimization_enabled = enable;
        
        const char* status_str = enable ? "enabled" : "disabled";
        DEBUG
            << "CNF optimization "
            << status_str
            << std::endl;
    }
    
    void Engine::optimize_and_commit()
    {
        if (!f_cnf_optimization_enabled || f_pending_clauses.empty()) {
            return;
        }
        
        f_optimization_in_progress = true;
        f_opt_stats.reset();
        f_opt_stats.original_clauses = f_pending_clauses.size();
        
        TRACE
            << "Starting CNF optimization with "
            << f_opt_stats.original_clauses
            << " clauses"
            << std::endl;
        
        // Run optimization pipeline
        optimize_cnf();
        
        // Commit optimized clauses to solver
        for (auto& clause : f_pending_clauses) {
            vec<Lit> ps;
            for (auto lit : clause) {
                ps.push(lit);
            }
            f_solver.addClause_(ps);
        }
        
        f_opt_stats.final_clauses = f_pending_clauses.size();
        
        size_t removed = f_opt_stats.original_clauses - f_opt_stats.final_clauses;
        double reduction = (100.0 * removed) / f_opt_stats.original_clauses;
        
        INFO
            << "CNF optimization complete: "
            << f_opt_stats.original_clauses << " -> "
            << f_opt_stats.final_clauses << " clauses "
            << "(" << removed
            << " removed, "
            << reduction
            << "% reduction)"
            << std::endl;
        
        DEBUG
            << "  Tautologies removed: " << f_opt_stats.removed_tautologies
            << ", Duplicates removed: " << f_opt_stats.removed_duplicates
            << ", Subsumed removed: " << f_opt_stats.removed_subsumed
            << std::endl;
        
        // Clear pending clauses
        f_pending_clauses.clear();
        f_optimization_in_progress = false;
    }
    
    void Engine::optimize_cnf()
    {
        // Run optimization passes in sequence
        remove_tautologies();
        remove_duplicates();
        // subsumption_elimination(); // Disabled - too heavy for now
    }
    
    bool Engine::has_tautology(const std::vector<Lit>& clause)
    {
        // Use set instead of unordered_set to avoid hash issues with Lit
        std::set<int> seen;
        for (auto lit : clause) {
            int lit_int = toInt(lit);
            int neg_lit_int = toInt(~lit);
            if (seen.count(neg_lit_int) > 0) {
                return true;
            }
            seen.insert(lit_int);
        }
        return false;
    }
    
    void Engine::remove_tautologies()
    {
        std::vector<std::vector<Lit>> result;
        result.reserve(f_pending_clauses.size());
        
        for (auto& clause : f_pending_clauses) {
            if (!has_tautology(clause)) {
                result.push_back(std::move(clause));
            } else {
                f_opt_stats.removed_tautologies++;
            }
        }
        
        f_pending_clauses = std::move(result);
    }
    
    void Engine::remove_duplicates()
    {
        // First sort literals within each clause
        for (auto& clause : f_pending_clauses) {
            std::sort(clause.begin(), clause.end(),
                [](Lit a, Lit b) { return toInt(a) < toInt(b); });
        }
        
        // Sort clauses for efficient duplicate detection
        std::sort(f_pending_clauses.begin(), f_pending_clauses.end(),
            [](const std::vector<Lit>& a, const std::vector<Lit>& b) {
                if (a.size() != b.size()) return a.size() < b.size();
                for (size_t i = 0; i < a.size(); ++i) {
                    if (toInt(a[i]) != toInt(b[i])) {
                        return toInt(a[i]) < toInt(b[i]);
                    }
                }
                return false;
            });
        
        // Remove duplicates
        std::vector<std::vector<Lit>> result;
        result.reserve(f_pending_clauses.size());
        
        for (size_t i = 0; i < f_pending_clauses.size(); ++i) {
            bool is_duplicate = false;
            
            // Check if this clause is a duplicate of the previous one
            if (i > 0) {
                const auto& prev = f_pending_clauses[i-1];
                const auto& curr = f_pending_clauses[i];
                
                if (prev.size() == curr.size()) {
                    is_duplicate = true;
                    for (size_t j = 0; j < prev.size(); ++j) {
                        if (toInt(prev[j]) != toInt(curr[j])) {
                            is_duplicate = false;
                            break;
                        }
                    }
                }
            }
            
            if (!is_duplicate) {
                result.push_back(std::move(f_pending_clauses[i]));
            } else {
                f_opt_stats.removed_duplicates++;
            }
        }
        
        f_pending_clauses = std::move(result);
    }
    
    bool Engine::is_subsumed(const std::vector<Lit>& smaller, const std::vector<Lit>& larger)
    {
        if (smaller.size() > larger.size()) return false;
        
        size_t j = 0;
        for (size_t i = 0; i < smaller.size(); ++i) {
            while (j < larger.size() && toInt(larger[j]) < toInt(smaller[i])) {
                j++;
            }
            if (j >= larger.size() || toInt(larger[j]) != toInt(smaller[i])) {
                return false;
            }
        }
        return true;
    }
    
    void Engine::subsumption_elimination()
    {
        // Clauses are already sorted by size from remove_duplicates
        std::vector<bool> subsumed(f_pending_clauses.size(), false);
        
        // For each clause, check if it's subsumed by any smaller clause
        for (size_t i = 0; i < f_pending_clauses.size(); ++i) {
            if (subsumed[i]) continue;
            
            for (size_t j = 0; j < i; ++j) {
                if (subsumed[j]) continue;
                if (f_pending_clauses[j].size() > f_pending_clauses[i].size()) break;
                
                if (is_subsumed(f_pending_clauses[j], f_pending_clauses[i])) {
                    subsumed[i] = true;
                    f_opt_stats.removed_subsumed++;
                    break;
                }
            }
        }
        
        // Collect non-subsumed clauses
        std::vector<std::vector<Lit>> result;
        result.reserve(f_pending_clauses.size());
        
        for (size_t i = 0; i < f_pending_clauses.size(); ++i) {
            if (!subsumed[i]) {
                result.push_back(std::move(f_pending_clauses[i]));
            }
        }
        
        f_pending_clauses = std::move(result);
    }

}; // namespace sat

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
#include <opts/opts_mgr.hh>

namespace sat {

    /**
 * @brief SAT instance ctor
 */
    Engine::Engine(const char* instance_name)
        : f_instance_name(instance_name)
        , f_enc_mgr(enc::EncodingMgr::INSTANCE())
        , f_cnf_optimization_enabled(false)  // Disabled by default (performance reasons)
        , f_optimization_in_progress(false)
    {
        const void* instance { this };

        /* Default configuration */
        opts::OptsMgr& opts_mgr { opts::OptsMgr::INSTANCE() };
        f_solver.random_var_freq = opts_mgr.sat_random_var_freq();
        f_solver.ccmin_mode = opts_mgr.sat_ccmin_mode();
        f_solver.phase_saving = opts_mgr.sat_phase_saving();
        f_solver.rnd_init_act = opts_mgr.sat_random_init_act();
        f_solver.garbage_frac = opts_mgr.sat_garbage_frac();
        f_solver.var_decay = opts_mgr.sat_var_decay();
        f_solver.clause_decay = opts_mgr.sat_clause_decay();
        f_solver.random_seed = opts_mgr.sat_random_seed();
        f_solver.luby_restart = opts_mgr.sat_luby_restart();
        f_solver.restart_first = opts_mgr.sat_restart_first();
        f_solver.restart_inc = opts_mgr.sat_restart_inc();
        f_solver.use_elim = opts_mgr.sat_elim();
        f_solver.use_rcheck = opts_mgr.sat_rcheck();
        f_solver.use_asymm = opts_mgr.sat_asymm();
        f_solver.grow = opts_mgr.sat_grow();
        f_solver.clause_lim = opts_mgr.sat_clause_lim();
        f_solver.subsumption_lim = opts_mgr.sat_subsumption_lim();
        f_solver.simp_garbage_frac = opts_mgr.sat_simp_garbage_frac();
        
        /* Enable CNF optimization if any individual optimization is enabled */
        if (opts_mgr.cnf_tautology_removal() || 
            opts_mgr.cnf_duplicate_removal() ||
            opts_mgr.cnf_subsumption() ||
            opts_mgr.cnf_variable_elimination() ||
            opts_mgr.cnf_self_subsumption() ||
            opts_mgr.cnf_blocked_clause()) {
            enable_cnf_optimization(true);
        }

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

        const clock_t t0 { clock() };
        for (int i = 0; i < groups.size(); ++i) {
            const Var grp { groups[i] };

            /* Assumptions work like "a -> phi". Here we use both
             * polarities of the implication, that is a positive group
             * var asserts the formulas in the group whereas a
             * negative group var asserts the negation of those
             * formulas. */
            assumptions.push(mkLit(abs(grp), grp < 0));
        }

        TRACE
            << "Solving ..."
            << std::endl;

        if (const lbool status { f_solver.solveLimited(assumptions) }; status == l_True) {
            f_status = STATUS_SAT;
        } else if (status == l_False) {
            f_status = STATUS_UNSAT;
        } else if (status == l_Undef) {
            f_status = STATUS_UNKNOWN;
        } else {
            assert(false); /* unreachable */
        }

        const clock_t elapsed { clock() - t0 };
        double secs { static_cast<double>(elapsed) / static_cast<double>(CLOCKS_PER_SEC) };

        TRACE
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
                cnf_push(*i, time, group);
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
        if (f_pending_clauses.empty()) {
            return;
        }

        clock_t start_time = clock();
        f_opt_stats.reset();
        f_opt_stats.original_clauses = f_pending_clauses.size();

        if (f_cnf_optimization_enabled) {
            f_optimization_in_progress = true;

            TRACE
                << "Starting CNF optimization with "
                << f_opt_stats.original_clauses
                << " clauses"
                << std::endl;

            // Run optimization pipeline with timing
            optimize_cnf();

            f_opt_stats.final_clauses = f_pending_clauses.size();
            
            size_t removed = f_opt_stats.original_clauses - f_opt_stats.final_clauses;
            double reduction = (removed > 0) ? (100.0 * removed) / f_opt_stats.original_clauses : 0.0;
            
            clock_t opt_time = clock() - start_time;
            double opt_secs = (double)opt_time / CLOCKS_PER_SEC;
            f_opt_stats.total_time_ms = opt_secs * 1000;
            
            INFO
                << "CNF optimization complete: "
                << f_opt_stats.original_clauses << " -> "
                << f_opt_stats.final_clauses << " clauses "
                << "(" << removed
                << " removed, "
                << reduction
                << "% reduction) in "
                << opt_secs << " seconds"
                << std::endl;
            
            DEBUG
                << "  Tautologies: " << f_opt_stats.removed_tautologies
                << " (" << f_opt_stats.tautology_time_ms << "ms)"
                << ", Duplicates: " << f_opt_stats.removed_duplicates
                << " (" << f_opt_stats.duplicate_time_ms << "ms)"
                << ", Subsumed: " << f_opt_stats.removed_subsumed
                << " (" << f_opt_stats.subsumption_time_ms << "ms)"
                << std::endl;
            
            if (f_opt_stats.removed_by_var_elim || f_opt_stats.removed_by_self_subsumption || f_opt_stats.removed_blocked) {
                DEBUG
                    << "  Var elim: " << f_opt_stats.removed_by_var_elim
                    << " (" << f_opt_stats.var_elim_time_ms << "ms)"
                    << ", Self-subsume: " << f_opt_stats.removed_by_self_subsumption
                    << " (" << f_opt_stats.self_subsumption_time_ms << "ms)"
                    << ", Blocked: " << f_opt_stats.removed_blocked
                    << " (" << f_opt_stats.blocked_clause_time_ms << "ms)"
                    << std::endl;
            }
        } else {
            // No optimization, just record stats
            f_opt_stats.final_clauses = f_opt_stats.original_clauses;
        }
        
        // Always commit clauses to solver
        clock_t commit_start = clock();
        for (auto& clause : f_pending_clauses) {
            vec<Lit> ps;
            for (auto lit : clause) {
                ps.push(lit);
            }
            f_solver.addClause_(ps);
        }
        clock_t commit_time = clock() - commit_start;
        double commit_secs = (double)commit_time / CLOCKS_PER_SEC;

        auto pending_clauses {  f_pending_clauses.size() };
        TRACE
            << "Committed "
            << pending_clauses
            << " clauses to solver in " << commit_secs << " seconds"
            << std::endl;
        
        // Clear pending clauses
        f_pending_clauses.clear();
        f_optimization_in_progress = false;
    }
    
    void Engine::optimize_cnf()
    {
        // Run optimization passes in sequence with timing
        opts::OptsMgr& opts_mgr { opts::OptsMgr::INSTANCE() };
        clock_t start;
        
        if (opts_mgr.cnf_tautology_removal()) {
            start = clock();
            remove_tautologies();
            f_opt_stats.tautology_time_ms = ((double)(clock() - start) / CLOCKS_PER_SEC) * 1000;
        }
        
        if (opts_mgr.cnf_duplicate_removal()) {
            start = clock();
            remove_duplicates();
            f_opt_stats.duplicate_time_ms = ((double)(clock() - start) / CLOCKS_PER_SEC) * 1000;
        }
        
        if (opts_mgr.cnf_subsumption()) {
            start = clock();
            subsumption_elimination();
            f_opt_stats.subsumption_time_ms = ((double)(clock() - start) / CLOCKS_PER_SEC) * 1000;
        }
        
        if (opts_mgr.cnf_variable_elimination()) {
            start = clock();
            variable_elimination();
            f_opt_stats.var_elim_time_ms = ((double)(clock() - start) / CLOCKS_PER_SEC) * 1000;
        }
        
        if (opts_mgr.cnf_self_subsumption()) {
            start = clock();
            self_subsuming_resolution();
            f_opt_stats.self_subsumption_time_ms = ((double)(clock() - start) / CLOCKS_PER_SEC) * 1000;
        }
        
        if (opts_mgr.cnf_blocked_clause()) {
            start = clock();
            blocked_clause_elimination();
            f_opt_stats.blocked_clause_time_ms = ((double)(clock() - start) / CLOCKS_PER_SEC) * 1000;
        }
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
    
    void Engine::variable_elimination()
    {
        // Variable elimination by resolution
        // For each variable, if eliminating it reduces the clause count, do it
        
        // Count occurrences of each variable
        std::unordered_map<Var, std::vector<size_t>> positive_occurrences;
        std::unordered_map<Var, std::vector<size_t>> negative_occurrences;
        
        for (size_t i = 0; i < f_pending_clauses.size(); ++i) {
            for (auto lit : f_pending_clauses[i]) {
                Var var = Minisat::var(lit);
                if (Minisat::sign(lit)) {
                    negative_occurrences[var].push_back(i);
                } else {
                    positive_occurrences[var].push_back(i);
                }
            }
        }
        
        std::vector<bool> clause_removed(f_pending_clauses.size(), false);
        
        // Try to eliminate variables
        for (auto& [var, pos_clauses] : positive_occurrences) {
            auto neg_it = negative_occurrences.find(var);
            if (neg_it == negative_occurrences.end()) continue;
            
            const auto& neg_clauses = neg_it->second;
            
            // Skip if too many resolvents would be created
            if (pos_clauses.size() * neg_clauses.size() > pos_clauses.size() + neg_clauses.size() + 10) {
                continue;
            }
            
            // Check if all resolvents are tautologies or already exist
            bool can_eliminate = true;
            std::vector<std::vector<Lit>> new_clauses;
            
            for (size_t pos_idx : pos_clauses) {
                if (clause_removed[pos_idx]) continue;
                
                for (size_t neg_idx : neg_clauses) {
                    if (clause_removed[neg_idx]) continue;
                    
                    // Create resolvent
                    std::vector<Lit> resolvent;
                    
                    // Add literals from positive clause (except var)
                    for (auto lit : f_pending_clauses[pos_idx]) {
                        if (Minisat::var(lit) != var) {
                            resolvent.push_back(lit);
                        }
                    }
                    
                    // Add literals from negative clause (except ~var)
                    for (auto lit : f_pending_clauses[neg_idx]) {
                        if (Minisat::var(lit) != var) {
                            // Check if literal already exists (would create tautology)
                            bool found = false;
                            for (auto existing : resolvent) {
                                if (existing == lit) {
                                    found = true;
                                    break;
                                } else if (existing == ~lit) {
                                    // Tautology - skip this resolvent
                                    goto next_resolvent;
                                }
                            }
                            if (!found) {
                                resolvent.push_back(lit);
                            }
                        }
                    }
                    
                    new_clauses.push_back(std::move(resolvent));
                    next_resolvent:;
                }
            }
            
            // If elimination is beneficial, mark clauses for removal and add resolvents
            if (can_eliminate && new_clauses.size() < pos_clauses.size() + neg_clauses.size()) {
                for (size_t idx : pos_clauses) {
                    if (!clause_removed[idx]) {
                        clause_removed[idx] = true;
                        f_opt_stats.removed_by_var_elim++;
                    }
                }
                for (size_t idx : neg_clauses) {
                    if (!clause_removed[idx]) {
                        clause_removed[idx] = true;
                        f_opt_stats.removed_by_var_elim++;
                    }
                }
                
                // Add resolvents
                for (auto& clause : new_clauses) {
                    f_pending_clauses.push_back(std::move(clause));
                }
            }
        }
        
        // Remove eliminated clauses
        std::vector<std::vector<Lit>> result;
        result.reserve(f_pending_clauses.size());
        
        for (size_t i = 0; i < f_pending_clauses.size(); ++i) {
            if (!clause_removed[i]) {
                result.push_back(std::move(f_pending_clauses[i]));
            }
        }
        
        f_pending_clauses = std::move(result);
    }
    
    void Engine::self_subsuming_resolution()
    {
        // Self-subsuming resolution: if C ∨ l and C ∨ ¬l exist,
        // we can replace C ∨ l with C
        
        std::vector<bool> modified(f_pending_clauses.size(), false);
        
        for (size_t i = 0; i < f_pending_clauses.size(); ++i) {
            if (modified[i]) continue;
            
            for (size_t j = i + 1; j < f_pending_clauses.size(); ++j) {
                if (modified[j]) continue;
                
                // Check if clauses differ by exactly one literal
                const auto& clause1 = f_pending_clauses[i];
                const auto& clause2 = f_pending_clauses[j];
                
                if (std::abs((int)clause1.size() - (int)clause2.size()) > 1) continue;
                
                // Find the differing literal
                Lit diff_lit1 = mkLit(0);
                Lit diff_lit2 = mkLit(0);
                bool found_diff = false;
                
                size_t p1 = 0, p2 = 0;
                while (p1 < clause1.size() && p2 < clause2.size()) {
                    if (toInt(clause1[p1]) == toInt(clause2[p2])) {
                        p1++;
                        p2++;
                    } else if (toInt(clause1[p1]) < toInt(clause2[p2])) {
                        if (found_diff) goto next_pair;
                        diff_lit1 = clause1[p1];
                        found_diff = true;
                        p1++;
                    } else {
                        if (found_diff) goto next_pair;
                        diff_lit2 = clause2[p2];
                        found_diff = true;
                        p2++;
                    }
                }
                
                // Handle remaining literals
                if (p1 < clause1.size()) {
                    if (found_diff) goto next_pair;
                    diff_lit1 = clause1[p1];
                    found_diff = true;
                }
                if (p2 < clause2.size()) {
                    if (found_diff) goto next_pair;
                    diff_lit2 = clause2[p2];
                    found_diff = true;
                }
                
                // Check if we have complementary literals
                if (found_diff && diff_lit1 == ~diff_lit2) {
                    // Perform self-subsuming resolution
                    if (clause1.size() > clause2.size()) {
                        // Remove diff_lit1 from clause1
                        auto& clause = f_pending_clauses[i];
                        clause.erase(std::remove(clause.begin(), clause.end(), diff_lit1), clause.end());
                        modified[i] = true;
                        f_opt_stats.removed_by_self_subsumption++;
                    } else {
                        // Remove diff_lit2 from clause2
                        auto& clause = f_pending_clauses[j];
                        clause.erase(std::remove(clause.begin(), clause.end(), diff_lit2), clause.end());
                        modified[j] = true;
                        f_opt_stats.removed_by_self_subsumption++;
                    }
                }
                
                next_pair:;
            }
        }
    }
    
    void Engine::blocked_clause_elimination()
    {
        // Blocked clause elimination: A clause C is blocked if 
        // for some literal l in C, all resolutions on l produce tautologies
        
        std::vector<bool> blocked(f_pending_clauses.size(), false);
        
        // Build occurrence lists
        std::unordered_map<int, std::vector<size_t>> lit_to_clauses;
        for (size_t i = 0; i < f_pending_clauses.size(); ++i) {
            for (auto lit : f_pending_clauses[i]) {
                lit_to_clauses[toInt(lit)].push_back(i);
            }
        }
        
        // Check each clause
        for (size_t i = 0; i < f_pending_clauses.size(); ++i) {
            if (blocked[i]) continue;
            
            // Try each literal in the clause
            bool is_blocked = false;
            for (auto lit : f_pending_clauses[i]) {
                bool all_resolvents_tautological = true;
                
                // Get clauses containing ~lit
                auto neg_it = lit_to_clauses.find(toInt(~lit));
                if (neg_it == lit_to_clauses.end()) {
                    // No clauses with ~lit, so this literal makes the clause blocked
                    is_blocked = true;
                    break;
                }
                
                // Check all possible resolvents
                for (size_t j : neg_it->second) {
                    if (i == j || blocked[j]) continue;
                    
                    // Check if resolvent would be tautological
                    bool tautological = false;
                    for (auto lit1 : f_pending_clauses[i]) {
                        if (lit1 == lit) continue; // Skip the resolved literal
                        
                        for (auto lit2 : f_pending_clauses[j]) {
                            if (lit2 == ~lit) continue; // Skip the resolved literal
                            
                            if (lit1 == ~lit2) {
                                tautological = true;
                                goto next_resolvent;
                            }
                        }
                    }
                    
                    if (!tautological) {
                        all_resolvents_tautological = false;
                        break;
                    }
                    
                    next_resolvent:;
                }
                
                if (all_resolvents_tautological) {
                    is_blocked = true;
                    break;
                }
            }
            
            if (is_blocked) {
                blocked[i] = true;
                f_opt_stats.removed_blocked++;
            }
        }
        
        // Remove blocked clauses
        std::vector<std::vector<Lit>> result;
        result.reserve(f_pending_clauses.size());
        
        for (size_t i = 0; i < f_pending_clauses.size(); ++i) {
            if (!blocked[i]) {
                result.push_back(std::move(f_pending_clauses[i]));
            }
        }
        
        f_pending_clauses = std::move(result);
    }

}; // namespace sat

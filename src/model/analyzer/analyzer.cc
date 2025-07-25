/**
 * @file analyzer.cc
 * @brief Semantic analyzer module
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

#include <common/common.hh>

#include <compiler/compiler.hh>

#include <expr/expr_mgr.hh>

#include <expr/expr.hh>
#include <symb/proxy.hh>
#include <type/type.hh>

#include <sat/sat.hh>

#include <model/analyzer/analyzer.hh>
#include <model/module.hh>

#include <utils/misc.hh>

#include <opts/opts_mgr.hh>

#include <algorithm>
#include <atomic>
#include <future>
#include <mutex>
#include <sstream>
#include <thread>
#include <vector>

namespace model {

    Analyzer::Analyzer()
    {
        const void* instance { this };

        DRIVEL
            << "Created Analyzer @"
            << instance
            << std::endl;
    }

    Analyzer::~Analyzer()
    {
        const void* instance { this };

        DRIVEL
            << "Destroying Analyzer @"
            << instance
            << std::endl;
    }

    void Analyzer::process(expr::Expr_ptr expr, expr::Expr_ptr ctx, analyze_section_t section)
    {
        assert(section == ANALYZE_INIT ||
               section == ANALYZE_INVAR ||
               section == ANALYZE_TRANS ||
               section == ANALYZE_DEFINE);

        // this needs to be set only once
        f_section = section;

        // remove previous results
        f_expr_stack.clear();
        f_ctx_stack.clear();

        // walk body in given ctx
        f_ctx_stack.push_back(ctx);

        // invoke walker on the body of the expr to be processed
        (*this)(expr);
        assert(!f_expr_stack.size());
    }

    void Analyzer::generate_framing_conditions()
    {
	expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };
        ModelMgr& mm { ModelMgr::INSTANCE() };

        DEBUG
            << "Generating framing conditions ..."
            << std::endl;

        /* identifer -> list of guards */
        using ProcessingMap =
            boost::unordered_map<expr::Expr_ptr, expr::ExprVector,
                                 utils::PtrHash, utils::PtrEq>;

        ProcessingMap map;

        /* pass 1: build a scheleton map */
        for (DependencyTrackingMap::const_iterator i = f_dependency_tracking_map.begin();
             i != f_dependency_tracking_map.end(); ++i) {

            expr::Expr_ptr ident { i->second };
            ProcessingMap::const_iterator pmi { map.find(ident) };

            if (map.end() == pmi) {
                map.insert(
                    std::pair<expr::Expr_ptr, expr::ExprVector>(
			ident, expr::ExprVector())
		);
            }
        }

        /* pass 2: group together all guards associated with each var
         * identifier */
        for (DependencyTrackingMap::const_iterator i = f_dependency_tracking_map.begin();
             i != f_dependency_tracking_map.end(); ++i) {

            expr::Expr_ptr guard { i->first };
            expr::Expr_ptr ident { i->second };

            ProcessingMap::iterator pmi { map.find(ident) };

	    DEBUG
		<< "Tracking ... "
		<< guard
		<< " for "
		<< ident
		<< std::endl;

            /* right? */
            assert(map.end() != pmi);

            expr::ExprVector& ev { pmi->second };
            ev.push_back(guard);
        }

        /* pass 3: for each group of clauses, for each pair <p, q>, p
           and q must be mutually exclusive (i.e. `p ^ q` must be
           UNSAT). */
        
        // Check if we should skip mutual exclusiveness checks
        opts::OptsMgr& opts_mgr { opts::OptsMgr::INSTANCE() };
        if (opts_mgr.skip_inertial_fsm_checks()) {
            WARN
                << "Skipping mutual exclusiveness checks for inertial FSM conditions."
                << std::endl
                << "This may lead to incorrect model behavior if guards are not mutually exclusive."
                << std::endl;
        } else {
            // Structure to hold compiled data for checks
            struct CompiledCheck {
            expr::Expr_ptr ident;
            expr::Expr_ptr p;
            expr::Expr_ptr q;
            std::vector<compiler::Unit> invar_units; // Pre-compiled INVARs
            compiler::Unit p_unit;
            compiler::Unit q_unit;
        };
        
        // First, compile all expressions in a single thread
        std::vector<CompiledCheck> compiled_checks;
        
        DEBUG
            << "Pre-compiling expressions for mutual exclusivity checks..."
            << std::endl;
        
        // Compile expressions without INVARs for now
        compiler::Compiler compiler;
        expr::Expr_ptr ctx { em.make_empty() };
        
        // Skipping INVARs - just checking syntactic mutual exclusion
        std::vector<compiler::Unit> compiled_invars; // Empty vector
        
        // Collect and compile all check expressions
        for (ProcessingMap::iterator i = map.begin();
             i != map.end(); ++i) {

            expr::Expr_ptr ident { i->first };
            const expr::ExprVector& ev { i->second };

            auto input_length { ev.size() };
            if (2 <= input_length) {
                for (unsigned i = 0; i < input_length - 1; ++i) {
                    expr::Expr_ptr p { ev[i] };
                    compiler::Unit p_unit = compiler.process(ctx, p);

                    for (unsigned j = i + 1; j < input_length; ++j) {
                        expr::Expr_ptr q { ev[j] };
                        compiler::Unit q_unit = compiler.process(ctx, q);
                        
                        compiled_checks.push_back({
                            ident, p, q, 
                            compiled_invars, 
                            p_unit, q_unit
                        });
                    }
                }
            }
        }
        
        // Now perform SAT checks in parallel
        if (!compiled_checks.empty()) {
            // Determine number of threads
            unsigned int num_threads = std::thread::hardware_concurrency();
            if (num_threads == 0) num_threads = 1;
            
            // For small check counts, don't overdo parallelism
            num_threads = std::min(num_threads, static_cast<unsigned int>(compiled_checks.size()));
            
            size_t num_checks = compiled_checks.size();
            DEBUG
                << "Performing " << num_checks << " mutual exclusivity SAT checks "
                << "using " << num_threads << " threads"
                << std::endl;
            
            // Mutex for thread-safe error reporting
            std::mutex error_mutex;
            std::vector<std::string> errors;
            
            // Mutex for thread-safe trace output
            std::mutex trace_mutex;
            
            // Atomic counter for sequential progress tracking
            std::atomic<size_t> progress_counter{0};
            
            // Lambda for worker threads - now only does SAT solving
            auto worker = [&compiled_checks, &error_mutex, &errors, &trace_mutex, &progress_counter, num_checks](size_t start, size_t end) {
                for (size_t i = start; i < end; ++i) {
                    const auto& check = compiled_checks[i];
                    
                    // Increment counter atomically and get the sequential number
                    size_t check_number = progress_counter.fetch_add(1) + 1;
                    
                    {
                        std::lock_guard<std::mutex> lock(trace_mutex);
                        TRACE
                            << "Check " << check_number << " of " << num_checks
                            << ": Testing mutual exclusiveness of `"
                            << check.p
                            << "` and `"
                            << check.q
                            << "` for identifier `"
                            << check.ident
                            << "`"
                            << std::endl;
                    }
                    
                    // Create SAT engine for this check
                    sat::Engine engine { "Analyzer" };
                    
                    // Skip INVARs - checking syntactic mutual exclusion only
                    
                    // Add pre-compiled guards
                    engine.push(check.p_unit, 0);
                    engine.push(check.q_unit, 0);
                    
                    // Solve
                    sat::status_t status { engine.solve() };
                    
                    if (status != sat::status_t::STATUS_UNSAT) {
                        std::lock_guard<std::mutex> lock(error_mutex);
                        std::ostringstream oss;
                        oss << "Found two guards that could be NOT mutually "
                            << "exclusive for identifier `"
                            << check.ident
                            << "`: `"
                            << check.p
                            << "` and `"
                            << check.q
                            << "`";
                        errors.push_back(oss.str());
                    }
                }
            };
            
            // Launch async tasks
            std::vector<std::future<void>> futures;
            size_t checks_per_thread = compiled_checks.size() / num_threads;
            size_t remainder = compiled_checks.size() % num_threads;
            
            size_t start = 0;
            for (unsigned int i = 0; i < num_threads; ++i) {
                size_t count = checks_per_thread + (i < remainder ? 1 : 0);
                if (count > 0) {
                    futures.push_back(
                        std::async(std::launch::async, worker, start, start + count)
                    );
                    start += count;
                }
            }
            
            // Wait for all tasks to complete
            for (auto& future : futures) {
                future.wait();
            }
            
            // Report all errors
            for (const auto& error : errors) {
                ERR << error << std::endl;
            }
        }
        } // end of else block for skip_inertial_fsm_checks

        /* pass 4: for each expr vector, build the conjunction of all
           (mutually exclusive) negated guards and associate it to the
           variable identifier.  The resulting expr will be used as
           guard for a newly generated TRANS of the form: <guard> ->
           <var> := var. */
        Module& main { mm.model().main_module() };

        for (ProcessingMap::iterator i = map.begin();
             i != map.end(); ++i) {

            expr::Expr_ptr ident { i->first };
            expr::ExprVector& ev { i->second };

            expr::Expr_ptr guard { NULL };
            for (expr::ExprVector::const_iterator j = ev.begin();
                 j != ev.end(); ++j) {

                expr::Expr_ptr expr { *j };

                guard = (guard)
                            ? em.make_and(guard, em.make_not(expr))
                            : em.make_not(expr);
            }

            /* synthetic TRANS will be added to the module. */
            expr::Expr_ptr synth_trans {
                em.make_implies(guard,
                                  em.make_eq(em.make_next(ident),
                                               ident))
            };

            INFO
                << "Adding inertial INVAR: "
                << synth_trans
                << std::endl;

            main.add_trans(synth_trans);
        }
    }


}; // namespace model

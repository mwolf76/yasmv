/**
 * @file reach/reach.cc
 * @brief SAT-based REACHABILITY reachability algorithm.
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
#include <algorithm>

#include <algorithms/reach/reach.hh>
#include <algorithms/reach/witness.hh>

#include <expr/time/analyzer/analyzer.hh>
#include <expr/time/expander/expander.hh>

#include <compiler/compiler.hh>

#include <boost/thread.hpp>
#include <boost/thread/mutex.hpp>

namespace reach {

    Reachability::Reachability(cmd::Command& command, model::Model& model)
        : Algorithm(command, model)
    {
        const void* instance { this };
        TRACE
            << "Created Reachability @"
            << instance
            << std::endl;
    }

    Reachability::~Reachability()
    {
        const void* instance { this };
        TRACE
            << "Destroyed Reachability @"
            << instance
            << std::endl;
    }

    void Reachability::process(expr::Expr_ptr target, expr::ExprVector constraints)
    {
        auto& om { opts::OptsMgr::INSTANCE() };

        expr::time::Analyzer eta { em() };

        /* the target formula */
        f_target = target;
        assert(f_target);

        /* store and inspect constraints: currently mixed-time
         * (i.e. backward + forward) constraints are *not*
         * supported */
        f_constraints = constraints;
        unsigned no_forward_constraints { 0 };
        unsigned no_backward_constraints { 0 };
        unsigned no_global_constraints { 0 };

        for (auto i = f_constraints.begin(); i != f_constraints.end(); ++i) {
            auto constraint { *i };

            eta.process(constraint);
            if (eta.has_forward_time() && eta.has_backward_time()) {
                ERR
                    << "Mixed-time constraints currently not supported!"
                    << std::endl;

                f_status = REACHABILITY_ERROR;
                return;
            }

            if (eta.has_forward_time()) {
                ++no_forward_constraints;
            } else if (eta.has_backward_time()) {
                ++no_backward_constraints;
            } else {
                ++no_global_constraints;
            }
        }

        unsigned no_constraints {
            no_forward_constraints +
            no_backward_constraints +
            no_global_constraints
        };
        TRACE
            << no_constraints
            << " additional constraints were provided: "
            << no_forward_constraints
            << " forward, "
            << no_backward_constraints
            << " backward, "
            << no_global_constraints
            << " global."
            << std::endl;

        bool use_forward { !no_backward_constraints };
        bool use_backward { !no_forward_constraints };

        /* TODO: consider introducing support for this: a bit trickier, but doable */
        if (!use_forward && !use_backward) {
            ERR
                << "Mixing forward and backward guided reachability "
                << "constraints currently not supported."
                << std::endl;

            f_status = REACHABILITY_ERROR;
            return;
        }

        expr::Expr_ptr ctx { em().make_empty() };

        TRACE
            << "Compiling target `"
            << f_target
            << "` ..."
            << std::endl;

        /* strategy threads will access this value in the main thread's stack */
        compiler::Unit target_cu { compiler().process(ctx, f_target) };
        expr::time::Expander expander { em() };

        for (auto i = f_constraints.begin(); i != f_constraints.end(); ++i) {
            auto constraint { *i };

            TRACE
                << "Compiling constraint `"
                << constraint
                << "` ..."
                << std::endl;

            compiler::Unit cu {
                compiler().process(ctx, expander.process(constraint))
            };
            f_constraint_cus.insert(
                std::pair<expr::Expr_ptr, compiler::Unit>(constraint, cu));
        }

        /* fire up strategies */
        f_status = REACHABILITY_UNKNOWN;

        algorithms::thread_ptrs tasks;
        if (use_forward) {
            if (om.reach_fast_forward_strategy()) {
                TRACE
                    << "Fast-Forward strategy enabled"
                    << std::endl;

                tasks.push_back(new boost::thread(
                    &Reachability::fast_forward_strategy, this, target_cu));
            }

            if (om.reach_forward_strategy()) {
                TRACE
                    << "Forward strategy enabled"
                    << std::endl;

                tasks.push_back(new boost::thread(
                    &Reachability::forward_strategy, this, target_cu));
            }
        } else {
            TRACE
                << "Forward strategies unavailable"
                << std::endl;
        }

        if (use_backward) {
            if (om.reach_fast_backward_strategy()) {
                TRACE
                    << "Fast-Backward strategy enabled"
                    << std::endl;

                tasks.push_back(new boost::thread(
                    &Reachability::fast_backward_strategy, this, target_cu));
            }

            if (om.reach_backward_strategy()) {
                TRACE
                    << "Backward strategy enabled"
                    << std::endl;

                tasks.push_back(new boost::thread(
                &Reachability::backward_strategy, this, target_cu));
            }
        } else {
            TRACE
                << "Backward strategies unavailable"
                << std::endl;
        }

        /* join and destroy all active threads */
        assert(0 < tasks.size());
        std::for_each(
            begin(tasks), end(tasks),
            [](algorithms::thread_ptr task) {
                task->join();
                delete task;
            });
    }

    /* synchronized */
    reachability_status_t Reachability::sync_status()
    {
        boost::mutex::scoped_lock lock { f_status_mutex };
        return f_status;
    }

    /* synchronized */
    bool Reachability::sync_set_status(reachability_status_t status)
    {
        boost::mutex::scoped_lock lock { f_status_mutex };

        /* consistency check */
        assert(f_status == status ||
               (status != REACHABILITY_UNKNOWN && f_status == REACHABILITY_UNKNOWN));

        bool res { f_status != status };

        /* set status, extract witness if reachable */
        f_status = status;

        return res;
    }

} // namespace reach

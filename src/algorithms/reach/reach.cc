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

#include <boost/thread.hpp>
#include <boost/thread/mutex.hpp>

typedef boost::thread* thread_ptr;
typedef std::vector<thread_ptr> thread_ptrs;

Reachability::Reachability(Command& command, Model& model)
    : Algorithm(command, model)
    , f_target(NULL)
    , f_target_cu(NULL)
{
    const void* instance
        (this);

    setup();

    if (! ok())
        throw FailedSetup();

    DRIVEL
        << "Created Reachability @"
        << instance
        << std::endl ;
}

Reachability::~Reachability()
{
    const void *instance
        (this);

    DRIVEL
        << "Destroyed Reachability @"
        << instance
        << std::endl ;
}

void Reachability::process(Expr_ptr target, ExprVector constraints)
{
    f_target = target;
    assert(f_target);

    Expr_ptr ctx { em().make_empty() };

    try {
        unsigned nconstraints { 0 };
        unsigned positive_time{ 0 };
        unsigned negative_time{ 0 };
        unsigned globally_time{ 0 };

        std::for_each(begin(constraints),
                      end(constraints),
                      [this, ctx, &nconstraints, &positive_time, &negative_time, &globally_time](Expr_ptr expr) {
                          INFO
                              << "Compiling constraint `"
                              << expr
                              << "` ..."
                              << std::endl;

                          CompilationUnit unit
                              (compiler().process(ctx, expr));
                          ++ nconstraints;

                          if (unit.is_positive_time()) {
                              f_positive_time_constraints.push_back(unit);
                              ++ positive_time ;
                          } else if (unit.is_negative_time()) {
                              f_negative_time_constraints.push_back(unit);
                              ++ negative_time ;
                          } else {
                              f_globally_time_constraints.push_back(unit);
                              ++ globally_time ;
                          }
                      });

        INFO
            << nconstraints
            << " additional constraints found: "
            << positive_time
            << " positive time, "
            << negative_time
            << " negative time, "
            << globally_time
            << " globally valid."
            << std::endl;

        /* Guided reachability has currently limited support: forward
           strategies can be used for positive and globally valid
           constraints, backward strategies can be used for negative
           and globally valid constraints. In principle, it should be
           possible to introduce fully symmetric support for all
           constraints on both strategies, but this would require a
           significant amount of change to the compiler and other
           internals. */
        bool use_forward { ! negative_time };
        bool use_backward{ ! positive_time };
        if (!use_forward && !use_backward) {
            ERR
                << "Mixing positive- and negative- time constraints currently not supported."
                << std::endl;

            f_status = REACHABILITY_ERROR;
            return ;
        }

        INFO
            << "Compiling target `"
            << f_target
            << "` ..."
            << std::endl;

        CompilationUnit unit
            (compiler().process(ctx, f_target));

        f_target_cu = &unit;

        /* fire up strategies */
        f_status = REACHABILITY_UNKNOWN;

        thread_ptrs tasks;

        if (use_forward) {
            INFO
                << "Forward strategies enabled"
                << std::endl;
            boost::thread ffwd(&Reachability::fast_forward_strategy, this);
            tasks.push_back(&ffwd);

            boost::thread fwd(&Reachability::forward_strategy, this);
            tasks.push_back(&fwd);
        }

        if (use_backward) {
            INFO
                << "Forward strategies enabled"
                << std::endl;

            boost::thread fbwd(&Reachability::fast_backward_strategy, this);
            tasks.push_back(&fbwd);

            boost::thread bwd(&Reachability::backward_strategy, this);
            tasks.push_back(&bwd);
        }

        /* join all active threads */
        std::for_each(begin(tasks), end(tasks), [](thread_ptr task) { task->join(); });
    }

    catch (Exception& e) {
        std::cerr
            << e.what()
            << std::endl;

        f_status = REACHABILITY_ERROR;
    }
}

/* synchronized */
reachability_status_t Reachability::sync_status()
{
    boost::mutex::scoped_lock lock
        (f_status_mutex);

    return f_status;
}

/* synchronized */
bool Reachability::sync_set_status(reachability_status_t status)
{
    boost::mutex::scoped_lock lock
        (f_status_mutex);

    /* consistency check */
    assert(f_status == status ||
           (status != REACHABILITY_UNKNOWN && f_status == REACHABILITY_UNKNOWN));

    bool res
        (f_status != status);

    /* set status, extract witness if reachable */
    f_status = status;

    return res;
}

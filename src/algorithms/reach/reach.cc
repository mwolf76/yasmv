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

void Reachability::process(Expr_ptr target,
                           ExprVector forward_constraints,
                           ExprVector backward_constraints,
                           ExprVector global_constraints)
{
    f_target = target;
    assert(f_target);

    Expr_ptr ctx { em().make_empty() };

    try {
        /* compile forward constraints */
        unsigned no_forward_constraints { 0 };
        std::for_each(
            begin(forward_constraints), end(forward_constraints),
            [this, ctx, &no_forward_constraints](Expr_ptr expr) {
                INFO
                    << "Compiling constraint `"
                    << expr
                    << "` ..."
                    << std::endl;

                CompilationUnit unit
                    (compiler().process(ctx, expr));
                f_forward_constraint_cus.push_back(unit);
                ++ no_forward_constraints;
            });

        /* compile backward constraints */
        unsigned no_backward_constraints { 0 };
        std::for_each(
            begin(backward_constraints), end(backward_constraints),
            [this, ctx, &no_backward_constraints](Expr_ptr expr) {
                INFO
                    << "Compiling constraint `"
                    << expr
                    << "` ..."
                    << std::endl;

                CompilationUnit unit
                    (compiler().process(ctx, expr));
                f_backward_constraint_cus.push_back(unit);
                ++ no_backward_constraints;
            });

        /* compile global constraints */
        unsigned no_global_constraints { 0 };
        std::for_each(
            begin(global_constraints), end(global_constraints),
            [this, ctx, &no_global_constraints](Expr_ptr expr) {
                INFO
                    << "Compiling constraint `"
                    << expr
                    << "` ..."
                    << std::endl;

                CompilationUnit unit
                    (compiler().process(ctx, expr));
                f_global_constraint_cus.push_back(unit);
                ++ no_global_constraints;
            });

        unsigned no_constraints { no_forward_constraints + no_backward_constraints + no_global_constraints };
        INFO
            << no_constraints
            << " additional constraints were provided: "
            << no_forward_constraints
            << " forward, "
            << no_backward_constraints
            << " backward, "
            << no_global_constraints
            << " global."
            << std::endl;

        bool use_forward { ! no_backward_constraints };
        bool use_backward{ ! no_forward_constraints };
        if (!use_forward && !use_backward) {
            /* TODO: consider introducing support for this: a bit trickier, but doable */
            ERR
                << "Mixing forward and backward guided reachability constraints currently not supported."
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

            tasks.push_back(new boost::thread (&Reachability::fast_forward_strategy, this));
            tasks.push_back(new boost::thread (&Reachability::forward_strategy, this));
        }

        if (use_backward) {
            INFO
                << "Backward strategies enabled"
                << std::endl;

            tasks.push_back(new boost::thread (&Reachability::fast_backward_strategy, this));
            tasks.push_back(new boost::thread (&Reachability::backward_strategy, this));
        }

        /* join and destroy all active threads */
        std::for_each(
            begin(tasks), end(tasks),
            [](thread_ptr task) {
                task->join();
                delete task;
            });
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

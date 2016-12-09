/**
 * @file bmc/classes.hh
 * @brief SAT-based BMC reachability algorithm.
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

#include <algorithms/bmc/classes.hh>

#include <boost/thread.hpp>
#include <boost/thread/mutex.hpp>

BMC::BMC(Command& command, Model& model)
    : Algorithm(command, model)
    , f_goal(NULL)
{
    const void* instance
        (this);

    setup();

    if (! ok())
        throw FailedSetup();

    DRIVEL
        << "Created BMC @"
        << instance
        << std::endl ;
}

BMC::~BMC()
{
    const void *instance
        (this);

    DRIVEL
        << "Destroyed BMC @"
        << instance
        << std::endl ;
}

void BMC::process(const Expr_ptr goal)
{
    f_goal = goal;
    assert(f_goal);

    /* check everyting is ok before spawning */
    Expr_ptr ctx
        (em().make_empty());

    try {
        INFO
            << "Compiling formula `"
            << f_goal
            << "` ..."
            << std::endl;

        CompilationUnit unit
            (compiler().process(ctx, f_goal));

        f_status = BMC_UNKNOWN;

        /* fire up strategies */
        boost::thread fwd(&BMC::forward_strategy,
                          this, unit);
        boost::thread bwd(&BMC::backward_strategy,
                          this, unit);

        /* wait for termination */
        fwd.join();
        bwd.join();
    }

    catch (Exception& e) {
        std::cerr
            << e.what()
            << std::endl;

        f_status = BMC_ERROR;
    }
}

/* synchronized */
reachability_status_t BMC::sync_status()
{
    boost::mutex::scoped_lock lock
        (f_status_mutex);

    return f_status;
}

/* synchronized */
void BMC::sync_set_status(reachability_status_t status)
{
    boost::mutex::scoped_lock lock
        (f_status_mutex);

    /* consistency check */
    assert(f_status == status ||
           (status != BMC_UNKNOWN && f_status == BMC_UNKNOWN));

    /* set status, extract witness if reachable */
    f_status = status;
}
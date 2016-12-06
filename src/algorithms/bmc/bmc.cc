/**
 * @file bmc.cc
 * @brief SAT-based BMC reachability analysis algorithm implementation.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA
 *
 **/

#include <boost/thread.hpp>
#include <boost/thread/mutex.hpp>

#include <algorithms/bmc/bmc.hh>
#include <witness/witness_mgr.hh>

BMC::BMC(Command& command, Model& model)
    : Algorithm(command, model)
    , f_fwd_k(-1)
    , f_bwd_k(-1)
{
    const void* instance
        (this);

    setup();

    if (!ok())
        throw FailedSetup();

    DRIVEL
        << "Created BMC @"
        << instance
        << std::endl ;
}

BMC::~BMC()
{
    const void* instance(this);
    DRIVEL
        << "Destroyed BMC @"
        << instance
        << std::endl ;
}

void BMC::process(const Expr_ptr target)
{
    /* check everyting is ok before spawning */
    Expr_ptr ctx
        (em().make_empty());

    try {
        INFO
            << "Compiling formula `"
            << target
            << "` ..."
            << std::endl;

        CompilationUnit ii
            (compiler().process( ctx, target));

        CompilationUnit vv
            (compiler().process( ctx, em().make_not(target)));

        f_status = BMC_UNKNOWN;

        /* launch parallel checking strategies */

        /* violation-looking strategies */
        boost::thread fwd_violation(&BMC::forward_violation,
                                    this, target, vv, ii);
        boost::thread bwd_violation(&BMC::backward_violation,
                                    this, target, vv, ii);

        /* proof-looking strategies */
        boost::thread fwd_proof(&BMC::forward_proof,
                                this, target, vv, ii);
        boost::thread bwd_proof(&BMC::backward_proof,
                                this, target, vv, ii);

        /* join'em all */
        fwd_violation.join();
        bwd_violation.join();
        fwd_proof.join();
        bwd_proof.join();
    }

    catch (Exception& e) {
        const char* what
            (strdup(e.what()));

        std::cerr
            << what
            << std::endl;

        f_status = BMC_ERROR;
        return;
    }
}

reachability_status_t BMC::status()
{ return sync_status(); }

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

    f_status = status;
}

/* synchronized */
step_t BMC::sync_fwd_k()
{
    boost::mutex::scoped_lock lock
        (f_status_mutex);

    return f_fwd_k;
}

void BMC::sync_set_fwd_k(step_t k)
{
    boost::mutex::scoped_lock lock
        (f_status_mutex);

    /* consistency check */
    assert(k >= f_fwd_k);

    f_fwd_k = k;
}

step_t BMC::sync_bwd_k()
{
    boost::mutex::scoped_lock lock
        (f_status_mutex);

    return f_bwd_k;
}

void BMC::sync_set_bwd_k(step_t k)
{
    boost::mutex::scoped_lock lock
        (f_status_mutex);

    /* consistency check */
    assert(k >= f_bwd_k);

    f_bwd_k = k;
}


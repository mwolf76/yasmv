/**
 * @file bmc/forward.cc
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

// reserved for witnesses
static const char *reach_trace_prfx ("fwd_reach_");

void BMC::forward_violation(Expr_ptr target,
                            CompilationUnit& ii,
                            CompilationUnit& vv)
{
    Engine engine
        ("forward violation strategy");

    step_t k
        (0);

    /* unused */
    (void) ii;

    /* initial constraints */
    assert_fsm_init(engine, k);
    assert_fsm_invar(engine, k);

    do {
        /* looking for witness : BMC(k-1) ^ ! P(k) */
        assert_formula(engine, k, vv, engine.new_group());

        INFO
            << "Forward: now looking for reachability witness (k = " << k << ")..."
            << std::endl ;

        status_t status
            (engine.solve());

        if (STATUS_UNKNOWN == status)
            goto cleanup;

        else if (STATUS_UNSAT == status)
            INFO
                << "Forward: no reachability witness found (k = " << k << ")..."
                << std::endl ;

        else if (STATUS_SAT == status) {
            ExprMgr& em
                (ExprMgr::INSTANCE());

            WitnessMgr& wm
                (WitnessMgr::INSTANCE());

            sync_set_status(BMC_REACHABLE);

            INFO
                << "Forward: Reachability witness exists (k = " << k << "), target `"
                << target
                << "` is REACHABLE."
                << std::endl;

            Witness& w
                (* new BMCCounterExample(target, model(), engine, k));

            {
                std::ostringstream oss;
                oss
                    << reach_trace_prfx
                    << wm.sync_autoincrement();

                w.set_id(oss.str());
            }

            {
                std::ostringstream oss;

                oss
                    << "Reachability witness for target `"
                    << target
                    << "` in module `"
                    << model().main_module().name()
                    << "`" ;

                w.set_desc(oss.str());
            }

            wm.record(w);
            wm.set_current(w);
            set_witness(w);

            goto cleanup;
        }

        if (sync_status() == BMC_UNKNOWN) {

            /* let forward proof searching algorithm there is no k-long path
               leading to a violation from initial states. */
            sync_set_fwd_k(++ k);

            /* disable violation */
            engine.disable_last_group();

            /* unrolling */
            assert_fsm_trans(engine, k);
            assert_fsm_invar(engine, k);
        }
    } while (sync_status() == BMC_UNKNOWN);

 cleanup:
    /* signal other threads it's time to go home */
    EngineMgr::INSTANCE()
        .interrupt();

    INFO
        << engine
        << std::endl;
} /* forward_violation() */

void BMC::forward_proof(Expr_ptr target,
                        CompilationUnit& ii,
                        CompilationUnit& vv)
{
    Engine engine
        ("fwd proof");

    step_t k
        (0);

    assert_fsm_init(engine, 0);
    assert_fsm_invar(engine, 0);

    do {
        /* wait for green light from violation algorithm */
        while (sync_fwd_k() <= k)
            ;

        /* unrolling */
        assert_fsm_trans(engine, k ++);
        assert_fsm_invar(engine, k);

        /* looking for exploration proof: does a new unseen state
           exist?  assert uniqueness and test for unsatisfiability */
        INFO
            << "Forward: looking for unreachability proof (k = " << k << ")..."
            << std::endl
            ;

        /* build state uniqueness constraint for each pair of states
           (j, k), where j < k */
        for (step_t j = 0; j < k; ++ j)
            assert_fsm_uniqueness(engine, j, k);

        /* is this still relevant? */
        if (sync_status() != BMC_UNKNOWN)
            goto cleanup;

        status_t status
            (engine.solve());

        if (STATUS_UNKNOWN == status)
            goto cleanup;

        else if (STATUS_SAT == status)
            INFO
                << "Forward: no unreachability proof found (k = " << k << ")"
                << std::endl;

        else if (STATUS_UNSAT == status) {
            INFO
                << "Forward: found unreachability proof (k = " << k << ")"
                << std::endl;

            sync_set_status(BMC_UNREACHABLE);
            goto cleanup;
        }
        else assert(false); /* unreachable */
    } while (sync_status() == BMC_UNKNOWN);

cleanup:
    /* signal other threads it's time to go home */
    EngineMgr::INSTANCE()
        .interrupt();

    INFO
        << engine
        << std::endl;
} /* forward_proof() */

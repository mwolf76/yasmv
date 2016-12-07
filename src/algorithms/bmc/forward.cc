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

void BMC::forward_reachability(CompilationUnit& goal)
{
    Engine engine
        ("fwd reachability");

    step_t k
        (0);

    /* initial constraints */
    assert_fsm_init(engine, k);
    assert_fsm_invar(engine, k);

    do {
        /* looking for witness : BMC(k-1) ^ ! P(k) */
        assert_formula(engine, k, goal, engine.new_group());

        INFO
            << "Forward: now looking for reachability witness (k = " << k << ")..."
            << std::endl ;

        status_t status
            (engine.solve());

        if (STATUS_UNKNOWN == status)
            goto cleanup;

        else if (STATUS_SAT == status) {
            INFO
                << "Forward: Reachability witness exists (k = " << k << "), target `"
                << f_phi
                << "` is REACHABLE."
                << std::endl;

            sync_set_status(BMC_REACHABLE);

            /* Extract reachability witness */
            WitnessMgr& wm
                (WitnessMgr::INSTANCE());

            Witness& w
                (* new BMCCounterExample(f_phi, model(), engine, k));

            /* witness identifier */
            std::ostringstream oss_id;
            oss_id
                << reach_trace_prfx
                << wm.autoincrement();
            w.set_id(oss_id.str());

            /* witness description */
            std::ostringstream oss_desc;
            oss_desc
                << "Reachability witness for target `"
                << f_phi
                << "` in module `"
                << model().main_module().name()
                << "`" ;
            w.set_desc(oss_desc.str());

            wm.record(w);
            wm.set_current(w);
            set_witness(w);

            goto cleanup;
        }

        else if (STATUS_UNSAT == status) {
            INFO
                << "Forward: no reachability witness found (k = " << k << ")..."
                << std::endl ;

            /* let forward unreachability searching algorithm there is no k-long path
               leading to a reachability from initial states. */
            /* disable reachability */
            engine.disable_last_group();

            /* unrolling next and synchronizing with unreachability strategy */
            assert_fsm_trans(engine, k);
            sync_set_fwd_k(++ k);

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
} /* forward_reachability() */

void BMC::forward_unreachability()
{
    Engine engine
        ("fwd unreachability");

    step_t k
        (0);

    assert_fsm_init(engine, 0);
    assert_fsm_invar(engine, 0);

    do {
        /* busy wait for green light from reachability strategy */
        while (sync_status() == BMC_UNKNOWN && sync_fwd_k() <= k)
            ;

        /* unrolling next */
        assert_fsm_trans(engine, k);
        ++ k;

        assert_fsm_invar(engine, k);

        /* looking for exploration unreachability: does a new reachable not-yet-seen
           state exist? assert uniqueness and test for unsatisfiability */
        INFO
            << "Forward: looking for unreachability unreachability (k = " << k << ")..."
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

        else if (STATUS_UNSAT == status) {
            INFO
                << "Forward: found unreachability unreachability (k = " << k << ")"
                << std::endl;

            sync_set_status(BMC_UNREACHABLE);
            goto cleanup;
        }

        else if (STATUS_SAT == status)
            INFO
                << "Forward: no unreachability unreachability found (k = " << k << ")"
                << std::endl;

        else assert(false); /* unreachable */

    } while (sync_status() == BMC_UNKNOWN);

cleanup:
    /* signal other threads it's time to go home */
    EngineMgr::INSTANCE()
        .interrupt();

    INFO
        << engine
        << std::endl;
} /* forward_unreachability() */

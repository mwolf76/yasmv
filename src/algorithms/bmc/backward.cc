/**
 * @file bmc/backward.cc
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

#include <algorithms/bmc/bmc.hh>
#include <algorithms/bmc/witness.hh>

#include <boost/thread.hpp>
#include <boost/thread/mutex.hpp>

// reserved for witnesses
static const char *reach_trace_prfx ("reach_");

void BMC::backward_strategy(CompilationUnit& goal)
{
    Engine engine
        ("backward");

    step_t k
        (0);

    /* goal state constraints */
    assert_formula(engine, UINT_MAX - k, goal);
    assert_fsm_invar(engine, UINT_MAX - k);

    status_t status
        (engine.solve());

    if (STATUS_UNKNOWN == status)
        goto cleanup;

    else if (STATUS_UNSAT == status) {
        INFO
            << "Backward: empty final states. Target is trivially UNREACHABLE."
            << std::endl;

        sync_set_status(BMC_UNREACHABLE);
        goto cleanup;
    }

    else if (STATUS_SAT == status)
        INFO
            << "Backward: GOAL consistency check ok."
            << std::endl;

    else assert(false); /* unreachable */

    do {
        /* looking for witness : I(k-1) ^ BMC(k-1) ^ ... ^! P(0) */
        assert_fsm_init(engine, UINT_MAX - k, engine.new_group());

        INFO
            << "Backward: now looking for reachability witness (k = " << k << ")..."
            << std::endl ;

        status_t status
            (engine.solve());

        if (STATUS_UNKNOWN == status)
            goto cleanup;

        else if (STATUS_SAT == status) {

            if (sync_set_status(BMC_REACHABLE)) {

                /* Extract reachability witness */
                WitnessMgr& wm
                    (WitnessMgr::INSTANCE());

                Witness& w
                    (* new BMCCounterExample(f_goal, model(), engine, k, true)); /* reversed */

                /* witness identifier */
                std::ostringstream oss_id;
                oss_id
                    << reach_trace_prfx
                    << wm.autoincrement();
                w.set_id(oss_id.str());

                /* witness description */
                std::ostringstream oss_desc;
                oss_desc
                    << "Reversed reachability witness for target `"
                    << f_goal
                    << "` in module `"
                    << model().main_module().name()
                    << "`" ;
                w.set_desc(oss_desc.str());

                wm.record(w);
                wm.set_current(w);
                set_witness(w);

                goto cleanup;
            }
        }

        else if (STATUS_UNSAT == status) {
            INFO
                << "Backward: no reachability witness found (k = " << k << ")..."
                << std::endl ;

            engine.disable_last_group();

            /* unrolling next */
            ++ k;
            assert_fsm_trans(engine, UINT_MAX - k);
            assert_fsm_invar(engine, UINT_MAX - k);

            /* build state uniqueness constraint for each pair of states
               (j, k), where j < k */
            for (step_t j = 0; j < k; ++ j)
                assert_fsm_uniqueness(engine, UINT_MAX - j, UINT_MAX - k);

            /* is this still relevant? */
            if (sync_status() != BMC_UNKNOWN)
                goto cleanup;

            INFO
                << "Backward: now looking for unreachability proof (k = " << k << ")..."
                << std::endl ;

            status_t status
                (engine.solve());

            if (STATUS_UNKNOWN == status)
                goto cleanup;

            else if (STATUS_SAT == status)
                INFO
                    << "Backward: no unreachability proof found (k = " << k << ")"
                    << std::endl;

            else if (STATUS_UNSAT == status) {
                INFO
                    << "Backward: found unreachability proof (k = " << k << ")"
                    << std::endl;

                sync_set_status(BMC_UNREACHABLE);
                goto cleanup;
            }
            else assert(false); /* unreachable */
        }

        TRACE
            << "Backward: done with k = " << k << "..."
            << std::endl ;


    } while (sync_status() == BMC_UNKNOWN);

 cleanup:
    /* signal other threads it's time to go home */
    EngineMgr::INSTANCE()
        .interrupt();

    INFO
        << engine
        << std::endl;
} /* BMC::backward_strategy() */


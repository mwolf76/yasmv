/**
 * @file bmc/fast_forward.cc
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

#include <algorithm>

#include <algorithms/reach/reach.hh>
#include <algorithms/reach/witness.hh>

#include <boost/thread.hpp>
#include <boost/thread/mutex.hpp>

// reserved for witnesses
static const char *reach_trace_prfx ("reach_");

void BMC::fast_forward_strategy()
{
    Engine engine { "fast_forward" };
    step_t k  { 0 };

    /* initial constraints */
    assert_fsm_init(engine, k);
    assert_fsm_invar(engine, k);
    std::for_each(begin(f_constraint_cus),
                  end(f_constraint_cus),
                  [this, &engine, k](CompilationUnit& cu) {
                      this->assert_formula(engine, k, cu);
                  });

    status_t status
        (engine.solve());

    if (STATUS_UNKNOWN == status)
        goto cleanup;

    else if (STATUS_UNSAT == status) {
        INFO
            << "Fast_Forward: Empty initial states. Target is trivially UNREACHABLE."
            << std::endl;

        sync_set_status(BMC_UNREACHABLE);
        goto cleanup;
    }

    else if (STATUS_SAT == status)
        INFO
            << "Fast_Forward: INIT consistency check ok."
            << std::endl;

    else assert(false); /* unreachable */

    do {
        /* looking for witness : BMC(k-1) ^ ! P(k) */
        assert_formula(engine, k, *f_target_cu, engine.new_group());

        INFO
            << "Fast_Forward: now looking for reachability witness (k = " << k << ")..."
            << std::endl ;

        status_t status
            (engine.solve());

        if (STATUS_UNKNOWN == status)
            goto cleanup;

        else if (STATUS_SAT == status) {
            INFO
                << "Fast_Forward: Reachability witness exists (k = " << k << "), target `"
                << f_target
                << "` is REACHABLE."
                << std::endl;

            if (sync_set_status(BMC_REACHABLE)) {

                /* Extract reachability witness */
                WitnessMgr& wm
                    (WitnessMgr::INSTANCE());

                Witness& w
                    (* new BMCCounterExample(f_target, model(), engine, k));

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
                    << f_target
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
                << "Fast_Forward: no reachability witness found (k = " << k << ")..."
                << std::endl ;

            engine.invert_last_group();

            /* unrolling next */
            assert_fsm_trans(engine, k);
            ++ k;
            assert_fsm_invar(engine, k);
        }

        TRACE
            << "Fast_Forward: done with k = " << k << "..."
            << std::endl ;

    } while (sync_status() == BMC_UNKNOWN);

 cleanup:
    /* signal other threads it's time to go home */
    EngineMgr::INSTANCE()
        .interrupt();

    INFO
        << engine
        << std::endl;
} /* BMC::fast_forward_strategy() */


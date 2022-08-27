/**
 * @file bmc/fast_backward.cc
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

#include <algorithms/reach/reach.hh>
#include <algorithms/reach/witness.hh>

#include <expr/time/analyzer/analyzer.hh>

#include <boost/thread.hpp>
#include <boost/thread/mutex.hpp>

static const char* reach_trace_prfx { "reach_" };

namespace reach {
    void Reachability::fast_backward_strategy(compiler::Unit& target_cu)
    {
        witness::WitnessMgr& wm(witness::WitnessMgr::INSTANCE());

        sat::Engine engine { "fast_backward" };
        step_t k { 0 };

        /* goal state constraints */
        assert_formula(engine, UINT_MAX - k, target_cu);
        assert_fsm_invar(engine, UINT_MAX - k);

        /* Timed constraints can be asserted immediately, global
	 * constraints must be asserted at time zero, therefore we
	 * don't need any filtering here. */
        std::for_each(
            begin(f_constraints), end(f_constraints),
            [this, &engine, k](expr::Expr_ptr constraint) {
                auto i { f_constraint_cus.find(constraint) };
                assert(f_constraint_cus.end() != i);

                compiler::Unit cu { i->second };
                this->assert_formula(engine, UINT_MAX - k, cu);
            });

        sat::status_t status { engine.solve() };

        if (sat::status_t::STATUS_UNKNOWN == status)
            goto cleanup;

        else if (sat::status_t::STATUS_UNSAT == status) {
            INFO
                << "Empty final states. Target is trivially UNREACHABLE."
                << std::endl;

            sync_set_status(REACHABILITY_UNREACHABLE);
            goto cleanup;
        }

        else if (sat::status_t::STATUS_SAT == status)
            INFO
                << "GOAL consistency check ok."
                << std::endl;

        else
            assert(false); /* unreachable */

        do {
            /* looking for witness : I(k-1) ^ Reachability(k-1) ^ ... ^! P(0) */
            assert_fsm_init(engine, UINT_MAX - k, engine.new_group());

            INFO
                << "Now looking for reachability witness (k = " << k << ")..."
                << std::endl;

            sat::status_t status { engine.solve() };

            if (sat::status_t::STATUS_UNKNOWN == status)
                goto cleanup;

            else if (sat::status_t::STATUS_SAT == status) {
                if (sync_set_status(REACHABILITY_REACHABLE)) {

                    /* Extract reachability witness */
                    witness::Witness& w { *new ReachabilityCounterExample(f_target, model(), engine, k, true) }; /* reversed */

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
                        << "`";
                    w.set_desc(oss_desc.str());

                    wm.record(w);
                    wm.set_current(w);
                    set_witness(w);

                    goto cleanup;
                }
            }

            else if (sat::status_t::STATUS_UNSAT == status) {
                INFO
                    << "No reachability witness found (k = " << k << ")..."
                    << std::endl;

                engine.invert_last_group();

                /* unrolling next */
                ++k;
                assert_fsm_trans(engine, UINT_MAX - k);
                assert_fsm_invar(engine, UINT_MAX - k);

                /* Only global (i.e. untimed) constraints need be asserted here */
                std::for_each(
                    begin(f_constraints), end(f_constraints),
                    [this, &engine, k](expr::Expr_ptr constraint) {
                        expr::time::Analyzer eta { em() };
                        eta.process(constraint);

                        /* if forward time made it up to this point, something went wrong */
                        assert(!eta.has_forward_time());

                        if (!eta.has_backward_time()) {
                            auto i { f_constraint_cus.find(constraint) };
                            assert(f_constraint_cus.end() != i);

                            compiler::Unit cu { i->second };
                            this->assert_formula(engine, UINT_MAX - k, cu);
                        }
                    });
            }

            TRACE
                << "Done with k = " << k << "..."
                << std::endl;

        } while (sync_status() == REACHABILITY_UNKNOWN);

    cleanup:
        /* signal other threads it's time to go home */
        sat::EngineMgr::INSTANCE().interrupt();

        INFO
            << engine
            << std::endl;
    } /* Reachability::fast_backward_strategy() */

} // namespace reach

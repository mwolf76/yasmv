/**
 * @file diameter.cc
 * @brief SAT-based FSM diameter computing algorithm implementation.
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

#include <boost/thread.hpp>

#include <algorithms/fsm/fsm.hh>
#include <witness_mgr.hh>

namespace fsm {

    ComputeDiameter::ComputeDiameter(cmd::Command& command, model::Model& model)
        : algorithms::Algorithm { command, model }
        , f_diameter { UINT_MAX }
    {
        const void* instance { this };
        TRACE
            << "Created ComputeDiameter @"
            << instance
            << std::endl;
    }

    ComputeDiameter::~ComputeDiameter()
    {
        const void* instance { this };
        TRACE
            << "Destroyed ComputeDiameter @"
            << instance
            << std::endl;
    }

    void ComputeDiameter::process()
    {
        sat::Engine engine { "ComputeDiameter" };

        /* fire up strategies */
        algorithms::thread_ptrs tasks;
        tasks.push_back(new boost::thread(&ComputeDiameter::forward_strategy, this));
        tasks.push_back(new boost::thread(&ComputeDiameter::backward_strategy, this));

        /* join and destroy all active threads */
        assert(0 < tasks.size());
        std::for_each(
            begin(tasks), end(tasks),
            [](algorithms::thread_ptr task) {
                task->join();
                delete task;
            });
    }

    void ComputeDiameter::forward_strategy()
    {
        sat::Engine engine { "forward" };
        step_t k { 0 };

        /* initial constraints */
        assert_fsm_invar(engine, k);

        sat::status_t status { engine.solve() };
        if (sat::status_t::STATUS_UNKNOWN == status) {
            goto cleanup;
        } else if (sat::status_t::STATUS_UNSAT == status) {
            INFO
                << "Invariant deadlock detected. FSM has no valid states."
                << std::endl;

            goto cleanup;
        } else if (sat::status_t::STATUS_SAT == status) {
            INFO
                << "INVAR consistency check ok."
                << std::endl;
        } else {
            assert(false); /* unreachable */
        }

        do {
            /* unrolling next */
            assert_fsm_trans(engine, k++);
            assert_fsm_invar(engine, k);

            /* build state uniqueness constraint for each pair of states
               (j, k), where j < k */
            for (step_t j = 0; j < k; ++j) {
                assert_fsm_uniqueness(engine, j, k);
            }

            INFO
                << "Now looking for infeasibility proof (k = " << k << ") ..."
                << std::endl;

            sat::status_t status { engine.solve() };
            if (sat::status_t::STATUS_UNKNOWN == status) {
                goto cleanup;
            } else if (sat::status_t::STATUS_UNSAT == status) {
                INFO
                    << "Found infeasibility proof (k = " << k << ")"
                    << std::endl;

                sync_set_diameter(k - 1);
                goto cleanup;
            } else if (sat::status_t::STATUS_SAT == status) {
                INFO
                    << "No infeasibility proof found (k = " << k << ")"
                    << std::endl;
            } else {
                assert(false); /* unreachable */
            }

            TRACE
                << "Done with k = " << k << "..."
                << std::endl;
        } while (sync_diameter() == UINT_MAX);

    cleanup:
        /* signal other threads it's time to go home */
        sat::EngineMgr::INSTANCE().interrupt();

        INFO
            << engine
            << std::endl;
    } /* ComputeDiameter::forward_strategy */

    void ComputeDiameter::backward_strategy()
    {
        sat::Engine engine { "backward" };
        step_t k { 0 };

        assert_fsm_invar(engine, UINT_MAX - k);

        sat::status_t status { engine.solve() };
        if (sat::status_t::STATUS_UNKNOWN == status) {
            goto cleanup;
        } else if (sat::status_t::STATUS_UNSAT == status) {
            INFO
                << "Invariant deadlock detected. FSM has no valid states."
                << std::endl;

            goto cleanup;
        } else if (sat::status_t::STATUS_SAT == status) {
            INFO
                << "INVAR consistency check ok."
                << std::endl;
        } else {
            assert(false); /* unreachable */
        }

        do {
            /* unrolling next */
            ++k;
            assert_fsm_trans(engine, UINT_MAX - k);
            assert_fsm_invar(engine, UINT_MAX - k);

            /* build state uniqueness constraint for each pair of states
               (j, k), where j < k */
            for (step_t j = 0; j < k; ++j) {
                assert_fsm_uniqueness(engine, UINT_MAX - j, UINT_MAX - k);
            }

            INFO
                << "Now looking for infeasibility proof (k = " << k << ")..."
                << std::endl;

            sat::status_t status { engine.solve() };

            if (sat::status_t::STATUS_UNKNOWN == status) {
                goto cleanup;
            } else if (sat::status_t::STATUS_SAT == status) {
                INFO
                    << "No infeasibility proof found (k = " << k << ")"
                    << std::endl;
            } else if (sat::status_t::STATUS_UNSAT == status) {
                INFO
                    << "Found infeasibility proof (k = " << k << ")"
                    << std::endl;

                sync_set_diameter(k - 1);
                goto cleanup;
            } else {
                assert(false); /* unreachable */
            }

            TRACE
                << "Done with k = " << k << "..."
                << std::endl;

        } while (sync_diameter() == UINT_MAX);

    cleanup:
        /* signal other threads it's time to go home */
        sat::EngineMgr::INSTANCE().interrupt();

        INFO
            << engine
            << std::endl;
    } /* Reachability::backward_strategy() */

    /* synchronized */
    step_t ComputeDiameter::sync_diameter()
    {
        boost::mutex::scoped_lock lock { f_diameter_mutex };
        return f_diameter;
    }

    /* synchronized */
    bool ComputeDiameter::sync_set_diameter(step_t diameter)
    {
        boost::mutex::scoped_lock lock { f_diameter_mutex };

        /* consistency check */
        assert(f_diameter == diameter || f_diameter == UINT_MAX);

        bool res { f_diameter != UINT_MAX };
        f_diameter = diameter;

        return res;
    }

} // namespace fsm

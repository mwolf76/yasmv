/**
 * @file trans.cc
 * @brief SAT-based FSM TRANS consistency checking algorithm implementation.
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

#include <boost/thread.hpp>

#include <algorithms/fsm/fsm.hh>
#include <witness_mgr.hh>

namespace fsm {

    CheckTransConsistency::CheckTransConsistency(cmd::Command& command, model::Model& model)
        : algorithms::Algorithm(command, model)
        , f_limit(1)
    {
        const void* instance { this };
        TRACE
            << "Created CheckTransConsistency @"
            << instance
            << std::endl;

        f_status = FSM_CONSISTENCY_UNDECIDED;
    }

    CheckTransConsistency::~CheckTransConsistency()
    {
        const void* instance { this };
        TRACE
            << "Destroyed CheckTransConsistency @"
            << instance
            << std::endl;
    }

    void CheckTransConsistency::process(expr::ExprVector constraints)
    {
        sat::Engine engine { "Transitional" };
        expr::Expr_ptr ctx { em().make_empty() };

        unsigned no_constraints { 0 };
        std::for_each(
            begin(constraints),
            end(constraints),
            [this, ctx, &no_constraints](expr::Expr_ptr expr) {
                INFO
                    << "Compiling constraint `"
                    << expr
                    << "` ..."
                    << std::endl;

                const compiler::Unit unit { this->compiler().process(ctx, expr) };

                f_constraint_cus.push_back(unit);
                ++no_constraints;
            });

        INFO
            << no_constraints
            << " additional constraints found."
            << std::endl;

        // assert the invars and constraints at time zero separately
        assert_fsm_invar(engine, 0);
        std::for_each(
            begin(f_constraint_cus),
            end(f_constraint_cus),
            [this, &engine](compiler::Unit& cu) {
                this->assert_formula(engine, 0, cu);
            });

        for (size_t k = 0; k < f_limit; ++ k) {
            INFO
                << "Checking FSM transition relation consistency"
                << "@" << k << std::endl;

            assert_fsm_trans(engine, k);

            // assert the invars and constraints at time k + 1
            assert_fsm_invar(engine, k + 1);
            std::for_each(
            begin(f_constraint_cus),
            end(f_constraint_cus),
            [this, &engine, k](compiler::Unit& cu) {
                    this->assert_formula(engine, k+1, cu);
            });

            sat::status_t status { engine.solve() };

            if (sat::status_t::STATUS_UNSAT == status) {
                f_status = FSM_CONSISTENCY_KO;
                break;
            }
        }

        // if no failures were detected up to this point, result is SAT
        if (f_status == FSM_CONSISTENCY_UNDECIDED) {
            f_status = FSM_CONSISTENCY_OK;
        }
    }
} // namespace fsm

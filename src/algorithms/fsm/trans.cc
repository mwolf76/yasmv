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

CheckTransConsistency::CheckTransConsistency(Command& command, Model& model)
    : Algorithm(command, model)
{
    const void* instance(this);

    setup();
    DRIVEL
        << "Created CheckTransConsistency @"
        << instance
        << std::endl;

    f_status = FSM_CONSISTENCY_UNDECIDED;
}

CheckTransConsistency::~CheckTransConsistency()
{
    const void* instance(this);
    DRIVEL
        << "Destroyed CheckTransConsistency @"
        << instance
        << std::endl;
}

void CheckTransConsistency::process(expr::ExprVector constraints)
{
    Engine engine { "Transitional" };
    expr::Expr_ptr ctx { em().make_empty() };

    unsigned nconstraints { 0 };
    std::for_each(begin(constraints),
                  end(constraints),
                  [this, ctx, &nconstraints](expr::Expr_ptr expr) {
                      INFO
                          << "Compiling constraint `"
                          << expr
                          << "` ..."
                          << std::endl;

                      CompilationUnit unit
                          (compiler().process(ctx, expr));

                      f_constraint_cus.push_back(unit);
                      ++ nconstraints;
                  });

    INFO
        << nconstraints
        << " additional constraints found."
        << std::endl;

    /* FSM constraints */
    assert_fsm_trans(engine, 0);
    assert_fsm_invar(engine, 0);

    /* Additional constraints, times 0 and 1 */
    for (step_t time = 0; time < 2; ++ time) {
        std::for_each(begin(f_constraint_cus),
                      end(f_constraint_cus),
                      [this, &engine, time](CompilationUnit& cu) {
                          this->assert_formula(engine, time, cu);
                      });
    }

    status_t status
        (engine.solve());

    if (STATUS_UNKNOWN == status) {
        f_status = FSM_CONSISTENCY_UNDECIDED;
    }
    else if (STATUS_UNSAT == status) {
        f_status = FSM_CONSISTENCY_KO;
    }
    else if (STATUS_SAT == status) {
        f_status = FSM_CONSISTENCY_OK;
    }
}

};

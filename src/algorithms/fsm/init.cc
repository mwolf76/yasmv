/**
 * @file init.cc
 * @brief SAT-based FSM INIT consistency checking algorithm implementation.
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

CheckInitConsistency::CheckInitConsistency(cmd::Command& command, model::Model& model)
    : algorithms::Algorithm(command, model)
{
    const void* instance(this);

    setup();
    DRIVEL
        << "Created CheckInitConsistency @"
        << instance
        << std::endl;

    f_status = FSM_CONSISTENCY_UNDECIDED;
}

CheckInitConsistency::~CheckInitConsistency()
{
    const void* instance(this);
    DRIVEL
        << "Destroyed CheckInitConsistency @"
        << instance
        << std::endl;
}

void CheckInitConsistency::process(expr::ExprVector constraints)
{
    sat::Engine engine { "Initial" };
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

                      compiler::Unit unit
                          (compiler().process(ctx, expr));

                      f_constraint_cus.push_back(unit);
                      ++ nconstraints;
                  });

    INFO
        << nconstraints
        << " additional constraints found."
        << std::endl;

    /* FSM constraints */
    assert_fsm_init(engine, 0);
    assert_fsm_invar(engine, 0);

    /* Additional constraints */
    std::for_each(begin(f_constraint_cus),
                  end(f_constraint_cus),
                  [this, &engine](compiler::Unit& cu) {
                      this->assert_formula(engine, 0, cu);
                  });

    sat::status_t status
        (engine.solve());

    if (sat::status_t::STATUS_UNKNOWN == status) {
        f_status = FSM_CONSISTENCY_UNDECIDED;
    }
    else if (sat::status_t::STATUS_UNSAT == status) {
        f_status = FSM_CONSISTENCY_KO;
    }
    else if (sat::status_t::STATUS_SAT == status) {
        f_status = FSM_CONSISTENCY_OK;
    }
}

} // namespace fsm

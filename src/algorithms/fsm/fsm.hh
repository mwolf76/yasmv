/**
 * @file fsm.hh
 * @brief SAT-based FSM Algorithms for consistency checking
 *
 * This header file contains the declarations required to implement
 * the consistency checking of initial states and transition relation.
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

#ifndef FSM_ALGORITHM_H
#define FSM_ALGORITHM_H

#include <cmd/command.hh>

#include <expr/expr.hh>

#include <algorithms/base.hh>
#include <witness/witness.hh>

namespace fsm {

typedef enum {
    FSM_CONSISTENCY_OK,
    FSM_CONSISTENCY_KO,
    FSM_CONSISTENCY_UNDECIDED
} fsm_consistency_t;

class CheckInitConsistency : public Algorithm {

public:
    CheckInitConsistency(cmd::Command& command, model::Model& model);
    ~CheckInitConsistency();

    void process(expr::ExprVector constraints);

    inline fsm_consistency_t status() const
    { return f_status; }

    inline void set_status(fsm_consistency_t status)
    { f_status = status; }

private:
    expr::ExprVector f_constraints;
    model::CompilationUnits f_constraint_cus;

    boost::mutex f_status_mutex;
    fsm_consistency_t f_status;
};

class CheckTransConsistency : public Algorithm {

public:
    CheckTransConsistency(cmd::Command& command, model::Model& model);
    ~CheckTransConsistency();

    void process(expr::ExprVector constraints);

    inline fsm_consistency_t status() const
    { return f_status; }

    inline void set_status(fsm_consistency_t status)
    { f_status = status; }

private:
    expr::ExprVector f_constraints;
    model::CompilationUnits f_constraint_cus;

    boost::mutex f_status_mutex;
    fsm_consistency_t f_status;
};

};

#endif /* FSM_ALGORITHM_H */

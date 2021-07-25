/**
 * @file reach/reach.hh
 * @brief SAT-based BMC reachability algorithm.
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

#ifndef REACHABILITY_ALGORITHM_H
#define REACHABILITY_ALGORITHM_H

#include <algorithms/base.hh>
#include <algorithms/reach/typedefs.hh>

class Reachability : public Algorithm {

public:
    Reachability(Command& command, Model& model);
    ~Reachability();

    void process(Expr_ptr target, ExprVector forward_constraints, ExprVector backward_constraints, ExprVector global_constraints);

    inline reachability_status_t status()
    { return sync_status(); }

    reachability_status_t sync_status();
    bool sync_set_status(reachability_status_t status);

private:
    Expr_ptr f_target;
    CompilationUnit_ptr f_target_cu;

    ExprVector f_constraints;

    CompilationUnits f_forward_constraint_cus; /* requires forward strategy */
    CompilationUnits f_backward_constraint_cus; /* requires backward strategy */
    CompilationUnits f_global_constraint_cus;

    boost::mutex f_status_mutex;
    reachability_status_t f_status;

    /* strategies */
    void forward_strategy();
    void backward_strategy();

    void fast_forward_strategy();
    void fast_backward_strategy();
};

#endif /* Reachability_ALGORITHM_CLASSES_H */

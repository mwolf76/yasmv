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

#include <cmd/command.hh>

#include <compiler/typedefs.hh>

namespace reach {

    class Reachability : public algorithms::Algorithm {

    public:
        Reachability(cmd::Command& command, model::Model& model);
        ~Reachability() override;

        void process(expr::Expr_ptr target, expr::ExprVector constraints);

        reachability_status_t status()
        {
            return sync_status();
        }

        reachability_status_t sync_status();
        bool sync_set_status(reachability_status_t status);

    private:
        expr::Expr_ptr f_target;

        expr::ExprVector f_constraints;

        using ConstraintCompilationMap =
            boost::unordered_map<expr::Expr_ptr, compiler::Unit,
                                 utils::PtrHash, utils::PtrEq>;
        ConstraintCompilationMap f_constraint_cus;

        boost::mutex f_status_mutex;
        reachability_status_t f_status;

        /* checking strategies */
        void forward_strategy(compiler::Unit& target_cu);
        void backward_strategy(compiler::Unit& target_cu);

        void fast_forward_strategy(compiler::Unit& target_cu);
        void fast_backward_strategy(compiler::Unit& target_cu);
    };

} // namespace reach

#endif /* REACHABILITY_ALGORITHM_H */

/**
 * @file internals.cc
 * @brief Semantic analyzer, internals implementation.
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

#include <common/common.hh>

#include <expr/expr.hh>
#include <symb/proxy.hh>
#include <type/type.hh>

#include <model/analyzer/analyzer.hh>
#include <model/model_mgr.hh>

namespace model {

    void Analyzer::pre_hook()
    {}
    void Analyzer::post_hook()
    {}

    void Analyzer::pre_node_hook(expr::Expr_ptr expr)
    {
        f_expr_stack.push_back(expr);
    }
    void Analyzer::post_node_hook(expr::Expr_ptr expr)
    {
        f_expr_stack.pop_back();
    }

    bool Analyzer::is_valid_guarded_action(expr::Expr_ptr expr) const
    {
        const expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };
        
        if (!expr || !expr->rhs()) {
            return false;
        }

        const expr::Expr_ptr rhs = expr->rhs();
        
        // Check if RHS is a single assignment
        if (em.is_assignment(rhs)) {
            return true;
        }
        
        // Check if RHS is a comma-separated list of assignments
        // NOTE: in the context of guarded actions, a comma operator
        // NOTE: is silently transformed into an `and` operator.
        if (em.is_and(rhs)) {
            // Traverse the comma-separated list
            expr::Expr_ptr current = rhs;
            while (em.is_and(current)) {
                if (!em.is_assignment(current->lhs())) {
                    return false;
                }
                current = current->rhs();
            }
            return em.is_assignment(current);
        }
        
        return false;
    }
    
    void Analyzer::track_dependency(const expr::Expr_ptr expr)
    {
        const expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };
        
        if (!expr || !expr->lhs() || !expr->rhs()) {
            return;
        }
        
        expr::Expr_ptr guard = expr->lhs();

        // Handle single assignment
        if (const expr::Expr_ptr action = expr->rhs(); em.is_assignment(action)) {
            f_dependency_tracking_map.insert(std::make_pair(guard, action->lhs()));
        } else if (em.is_and(action)) {
            expr::Expr_ptr current = action;
            while (em.is_and(current)) {
                if (const expr::Expr_ptr inner_action { current->lhs() }; em.is_assignment(inner_action)) {
                    f_dependency_tracking_map.insert(
                        std::make_pair(guard, inner_action->lhs())
                    );
                }
                current = current->rhs();
            }
            // Process the last element
            if (em.is_assignment(current)) {
                f_dependency_tracking_map.insert(std::make_pair(guard, current->lhs()));
            }
        }
    }
}; // namespace model

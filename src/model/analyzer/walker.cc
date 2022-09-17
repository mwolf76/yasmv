/**
 * @file analyzer/walker.cc
 * @brief Semantic analyzer module, walker pattern implementation.
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

#include <compiler/compiler.hh>

#include <expr/expr.hh>
#include <type/type.hh>

#include <symb/classes.hh>
#include <symb/proxy.hh>

#include <model/analyzer/analyzer.hh>
#include <sat/sat.hh>


#include <utils/misc.hh>

namespace model {

    bool Analyzer::walk_F_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_F_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_G_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_G_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_X_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_X_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_U_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_U_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_U_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_R_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_R_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_R_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_at_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_at_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_at_postorder(const expr::Expr_ptr expr)
    {}

    /* INTERVAL needs rewriting */
    bool Analyzer::walk_interval_preorder(const expr::Expr_ptr expr)
    {
        assert(false);
        return false;
    }
    bool Analyzer::walk_interval_inorder(const expr::Expr_ptr expr)
    {
        assert(false);
        return false;
    }
    void Analyzer::walk_interval_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_next_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_next_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_neg_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_neg_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_not_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_not_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_bw_not_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_bw_not_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_add_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_add_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_add_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_sub_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_sub_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_sub_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_div_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_div_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_div_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_mul_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_mul_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_mul_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_mod_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_mod_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_mod_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_and_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_and_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_and_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_bw_and_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_bw_and_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_bw_and_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_or_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_or_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_or_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_bw_or_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_bw_or_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_bw_or_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_bw_xor_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_bw_xor_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_bw_xor_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_bw_xnor_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_bw_xnor_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_bw_xnor_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_guard_preorder(const expr::Expr_ptr expr)
    {
	expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };

        if (f_section == ANALYZE_INIT) {
            throw SemanticError("Guards not allowed in INITs");
        }

        if (f_section == ANALYZE_INVAR) {
            throw SemanticError("Guards not allowed in INVARs");
        }

        if (f_section == ANALYZE_DEFINE) {
            throw SemanticError("Guards not allowed in DEFINEs");
        }

        /* now we know it's a TRANS */
        if (1 != f_expr_stack.size()) {
            throw SemanticError("Guards are only allowed toplevel in TRANSes");
        }

        expr::Expr_ptr guard { expr->lhs() };
        expr::Expr_ptr action { expr->rhs() };

        if (! em.is_assignment(action)) {
            throw SemanticError("Guarded actions must be assignments");
        }

        expr::Expr_ptr lhs { action->lhs() };

        INFO
            << "Tracking dependency: "
            << lhs
            << " -> "
            << guard
            << std::endl;

        f_dependency_tracking_map.insert(
            std::pair<expr::Expr_ptr, expr::Expr_ptr>
	    (guard, lhs));

        return true;
    }

    bool Analyzer::walk_guard_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_guard_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_implies_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_implies_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_implies_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_cast_preorder(const expr::Expr_ptr expr)
    {
	return false;
    }
    bool Analyzer::walk_cast_inorder(const expr::Expr_ptr expr)
    {
	assert(false); /* unreachable */
        return false;
    }
    void Analyzer::walk_cast_postorder(const expr::Expr_ptr expr)
    {
	assert(false); /* unreachable */
    }

    bool Analyzer::walk_type_preorder(const expr::Expr_ptr expr)
    {
        return false;
    }
    bool Analyzer::walk_type_inorder(const expr::Expr_ptr expr)
    {
        assert(false); /* unreachable */
        return false;
    }
    void Analyzer::walk_type_postorder(const expr::Expr_ptr expr)
    {
        assert(false); /* unreachable */
    }

    bool Analyzer::walk_lshift_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_lshift_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_lshift_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_rshift_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_rshift_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_rshift_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_assignment_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_assignment_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_assignment_postorder(const expr::Expr_ptr expr)
    {
	expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };

        if (f_section == ANALYZE_INIT) {
            throw SemanticError("Assignments not allowed in INITs");
        }

        if (f_section == ANALYZE_INVAR) {
            throw SemanticError("Assignments not allowed in INVARs");
        }

        if (f_section == ANALYZE_DEFINE) {
            throw SemanticError("Assignments not allowed in DEFINEs");
        }

        expr::Expr_ptr lhs { expr->lhs() };

        if (!em.is_lvalue(lhs)) {
            throw SemanticError("Assignments require an lvalue for lhs");
        }

        /* strip [] */
        if (em.is_subscript(lhs)) {
            lhs = lhs->lhs();
        }

        /* assignment lhs *must* be an ordinary state variable */
        expr::Expr_ptr ctx { f_ctx_stack.back() };
        expr::Expr_ptr full { em.make_dot(ctx, lhs) };

        symb::ResolverProxy resolver;

        symb::Symbol_ptr symb { resolver.symbol(full) };

        if (symb->is_variable()) {
            const symb::Variable& var { symb->as_variable() };

            /* INPUT vars are in fact bodyless, typed DEFINEs */
            if (var.is_input()) {
                throw SemanticError("Assignments not allowed on input vars.");
            }

            /* FROZEN vars can not be assigned */
            if (var.is_frozen()) {
                throw SemanticError("Assignments can not be used on frozen vars.");
            }

            /* assignments can only be used on INERTIAL vars */
            if (!var.is_inertial()) {
                throw SemanticError("Assignments can only be used on inertial vars.");
            }
        }

        else if (symb->is_define()) {
            symb::Define& define { symb->as_define() };
            expr::Expr_ptr body { define.body() };

            /* recur in body */
            (*this)(body);
        }
    }

    bool Analyzer::walk_eq_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_eq_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_eq_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_ne_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_ne_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_ne_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_gt_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_gt_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_gt_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_ge_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_ge_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_ge_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_lt_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_lt_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_lt_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_le_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_le_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_le_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_ite_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_ite_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_ite_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_cond_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_cond_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_cond_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_dot_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_dot_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_dot_postorder(const expr::Expr_ptr expr)
    {}

    /* on-demand preprocessing to expand defines delegated to Preprocessor */
    bool Analyzer::walk_params_preorder(const expr::Expr_ptr expr)
    {
        expr::Expr_ptr ctx { f_ctx_stack.back() };
        expr::Expr_ptr preprocessed {
            f_preprocessor.process(expr, ctx)
        };

        (*this)(preprocessed);

        return false;
    }
    bool Analyzer::walk_params_inorder(const expr::Expr_ptr expr)
    {
        assert(false);
        return false; /* unreachable */
    }
    void Analyzer::walk_params_postorder(const expr::Expr_ptr expr)
    {
        assert(false);
        return; /* unreachable */
    }

    bool Analyzer::walk_params_comma_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_params_comma_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_params_comma_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_subscript_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool Analyzer::walk_subscript_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_subscript_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_array_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_array_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_array_comma_preorder(expr::Expr_ptr expr)
    {
        return true;
    }

    bool Analyzer::walk_array_comma_inorder(expr::Expr_ptr expr)
    {
        return true;
    }

    void Analyzer::walk_array_comma_postorder(expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_set_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Analyzer::walk_set_postorder(const expr::Expr_ptr expr)
    {}

    bool Analyzer::walk_set_comma_preorder(expr::Expr_ptr expr)
    {
        return true;
    }

    bool Analyzer::walk_set_comma_inorder(expr::Expr_ptr expr)
    {
        return true;
    }

    void Analyzer::walk_set_comma_postorder(expr::Expr_ptr expr)
    {}

    void Analyzer::walk_instant(const expr::Expr_ptr expr)
    {}

    void Analyzer::walk_leaf(const expr::Expr_ptr expr)
    {
	expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };

	if (em.is_identifier(expr)) {
            expr::Expr_ptr ctx { f_ctx_stack.back() };
            expr::Expr_ptr full { em.make_dot(ctx, expr) };

            symb::ResolverProxy resolver;
            symb::Symbol_ptr symb { resolver.symbol(full) };

            if (symb->is_variable()) {
                const symb::Variable& var { symb->as_variable() };

                /* Sanity checks on var modifiers */
                if (var.is_input() && var.is_inertial()) {
                    throw SemanticError(
                        "@input and @inertial not simultaneously allowed on the same var.");
                }

                if (var.is_input() && var.is_frozen()) {
                    throw SemanticError(
                        "@input and @frozen not simultaneously allowed on the same var.");
                }

                if (var.is_inertial() && var.is_frozen()) {
                    throw SemanticError(
                        "@inertial and @frozen not simultaneously allowed on the same var.");
                }
            }

	    else if (symb->is_define()) {
                symb::Define& define { symb->as_define() };
                expr::Expr_ptr body { define.body() };

                /* recur in body */
                (*this)(body);
            }
        }
    }

}; // namespace model

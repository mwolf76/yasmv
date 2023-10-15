/**
 * @file expander.cc
 * @brief Expr time expander class implementation
 *
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
#include <expr/expr_mgr.hh>

#include <expr/time/expander/expander.hh>

#include <common/logging.hh>

namespace expr::time {

    Expander::Expander(ExprMgr& em)
        : f_em(em)
    {
        const void* instance { this };
        DRIVEL
            << "Initialized Expr Expander @"
            << instance
            << std::endl;
    }

    Expander::~Expander()
    {
        const void* instance { this };
        DRIVEL
            << "Destroyed Expr Expander @"
            << instance
            << std::endl;
    }

    void Expander::pre_hook()
    {}

    void Expander::post_hook()
    {}

    Expr_ptr Expander::process(Expr_ptr expr)
    {
        f_expr_stack.clear();
        this->operator()(expr);

        TOP_EXPR(res);
        return res;
    }

    // TODO: a lot of internal_errors could actually be normally supported
    bool Expander::walk_F_preorder(const Expr_ptr expr)
    {
        return internal_error(expr);
    }
    void Expander::walk_F_postorder(const Expr_ptr expr)
    {}

    bool Expander::walk_G_preorder(const Expr_ptr expr)
    {
        return internal_error(expr);
    }
    void Expander::walk_G_postorder(const Expr_ptr expr)
    {}

    bool Expander::walk_X_preorder(const Expr_ptr expr)
    {
        return internal_error(expr);
    }
    void Expander::walk_X_postorder(const Expr_ptr expr)
    {}

    bool Expander::walk_U_preorder(const Expr_ptr expr)
    {
        return internal_error(expr);
    }
    bool Expander::walk_U_inorder(const Expr_ptr expr)
    {
        return false;
    }
    void Expander::walk_U_postorder(const Expr_ptr expr)
    {}

    bool Expander::walk_R_preorder(const Expr_ptr expr)
    {
        return internal_error(expr);
    }
    bool Expander::walk_R_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_R_postorder(const Expr_ptr expr)
    {}

    bool Expander::walk_at_preorder(const Expr_ptr expr)
    {
        Expr_ptr lhs { expr->lhs() };
        assert(f_em.is_instant(lhs) ||
               f_em.is_interval(lhs));

        Expr_ptr rhs { expr->rhs() };
        assert(NULL != rhs);

        return true;
    }
    bool Expander::walk_at_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_at_postorder(const Expr_ptr expr)
    {
        POP_EXPR(rhs);
        POP_EXPR(lhs);

        if (f_em.is_instant(lhs)) {
            Expr_ptr at_expr { f_em.make_at(lhs, rhs) };
            PUSH_EXPR(at_expr);
        } else {
            assert(f_em.is_interval(lhs));

            Expr_ptr a { lhs->lhs() };
            assert(f_em.is_instant(a));

            Expr_ptr b { lhs->rhs() };
            assert(f_em.is_instant(b));

            step_t va { (step_t) a->value() };
            step_t vb { (step_t) b->value() };

            step_t begin { va <= vb ? va : vb };
            step_t end { vb <= va ? va : vb };

            Expr_ptr res { NULL };
            for (step_t k = begin; k <= end; ++k) {
                Expr_ptr fragment = f_em.make_at(f_em.make_instant(k), rhs);
                res = (NULL == res)
                          ? fragment
                          : f_em.make_and(res, fragment);
            }

            PUSH_EXPR(res);
        }
    }

    /* rewrite the interval into an instant */
    bool Expander::walk_interval_preorder(const Expr_ptr expr)
    {
        Expr_ptr lhs { expr->lhs() };
        assert(f_em.is_instant(lhs));

        Expr_ptr rhs { expr->rhs() };
        assert(f_em.is_instant(rhs));

        return true;
    }
    bool Expander::walk_interval_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_interval_postorder(const Expr_ptr expr)
    {
        POP_EXPR(rhs);
        POP_EXPR(lhs);

        Expr_ptr interval { f_em.make_interval(lhs, rhs) };
        PUSH_EXPR(interval);
    }

    bool Expander::walk_next_preorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_next_postorder(const Expr_ptr expr)
    {
        POP_EXPR(lhs);

        Expr_ptr next { f_em.make_next(lhs) };
        PUSH_EXPR(next);
    }

    bool Expander::walk_neg_preorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_neg_postorder(const Expr_ptr expr)
    {
        POP_EXPR(lhs);
        Expr_ptr neg { f_em.make_neg(lhs) };
        PUSH_EXPR(neg);
    }

    bool Expander::walk_not_preorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_not_postorder(const Expr_ptr expr)
    {
        POP_EXPR(lhs);

        Expr_ptr not_expr { f_em.make_not(lhs) };
        PUSH_EXPR(not_expr);
    }

    bool Expander::walk_bw_not_preorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_bw_not_postorder(const Expr_ptr expr)
    {
        POP_EXPR(lhs);

        Expr_ptr res { f_em.make_bw_not(lhs) };
        PUSH_EXPR(res);
    }

    bool Expander::walk_add_preorder(const Expr_ptr expr)
    {
        return true;
    }
    bool Expander::walk_add_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_add_postorder(const Expr_ptr expr)
    {
        POP_EXPR(rhs);
        POP_EXPR(lhs);

        Expr_ptr res { f_em.make_add(lhs, rhs) };
        PUSH_EXPR(res);
    }

    bool Expander::walk_sub_preorder(const Expr_ptr expr)
    {
        return true;
    }
    bool Expander::walk_sub_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_sub_postorder(const Expr_ptr expr)
    {
        POP_EXPR(rhs);
        POP_EXPR(lhs);

        Expr_ptr res { f_em.make_sub(lhs, rhs) };
        PUSH_EXPR(res);
    }

    bool Expander::walk_div_preorder(const Expr_ptr expr)
    {
        return true;
    }
    bool Expander::walk_div_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_div_postorder(const Expr_ptr expr)
    {
        POP_EXPR(rhs);
        POP_EXPR(lhs);

        Expr_ptr res { f_em.make_div(lhs, rhs) };
        PUSH_EXPR(res);
    }

    bool Expander::walk_mul_preorder(const Expr_ptr expr)
    {
        return true;
    }
    bool Expander::walk_mul_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_mul_postorder(const Expr_ptr expr)
    {
        POP_EXPR(rhs);
        POP_EXPR(lhs);

        Expr_ptr res { f_em.make_mul(lhs, rhs) };
        PUSH_EXPR(res);
    }

    bool Expander::walk_mod_preorder(const Expr_ptr expr)
    {
        return true;
    }
    bool Expander::walk_mod_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_mod_postorder(const Expr_ptr expr)
    {
        POP_EXPR(rhs);
        POP_EXPR(lhs);

        Expr_ptr res { f_em.make_mod(lhs, rhs) };
        PUSH_EXPR(res);
    }

    bool Expander::walk_and_preorder(const Expr_ptr expr)
    {
        return true;
    }
    bool Expander::walk_and_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_and_postorder(const Expr_ptr expr)
    {
        POP_EXPR(rhs);
        POP_EXPR(lhs);

        Expr_ptr res { f_em.make_and(lhs, rhs) };
        PUSH_EXPR(res);
    }

    bool Expander::walk_bw_and_preorder(const Expr_ptr expr)
    {
        return true;
    }
    bool Expander::walk_bw_and_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_bw_and_postorder(const Expr_ptr expr)
    {
        POP_EXPR(rhs);
        POP_EXPR(lhs);

        Expr_ptr res { f_em.make_bw_and(lhs, rhs) };
        PUSH_EXPR(res);
    }

    bool Expander::walk_or_preorder(const Expr_ptr expr)
    {
        return true;
    }
    bool Expander::walk_or_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_or_postorder(const Expr_ptr expr)
    {
        POP_EXPR(rhs);
        POP_EXPR(lhs);

        Expr_ptr res { f_em.make_or(lhs, rhs) };
        PUSH_EXPR(res);
    }

    bool Expander::walk_bw_or_preorder(const Expr_ptr expr)
    {
        return true;
    }
    bool Expander::walk_bw_or_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_bw_or_postorder(const Expr_ptr expr)
    {
        POP_EXPR(rhs);
        POP_EXPR(lhs);

        Expr_ptr res { f_em.make_bw_or(lhs, rhs) };
        PUSH_EXPR(res);
    }

    bool Expander::walk_bw_xor_preorder(const Expr_ptr expr)
    {
        return true;
    }
    bool Expander::walk_bw_xor_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_bw_xor_postorder(const Expr_ptr expr)
    {
        POP_EXPR(rhs);
        POP_EXPR(lhs);

        Expr_ptr res { f_em.make_bw_xor(lhs, rhs) };
        PUSH_EXPR(res);
    }

    bool Expander::walk_bw_xnor_preorder(const Expr_ptr expr)
    {
        return true;
    }
    bool Expander::walk_bw_xnor_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_bw_xnor_postorder(const Expr_ptr expr)
    {
        POP_EXPR(rhs);
        POP_EXPR(lhs);

        Expr_ptr res { f_em.make_bw_xnor(lhs, rhs) };
        PUSH_EXPR(res);
    }

    bool Expander::walk_guard_preorder(const Expr_ptr expr)
    {
        return internal_error(expr);
    }
    bool Expander::walk_guard_inorder(const Expr_ptr expr)
    {
        return false;
    }
    void Expander::walk_guard_postorder(const Expr_ptr expr)
    {}

    bool Expander::walk_implies_preorder(const Expr_ptr expr)
    {
        return true;
    }
    bool Expander::walk_implies_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_implies_postorder(const Expr_ptr expr)
    {
        POP_EXPR(rhs);
        POP_EXPR(lhs);

        Expr_ptr res { f_em.make_implies(lhs, rhs) };
        PUSH_EXPR(res);
    }

    bool Expander::walk_cast_preorder(const Expr_ptr expr)
    {
        return internal_error(expr);
    }
    bool Expander::walk_cast_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_cast_postorder(const Expr_ptr expr)
    {}

    bool Expander::walk_type_preorder(const Expr_ptr expr)
    {
        return internal_error(expr);
    }
    bool Expander::walk_type_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_type_postorder(const Expr_ptr expr)
    {}

    bool Expander::walk_lshift_preorder(const Expr_ptr expr)
    {
        return true;
    }
    bool Expander::walk_lshift_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_lshift_postorder(const Expr_ptr expr)
    {
        POP_EXPR(rhs);
        POP_EXPR(lhs);

        Expr_ptr res { f_em.make_lshift(lhs, rhs) };
        PUSH_EXPR(res);
    }

    bool Expander::walk_rshift_preorder(const Expr_ptr expr)
    {
        return true;
    }
    bool Expander::walk_rshift_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_rshift_postorder(const Expr_ptr expr)
    {
        POP_EXPR(rhs);
        POP_EXPR(lhs);

        Expr_ptr res { f_em.make_rshift(lhs, rhs) };
        PUSH_EXPR(res);
    }

    bool Expander::walk_assignment_preorder(const Expr_ptr expr)
    {
        return internal_error(expr);
    }
    bool Expander::walk_assignment_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_assignment_postorder(const Expr_ptr expr)
    {}

    bool Expander::walk_eq_preorder(const Expr_ptr expr)
    {
        return true;
    }
    bool Expander::walk_eq_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_eq_postorder(const Expr_ptr expr)
    {
        POP_EXPR(rhs);
        POP_EXPR(lhs);

        Expr_ptr res { f_em.make_eq(lhs, rhs) };
        PUSH_EXPR(res);
    }

    bool Expander::walk_ne_preorder(const Expr_ptr expr)
    {
        return true;
    }
    bool Expander::walk_ne_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_ne_postorder(const Expr_ptr expr)
    {
        POP_EXPR(rhs);
        POP_EXPR(lhs);

        Expr_ptr res { f_em.make_ne(lhs, rhs) };
        PUSH_EXPR(res);
    }

    bool Expander::walk_gt_preorder(const Expr_ptr expr)
    {
        return true;
    }
    bool Expander::walk_gt_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_gt_postorder(const Expr_ptr expr)
    {
        POP_EXPR(rhs);
        POP_EXPR(lhs);

        Expr_ptr res { f_em.make_gt(lhs, rhs) };
        PUSH_EXPR(res);
    }

    bool Expander::walk_ge_preorder(const Expr_ptr expr)
    {
        return true;
    }
    bool Expander::walk_ge_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_ge_postorder(const Expr_ptr expr)
    {
        POP_EXPR(rhs);
        POP_EXPR(lhs);

        Expr_ptr res { f_em.make_ge(lhs, rhs) };
        PUSH_EXPR(res);
    }

    bool Expander::walk_lt_preorder(const Expr_ptr expr)
    {
        return true;
    }
    bool Expander::walk_lt_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_lt_postorder(const Expr_ptr expr)
    {
        POP_EXPR(rhs);
        POP_EXPR(lhs);

        Expr_ptr res { f_em.make_lt(lhs, rhs) };
        PUSH_EXPR(res);
    }

    bool Expander::walk_le_preorder(const Expr_ptr expr)
    {
        return true;
    }
    bool Expander::walk_le_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_le_postorder(const Expr_ptr expr)
    {
        POP_EXPR(rhs);
        POP_EXPR(lhs);

        Expr_ptr res { f_em.make_le(lhs, rhs) };
        PUSH_EXPR(res);
    }

    bool Expander::walk_ite_preorder(const Expr_ptr expr)
    {
        return true;
    }
    bool Expander::walk_ite_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_ite_postorder(const Expr_ptr expr)
    {
        POP_EXPR(rhs);
        POP_EXPR(lhs);
        POP_EXPR(cond);

        Expr_ptr res {
            f_em.make_ite(
                f_em.make_cond(cond, lhs),
                rhs)
        };
        PUSH_EXPR(res);
    }

    bool Expander::walk_cond_preorder(const Expr_ptr expr)
    {
        return true;
    }
    bool Expander::walk_cond_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_cond_postorder(const Expr_ptr expr)
    {}

    bool Expander::walk_dot_preorder(const Expr_ptr expr)
    {
        return internal_error(expr);
    }
    bool Expander::walk_dot_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_dot_postorder(const Expr_ptr expr)
    {}

    bool Expander::walk_params_preorder(const Expr_ptr expr)
    {
        return internal_error(expr);
    }
    bool Expander::walk_params_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_params_postorder(const Expr_ptr expr)
    {}

    bool Expander::walk_params_comma_preorder(const Expr_ptr expr)
    {
        return internal_error(expr);
    }
    bool Expander::walk_params_comma_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_params_comma_postorder(const Expr_ptr expr)
    {}

    bool Expander::walk_subscript_preorder(const Expr_ptr expr)
    {
        return internal_error(expr);
    }
    bool Expander::walk_subscript_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_subscript_postorder(const Expr_ptr expr)
    {}

    bool Expander::walk_array_preorder(const Expr_ptr expr)
    {
        return internal_error(expr);
    }
    void Expander::walk_array_postorder(const Expr_ptr expr)
    {}

    bool Expander::walk_array_comma_preorder(const Expr_ptr expr)
    {
        return internal_error(expr);
    }
    bool Expander::walk_array_comma_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_array_comma_postorder(const Expr_ptr expr)
    {}

    bool Expander::walk_set_preorder(const Expr_ptr expr)
    {
        return internal_error(expr);
    }
    void Expander::walk_set_postorder(const Expr_ptr expr)
    {}

    bool Expander::walk_set_comma_preorder(const Expr_ptr expr)
    {
        return internal_error(expr);
    }
    bool Expander::walk_set_comma_inorder(const Expr_ptr expr)
    {
        return true;
    }
    void Expander::walk_set_comma_postorder(const Expr_ptr expr)
    {}

    void Expander::walk_instant(const Expr_ptr expr)
    {
        PUSH_EXPR(expr);
    }

    void Expander::walk_leaf(const Expr_ptr expr)
    {
        PUSH_EXPR(expr);
    }

    bool Expander::internal_error(const Expr_ptr expr)
    {
        ERR
            << "Expression `"
            << expr
            << "` was not supposed to be reached."
            << std::endl;

        throw InternalError("Time resolution aborted");
        return false;
    }

} // namespace expr::time

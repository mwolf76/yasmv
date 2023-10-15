/**
 * @file type_checker.cc
 * @brief Type checking subsystem, Type checker class implementation.
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
#include <type/type.hh>

#include <symb/classes.hh>
#include <symb/proxy.hh>

#include <model/type_checker/type_checker.hh>

#include <utils/logging.hh>

namespace model {

    TypeChecker::TypeChecker(ModelMgr& owner)
        : f_map()
        , f_type_stack()
        , f_ctx_stack()
        , f_owner(owner)
    {
        const void* instance { this };

        DRIVEL
            << "Created TypeChecker @"
            << instance
            << std::endl;
    }

    TypeChecker::~TypeChecker()
    {
        const void* instance { this };

        DRIVEL
            << "Destroying TypeChecker @"
            << instance
            << std::endl;
    }

    /* this function is not memoized by design, for a memoized wrapper use type() */
    type::Type_ptr TypeChecker::process(expr::Expr_ptr expr, expr::Expr_ptr ctx)
    {
        // remove previous results
        f_type_stack.clear();
        f_ctx_stack.clear();

        // walk body in given ctx
        f_ctx_stack.push_back(ctx);

        // invoke walker on the body of the expr to be processed
        (*this)(expr);

        if (1 != f_type_stack.size()) {
            throw expr::InternalError("TypeChecker::process post-condition checks failed");
        }

        POP_TYPE(res);
        assert(NULL != res);

        return res;
    }

    bool TypeChecker::walk_F_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    void TypeChecker::walk_F_postorder(const expr::Expr_ptr expr)
    {
        walk_unary_ltl_postorder(expr);
    }

    bool TypeChecker::walk_G_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    void TypeChecker::walk_G_postorder(const expr::Expr_ptr expr)
    {
        walk_unary_ltl_postorder(expr);
    }

    bool TypeChecker::walk_X_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    void TypeChecker::walk_X_postorder(const expr::Expr_ptr expr)
    {
        walk_unary_ltl_postorder(expr);
    }

    bool TypeChecker::walk_U_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_U_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_U_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_ltl_postorder(expr);
    }

    bool TypeChecker::walk_R_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_R_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_R_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_ltl_postorder(expr);
    }

    bool TypeChecker::walk_at_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_at_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_at_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_timed_postorder(expr);
    }

    bool TypeChecker::walk_interval_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_interval_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_interval_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_timed_postorder(expr);
    }

    bool TypeChecker::walk_next_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    void TypeChecker::walk_next_postorder(const expr::Expr_ptr expr)
    {
        walk_unary_fsm_postorder(expr);
    }

    bool TypeChecker::walk_neg_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    void TypeChecker::walk_neg_postorder(const expr::Expr_ptr expr)
    {
        walk_unary_arithmetical_postorder(expr);
    }

    bool TypeChecker::walk_not_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    void TypeChecker::walk_not_postorder(const expr::Expr_ptr expr)
    {
        walk_unary_logical_postorder(expr);
    }

    bool TypeChecker::walk_bw_not_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    void TypeChecker::walk_bw_not_postorder(const expr::Expr_ptr expr)
    {
        walk_unary_arithmetical_postorder(expr);
    }

    bool TypeChecker::walk_add_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_add_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_add_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_arithmetical_postorder(expr);
    }

    bool TypeChecker::walk_sub_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_sub_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_sub_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_arithmetical_postorder(expr);
    }

    bool TypeChecker::walk_div_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_div_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_div_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_arithmetical_postorder(expr);
    }

    bool TypeChecker::walk_mul_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_mul_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_mul_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_arithmetical_postorder(expr);
    }

    bool TypeChecker::walk_mod_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_mod_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_mod_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_arithmetical_postorder(expr);
    }

    bool TypeChecker::walk_and_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_and_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_and_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_logical_postorder(expr);
    }

    bool TypeChecker::walk_bw_and_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_bw_and_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_bw_and_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_arithmetical_postorder(expr);
    }

    bool TypeChecker::walk_or_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_or_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_or_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_logical_postorder(expr);
    }

    bool TypeChecker::walk_bw_or_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_bw_or_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_bw_or_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_arithmetical_postorder(expr);
    }

    bool TypeChecker::walk_bw_xor_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_bw_xor_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_bw_xor_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_arithmetical_postorder(expr);
    }

    bool TypeChecker::walk_bw_xnor_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_bw_xnor_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_bw_xnor_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_arithmetical_postorder(expr);
    }

    bool TypeChecker::walk_guard_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_guard_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_guard_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_logical_postorder(expr);
    }

    bool TypeChecker::walk_implies_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_implies_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_implies_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_logical_postorder(expr);
    }

    bool TypeChecker::walk_cast_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_cast_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_cast_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_cast_postorder(expr);
    }

    bool TypeChecker::walk_type_preorder(const expr::Expr_ptr expr)
    {
        type::TypeMgr& tm { type::TypeMgr::INSTANCE() };
        PUSH_TYPE(tm.find_type_by_def(expr));

        /* no need to process further */
        return false;
    }
    bool TypeChecker::walk_type_inorder(const expr::Expr_ptr expr)
    {
        assert(false); /* unreachable */
        return false;
    }
    void TypeChecker::walk_type_postorder(const expr::Expr_ptr expr)
    {
        assert(false); /* unreachable */
    }

    bool TypeChecker::walk_lshift_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_lshift_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_lshift_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_shift_postorder(expr);
    }

    bool TypeChecker::walk_rshift_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_rshift_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_rshift_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_shift_postorder(expr);
    }

    bool TypeChecker::walk_assignment_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_assignment_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_assignment_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_equality_postorder(expr);
    }

    bool TypeChecker::walk_eq_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_eq_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_eq_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_equality_postorder(expr);
    }

    bool TypeChecker::walk_ne_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_ne_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_ne_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_equality_postorder(expr);
    }

    bool TypeChecker::walk_gt_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_gt_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_gt_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_relational_postorder(expr);
    }

    bool TypeChecker::walk_ge_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_ge_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_ge_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_relational_postorder(expr);
    }

    bool TypeChecker::walk_lt_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_lt_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_lt_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_relational_postorder(expr);
    }

    bool TypeChecker::walk_le_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_le_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_le_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_relational_postorder(expr);
    }

    bool TypeChecker::walk_ite_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_ite_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_ite_postorder(const expr::Expr_ptr expr)
    {
        walk_binary_ite_postorder(expr);
    }

    bool TypeChecker::walk_cond_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_cond_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_cond_postorder(const expr::Expr_ptr expr)
    {
        POP_TYPE(lhs_type);
        POP_TYPE(cnd);
        if (!cnd->is_boolean()) {
            throw type::BadType(expr->lhs()->lhs(), cnd);
        }

        PUSH_TYPE(lhs_type);
    }

    bool TypeChecker::walk_dot_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_dot_inorder(const expr::Expr_ptr expr)
    {
        expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };
        expr::Expr_ptr ctx { em.make_dot(f_ctx_stack.back(), expr->lhs()) };

        f_ctx_stack.push_back(ctx);
        f_type_stack.pop_back();

        return true;
    }
    void TypeChecker::walk_dot_postorder(const expr::Expr_ptr expr)
    {
        f_ctx_stack.pop_back();
    }

    /* on-demand preprocessing to expand defines delegated to Preprocessor */
    bool TypeChecker::walk_params_preorder(const expr::Expr_ptr expr)
    {
        expr::Expr_ptr ctx { f_ctx_stack.back() };
        expr::Expr_ptr preprocessed { f_preprocessor.process(expr, ctx) };

        (*this)(preprocessed);
        return false;
    }
    bool TypeChecker::walk_params_inorder(const expr::Expr_ptr expr)
    {
        assert(false);
        return false; /* unreachable */
    }
    void TypeChecker::walk_params_postorder(const expr::Expr_ptr expr)
    {
        assert(false);
        return; /* unreachable */
    }

    bool TypeChecker::walk_params_comma_preorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    bool TypeChecker::walk_params_comma_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_params_comma_postorder(const expr::Expr_ptr expr)
    {}

    bool TypeChecker::walk_subscript_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool TypeChecker::walk_subscript_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void TypeChecker::walk_subscript_postorder(const expr::Expr_ptr expr)
    {
        POP_TYPE(index);
        if (!index->is_algebraic()) {
            throw type::BadType(expr->rhs(), index);
        }

        /* return wrapped type */
        PUSH_TYPE(check_array(expr->lhs())
                      ->as_array()
                      ->of());
    }

    bool TypeChecker::walk_array_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    void TypeChecker::walk_array_postorder(const expr::Expr_ptr expr)
    {
        /* Here we need to handle the singleton corner case
         * (e.g. [42]). We can do it here because nested arrays are
         * not supported. */
        type::TypeMgr& tm { type::TypeMgr::INSTANCE() };

        /* inspect head... */
        POP_TYPE(type);

        /* is it already an array type? */
        if (type->is_array()) {
            PUSH_TYPE(type);
            return;
        }

        type::ScalarType_ptr scalar_type { type->as_scalar() };

        /* build a singleton array type */
        type::ArrayType_ptr new_array_type {
            tm.find_array_type(scalar_type, 1)
        };

        PUSH_TYPE(new_array_type);
        return;
    }

    bool TypeChecker::walk_array_comma_preorder(expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }

    bool TypeChecker::walk_array_comma_inorder(expr::Expr_ptr expr)
    {
        return true;
    }

    void TypeChecker::walk_array_comma_postorder(expr::Expr_ptr expr)
    {
        type::TypeMgr& tm { type::TypeMgr::INSTANCE() };

        POP_TYPE(rhs_type);
        POP_TYPE(lhs_type);

        type::ArrayType_ptr array_type { NULL };

        if (rhs_type->is_array()) {
            array_type = rhs_type->as_array();
            type::ScalarType_ptr of_type { array_type->of() };

            assert(lhs_type->is_scalar() &&
                   lhs_type->width() == of_type->width());

            type::ArrayType_ptr new_array_type {
                tm.find_array_type(of_type, 1 + array_type->nelems())
            };

            PUSH_TYPE(new_array_type);
            return;
        }

        if (rhs_type->is_scalar()) {
            type::ScalarType_ptr of_type { rhs_type->as_scalar() };

            assert(lhs_type->is_scalar() &&
                   lhs_type->width() == of_type->width());

            array_type = tm.find_array_type(of_type, 2);
            PUSH_TYPE(array_type);
        }
    }

    bool TypeChecker::walk_set_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    void TypeChecker::walk_set_postorder(const expr::Expr_ptr expr)
    {}

    bool TypeChecker::walk_set_comma_preorder(expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }

    bool TypeChecker::walk_set_comma_inorder(expr::Expr_ptr expr)
    {
        return true;
    }

    void TypeChecker::walk_set_comma_postorder(expr::Expr_ptr expr)
    {
        POP_TYPE(rhs);
        POP_TYPE(lhs);

        if (lhs != rhs) {
            throw type::TypeMismatch(expr, lhs, rhs);
        }

        PUSH_TYPE(lhs);
    }

    void TypeChecker::walk_instant(const expr::Expr_ptr expr)
    {
        type::TypeMgr& tm { type::TypeMgr::INSTANCE() };
        PUSH_TYPE(tm.find_time());
    }


    void TypeChecker::walk_leaf(const expr::Expr_ptr expr)
    {
        type::TypeMgr& tm { type::TypeMgr::INSTANCE() };
        expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };

        // cache miss took care of the stack already
        if (!cache_miss(expr)) {
            return;
        }

        // is an integer const ..
        if (em.is_int_const(expr)) {
            unsigned ww { opts::OptsMgr::INSTANCE().word_width() };
            PUSH_TYPE(tm.find_constant(ww));
            return;
        }

        // .. or a symbol
        if (em.is_identifier(expr)) {
            expr::Expr_ptr ctx { f_ctx_stack.back() };

            symb::ResolverProxy proxy;
            symb::Symbol_ptr symb { proxy.symbol(em.make_dot(ctx, expr)) };

            if (symb->is_const()) {
                type::Type_ptr res { symb->as_const().type() };
                PUSH_TYPE(res);
                return;
            } else if (symb->is_literal()) {
                type::Type_ptr res { symb->as_literal().type() };
                PUSH_TYPE(res);
                return;
            } else if (symb->is_variable()) {
                type::Type_ptr res { symb->as_variable().type() };
                PUSH_TYPE(res);
                return;
            } else if (symb->is_parameter()) {
                type::Type_ptr res { symb->as_parameter().type() };
                PUSH_TYPE(res);
                return;
            }

            /* DEFINE, we can safely recur into its body. */
            else if (symb->is_define()) {
                symb::Define& define { symb->as_define() };
                expr::Expr_ptr body { define.body() };

                DEBUG
                    << "Recurring in `"
                    << body
                    << "`"
                    << std::endl;

                (*this)(body);
                return;
            }
        }

        assert(false); // unexpected
    }

}; // namespace model

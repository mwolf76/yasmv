/**
 * @file evaluator.cc
 * @brief Expressions evaluator class implementation.
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

#include <utils/ctx.hh>

#include <witness/evaluator.hh>
#include <witness/exceptions.hh>
#include <witness/witness_mgr.hh>

namespace witness {

    Evaluator::Evaluator(WitnessMgr& owner)
        : f_owner(owner)
    {
        const void* instance { this };
        DRIVEL
            << "Created Evaluator @"
            << instance
            << std::endl;
    }

    Evaluator::~Evaluator()
    {
        const void* instance { this };
        DRIVEL
            << "Destroying Evaluator @"
            << instance
            << std::endl;
    }

    void Evaluator::clear_internals()
    {
        f_type_stack.clear();
        f_values_stack.clear();
        f_ctx_stack.clear();
        f_time_stack.clear();
        f_te2v_map.clear();
    }

    expr::Expr_ptr Evaluator::process(Witness_ptr witness,
                                      expr::Expr_ptr ctx,
                                      expr::Expr_ptr body,
                                      step_t time)
    {
        expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };

        clear_internals();

        // setting the environment(if applicable)
        f_witness = witness;

        // walk body in given ctx
        f_ctx_stack.push_back(ctx);

        // toplevel (time is assumed at 0, arbitrarily nested next allowed)
        f_time_stack.push_back(time);

        /* Invoke walker on the body of the expr to be processed */
        (*this)(body);

        // sanity conditions, relaxed for arrays
        assert(0 < f_values_stack.size() &&
               1 == f_type_stack.size() &&
               1 == f_ctx_stack.size() &&
               1 == f_time_stack.size());

        /* exactly one type in all cases */
        POP_TYPE(res_type);

        if (res_type->is_boolean()) {
            assert(1 == f_values_stack.size());
            value_t res_value { f_values_stack.back() };

            return res_value
                       ? em.make_true()
                       : em.make_false();
        }

        else if (res_type->is_string()) {
            assert(1 == f_values_stack.size());
            value_t cp { f_values_stack.at(0) };
            expr::Atom atom { (const char*) cp };

            return em.make_qstring(atom);
        }

        else if (res_type->is_enum()) {
            assert(1 == f_values_stack.size());
            value_t res_value { f_values_stack.back() };
            type::EnumType_ptr enum_type { res_type->as_enum() };

            const expr::ExprSet& literals { enum_type->literals() };
            expr::ExprSet::const_iterator i { literals.begin() };

            while (0 < res_value) {
                --res_value;
                ++i;
            }

            return *i;
        }

        else if (res_type->is_algebraic()) {
            assert(1 == f_values_stack.size());
            value_t res_value { f_values_stack.back() };

            return em.make_const(res_value);
        }

        else if (res_type->is_array()) {
            type::ArrayType_ptr atype { res_type->as_array() };

            assert(atype->nelems() ==
                   f_values_stack.size());

            expr::Expr_ptr lst(NULL);

            /* assemble array values list */
            for (unsigned i = 0; i < atype->nelems(); ++i) {
                value_t lst_value { f_values_stack.back() };
                f_values_stack.pop_back();

                lst = lst
                          ? em.make_array_comma(lst, em.make_const(lst_value))
                          : em.make_const(lst_value);
            }

            /* wrap list in ARRAY node and return */
            return em.make_array(lst);
        }

        else {
            assert(false);
        }
    }

    /*  Evaluation engine is implemented using a simple expression walker
     *  pattern: (a) on preorder, return true if the node has not yet been
     *  visited; (b) always do in-order (for binary nodes); (c) perform
     *  proper compilation in post-order hooks. */
    bool Evaluator::walk_at_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_at_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_at_postorder(const expr::Expr_ptr expr)
    {
        POP_TYPE(rhs_type);
        DROP_TYPE();
        PUSH_TYPE(rhs_type);

        POP_VALUE(rhs);
        DROP_VALUE();
        PUSH_VALUE(rhs);

        assert(0 < f_time_stack.size());
        f_time_stack.pop_back(); // reset time stack
    }

    /* unexpected */
    bool Evaluator::walk_interval_preorder(const expr::Expr_ptr expr)
    {
        assert(false);
        return false;
    }
    bool Evaluator::walk_interval_inorder(const expr::Expr_ptr expr)
    {
        return false;
    }
    void Evaluator::walk_interval_postorder(const expr::Expr_ptr expr)
    {}

    bool Evaluator::walk_next_preorder(const expr::Expr_ptr expr)
    {
        step_t curr_time { f_time_stack.back() };
        f_time_stack.push_back(curr_time + 1);

        return true;
    }
    void Evaluator::walk_next_postorder(const expr::Expr_ptr expr)
    {
        assert(0 < f_time_stack.size());
        f_time_stack.pop_back(); // reset time stack
    }

    bool Evaluator::walk_neg_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    void Evaluator::walk_neg_postorder(const expr::Expr_ptr expr)
    {
        POP_VALUE(lhs);
        PUSH_VALUE(-lhs);
    }

    bool Evaluator::walk_not_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    void Evaluator::walk_not_postorder(const expr::Expr_ptr expr)
    {
        POP_VALUE(lhs);
        PUSH_VALUE(!lhs);
    }

    bool Evaluator::walk_bw_not_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    void Evaluator::walk_bw_not_postorder(const expr::Expr_ptr expr)
    {
        POP_VALUE(lhs);
        PUSH_VALUE(~lhs);
    }

    bool Evaluator::walk_add_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_add_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_add_postorder(const expr::Expr_ptr expr)
    {
        DROP_TYPE();

        POP_VALUE(rhs);
        POP_VALUE(lhs);
        PUSH_VALUE(lhs + rhs);
    }

    bool Evaluator::walk_sub_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_sub_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_sub_postorder(const expr::Expr_ptr expr)
    {
        DROP_TYPE();

        POP_VALUE(rhs);
        POP_VALUE(lhs);
        PUSH_VALUE(lhs - rhs);
    }

    bool Evaluator::walk_div_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_div_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_div_postorder(const expr::Expr_ptr expr)
    {
        DROP_TYPE();

        POP_VALUE(rhs);
        POP_VALUE(lhs);
        PUSH_VALUE(lhs / rhs);
    }

    bool Evaluator::walk_mul_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_mul_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_mul_postorder(const expr::Expr_ptr expr)
    {
        DROP_TYPE();

        POP_VALUE(rhs);
        POP_VALUE(lhs);
        PUSH_VALUE(lhs * rhs);
    }

    bool Evaluator::walk_mod_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_mod_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_mod_postorder(const expr::Expr_ptr expr)
    {
        DROP_TYPE();

        POP_VALUE(rhs);
        POP_VALUE(lhs);
        PUSH_VALUE(lhs % rhs);
    }

    bool Evaluator::walk_and_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_and_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_and_postorder(const expr::Expr_ptr expr)
    {
        DROP_TYPE();

        POP_VALUE(rhs);
        POP_VALUE(lhs);
        PUSH_VALUE(lhs && rhs);
    }

    bool Evaluator::walk_bw_and_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_bw_and_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_bw_and_postorder(const expr::Expr_ptr expr)
    {
        DROP_TYPE();

        POP_VALUE(rhs);
        POP_VALUE(lhs);
        PUSH_VALUE(lhs & rhs);
    }

    bool Evaluator::walk_or_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_or_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_or_postorder(const expr::Expr_ptr expr)
    {
        DROP_TYPE();

        POP_VALUE(rhs);
        POP_VALUE(lhs);
        PUSH_VALUE(lhs || rhs);
    }

    bool Evaluator::walk_bw_or_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_bw_or_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_bw_or_postorder(const expr::Expr_ptr expr)
    {
        DROP_TYPE();

        POP_VALUE(rhs);
        POP_VALUE(lhs);
        PUSH_VALUE(lhs | rhs);
    }

    bool Evaluator::walk_bw_xor_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_bw_xor_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_bw_xor_postorder(const expr::Expr_ptr expr)
    {
        DROP_TYPE();

        POP_VALUE(rhs);
        POP_VALUE(lhs);
        PUSH_VALUE(lhs ^ rhs);
    }

    bool Evaluator::walk_bw_xnor_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_bw_xnor_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_bw_xnor_postorder(const expr::Expr_ptr expr)
    {
        DROP_TYPE();

        POP_VALUE(rhs);
        POP_VALUE(lhs);
        PUSH_VALUE(((!lhs) | rhs) & ((!rhs) | lhs));
    }

    bool Evaluator::walk_guard_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_guard_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_guard_postorder(const expr::Expr_ptr expr)
    {
        assert(false); /* unreachable */
    }

    bool Evaluator::walk_implies_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_implies_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_implies_postorder(const expr::Expr_ptr expr)
    {
        DROP_TYPE();

        POP_VALUE(rhs);
        POP_VALUE(lhs);
        PUSH_VALUE((!lhs || rhs));
    }

    bool Evaluator::walk_lshift_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_lshift_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_lshift_postorder(const expr::Expr_ptr expr)
    {
        /* drops rhs, which is fine */
        DROP_TYPE();

        POP_VALUE(rhs);
        POP_VALUE(lhs);
        PUSH_VALUE((lhs << rhs));
    }

    bool Evaluator::walk_rshift_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_rshift_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_rshift_postorder(const expr::Expr_ptr expr)
    {
        /* drop rhs, which is fine */
        DROP_TYPE();

        POP_VALUE(rhs);
        POP_VALUE(lhs);
        PUSH_VALUE((lhs >> rhs));
    }

    bool Evaluator::walk_assignment_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_assignment_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_assignment_postorder(const expr::Expr_ptr expr)
    {
        assert(false); /* unreachable */
    }

    bool Evaluator::walk_eq_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_eq_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_eq_postorder(const expr::Expr_ptr expr)
    {
        type::TypeMgr& tm { f_owner.tm() };

        POP_TYPE(rhs_type);
        POP_TYPE(lhs_type);

        if (rhs_type->is_scalar() &&
            lhs_type->is_scalar()) {

            POP_VALUE(rhs);
            POP_VALUE(lhs);

            PUSH_VALUE((lhs == rhs));
        }

        else if (rhs_type->is_array() &&
                 lhs_type->is_array()) {

            type::ArrayType_ptr arhs_type { rhs_type->as_array() };
            type::ArrayType_ptr alhs_type { lhs_type->as_array() };

            assert(arhs_type->width() ==
                       alhs_type->width() &&
                   arhs_type->nelems() ==
                       alhs_type->nelems());

            unsigned nelems { arhs_type->nelems() };

            value_t rhs[nelems];
            for (unsigned i = 0; i < nelems; ++i) {
                rhs[i] = TOP_VALUE();
                DROP_VALUE();
            }

            value_t lhs[nelems];
            for (unsigned i = 0; i < nelems; ++i) {
                lhs[i] = TOP_VALUE();
                DROP_VALUE();
            }

            bool res { true };
            for (unsigned i = 0; res && i < nelems; ++i) {
                if (rhs[i] != lhs[i])
                    res = false;
            }

            PUSH_VALUE((value_t) res);
        }

        else {
            assert(false);
        }

        PUSH_TYPE(tm.find_boolean());
    }

    bool Evaluator::walk_ne_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_ne_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_ne_postorder(const expr::Expr_ptr expr)
    {
        type::TypeMgr& tm { f_owner.tm() };

        DROP_TYPE();
        DROP_TYPE();
        PUSH_TYPE(tm.find_boolean());

        POP_VALUE(rhs);
        POP_VALUE(lhs);
        PUSH_VALUE(lhs != rhs);
    }

    bool Evaluator::walk_gt_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_gt_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_gt_postorder(const expr::Expr_ptr expr)
    {
        type::TypeMgr& tm { f_owner.tm() };

        DROP_TYPE();
        DROP_TYPE();
        PUSH_TYPE(tm.find_boolean());

        POP_VALUE(rhs);
        POP_VALUE(lhs);
        PUSH_VALUE((lhs > rhs));
    }

    bool Evaluator::walk_ge_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_ge_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_ge_postorder(const expr::Expr_ptr expr)
    {
        type::TypeMgr& tm { f_owner.tm() };

        DROP_TYPE();
        DROP_TYPE();
        PUSH_TYPE(tm.find_boolean());

        POP_VALUE(rhs);
        POP_VALUE(lhs);
        PUSH_VALUE((lhs >= rhs));
    }

    bool Evaluator::walk_lt_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_lt_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_lt_postorder(const expr::Expr_ptr expr)
    {
        type::TypeMgr& tm { f_owner.tm() };

        DROP_TYPE();
        DROP_TYPE();
        PUSH_TYPE(tm.find_boolean());

        POP_VALUE(rhs);
        POP_VALUE(lhs);
        PUSH_VALUE((lhs < rhs));
    }

    bool Evaluator::walk_le_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_le_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_le_postorder(const expr::Expr_ptr expr)
    {
        type::TypeMgr& tm { f_owner.tm() };

        DROP_TYPE();
        DROP_TYPE();
        PUSH_TYPE(tm.find_boolean());

        POP_VALUE(rhs);
        POP_VALUE(lhs);
        PUSH_VALUE((lhs <= rhs));
    }

    bool Evaluator::walk_ite_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_ite_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_ite_postorder(const expr::Expr_ptr expr)
    {
        POP_TYPE(rhs_type);
        DROP_TYPE();
        DROP_TYPE();
        PUSH_TYPE(rhs_type);

        POP_VALUE(rhs);
        POP_VALUE(lhs);
        POP_VALUE(cnd);
        PUSH_VALUE((cnd ? lhs : rhs));
    }

    bool Evaluator::walk_cond_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_cond_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_cond_postorder(const expr::Expr_ptr expr)
    { /* nop */
    }

    bool Evaluator::walk_dot_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_dot_inorder(const expr::Expr_ptr expr)
    {
        expr::ExprMgr& em { f_owner.em() };

        DROP_TYPE();

        TOP_CTX(parent_ctx);

        expr::Expr_ptr ctx { em.make_dot(parent_ctx, expr->lhs()) };
        PUSH_CTX(ctx);

        return true;
    }
    void Evaluator::walk_dot_postorder(const expr::Expr_ptr expr)
    {
        DROP_CTX();
    }

    bool Evaluator::walk_params_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_params_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_params_postorder(const expr::Expr_ptr expr)
    {
        assert(false); /* not yet implemented */
    }

    bool Evaluator::walk_params_comma_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_params_comma_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_params_comma_postorder(const expr::Expr_ptr expr)
    {
        assert(false); /* TODO support inlined non-determinism */
    }


    bool Evaluator::walk_subscript_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_subscript_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }

    void Evaluator::walk_subscript_postorder(const expr::Expr_ptr expr)
    {
        bool found { false };
        value_t res { 0 };

        POP_TYPE(rhs_type);
        assert(rhs_type->is_algebraic());

        POP_TYPE(lhs_type);
        assert(lhs_type->is_array());

        const type::ArrayType_ptr alhs_type { lhs_type->as_array() };

        /* fetch the index */
        POP_VALUE(index);

        /* fetch all items, record the interesting one */
        for (unsigned i = 0; i < alhs_type->nelems(); ++i) {
            POP_VALUE(elem);

            if (i == alhs_type->nelems() - index - 1) {
                found = true;
                res = elem;
            }
        }

        if (!found) {
            throw NoValue(expr);
        }

        /* return the value and scalar type*/
        PUSH_TYPE(alhs_type->of());
        PUSH_VALUE(res);
    }

    bool Evaluator::walk_array_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    void Evaluator::walk_array_postorder(const expr::Expr_ptr expr)
    {}

    bool Evaluator::walk_array_comma_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_array_comma_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_array_comma_postorder(const expr::Expr_ptr expr)
    {
        type::TypeMgr& tm { type::TypeMgr::INSTANCE() };

        POP_TYPE(rhs_type);

        unsigned nelems(rhs_type->is_scalar()
                            ? 2 /* base */
                            : 1 + rhs_type->as_array()->nelems());

        POP_TYPE(lhs_type);
        assert(lhs_type->is_scalar());

        type::ArrayType_ptr atmp_type {
            tm.find_array_type(lhs_type->as_scalar(), nelems)
        };

        PUSH_TYPE(atmp_type);
    }

    bool Evaluator::walk_set_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    void Evaluator::walk_set_postorder(const expr::Expr_ptr expr)
    {
        assert(false); // TODO
    }

    bool Evaluator::walk_set_comma_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_set_comma_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_set_comma_postorder(const expr::Expr_ptr expr)
    {
        assert(false); /* TODO support inlined non-determinism */
    }

    bool Evaluator::walk_type_preorder(const expr::Expr_ptr expr)
    {
        return false;
    }
    bool Evaluator::walk_type_inorder(const expr::Expr_ptr expr)
    {
        assert(false);
        return false;
    }
    void Evaluator::walk_type_postorder(const expr::Expr_ptr expr)
    {
        assert(false);
    }

    bool Evaluator::walk_cast_preorder(const expr::Expr_ptr expr)
    {
        return cache_miss(expr);
    }
    bool Evaluator::walk_cast_inorder(const expr::Expr_ptr expr)
    {
        return true;
    }
    void Evaluator::walk_cast_postorder(const expr::Expr_ptr expr)
    { /* nop */
    }

}; // namespace witness

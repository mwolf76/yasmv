/**
 * @file internals.cc
 * @brief Type checking subsystem, internals implementation.
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

#include <enc/enc_mgr.hh>

#include <model/model_mgr.hh>
#include <model/type_checker/type_checker.hh>

#include <utils/logging.hh>

#define DEBUG_TYPE_CHECKER

namespace model {

    // fun: any -> any
    void TypeChecker::walk_unary_fsm_postorder(const expr::Expr_ptr expr)
    {
        PUSH_TYPE(check_any(expr->lhs()));
    }

    // fun: arithmetical -> arithmetical
    void TypeChecker::walk_unary_arithmetical_postorder(const expr::Expr_ptr expr)
    {
        PUSH_TYPE(check_arithmetical(expr->lhs()));
    }

    // fun: logical -> logical
    void TypeChecker::walk_unary_logical_postorder(const expr::Expr_ptr expr)
    {
        PUSH_TYPE(check_logical(expr->lhs()));
    }

    // fun: instant, (timed) any -> any
    void TypeChecker::walk_binary_timed_postorder(const expr::Expr_ptr expr)
    {
        PUSH_TYPE(check_timed(expr));
    }

    // fun: arithmetical, arithmetical -> arithmetical
    void TypeChecker::walk_binary_arithmetical_postorder(const expr::Expr_ptr expr)
    {
        auto& tm { type::TypeMgr::INSTANCE() };

        const auto rhs { check_arithmetical(expr->rhs()) };
        const auto lhs { check_arithmetical(expr->lhs()) };

        // identical types most definitely match
        if (rhs == lhs) {
            PUSH_TYPE(rhs);
            return;
        }

        const auto arhs { dynamic_cast<type::AlgebraicType_ptr>(rhs) };
        const auto alhs { dynamic_cast<type::AlgebraicType_ptr>(lhs) };

        // if rhs is a constant, use lhs type
        if (arhs->is_constant()) {
            PUSH_TYPE(alhs);
            return;
        }

        // lhs is a constant, use rhs type
        if (alhs->is_constant()) {
            PUSH_TYPE(arhs);
            return;
        }

        const bool signedness {
            arhs->is_signed_algebraic() ||
            alhs->is_signed_algebraic()
        };

        // resulting type has the same width as the largest
        const auto width {
            std::max(arhs->width(),
                     alhs->width())
        };

        PUSH_TYPE(
            signedness
                ? tm.find_signed(width)
                : tm.find_unsigned(width));
    }

    // fun: logical x logical -> logical
    void TypeChecker::walk_binary_fsm_postorder(const expr::Expr_ptr expr)
    {
        const auto rhs_type { check_logical(expr->rhs()) };
        (void) rhs_type;

        const auto lhs_type { check_logical(expr->lhs()) };

        PUSH_TYPE(lhs_type);
    }

    // fun: logical x logical -> logical
    void TypeChecker::walk_binary_logical_postorder(const expr::Expr_ptr expr)
    {
        const auto rhs_type { check_logical(expr->rhs()) };
        (void) rhs_type;

        const auto lhs_type { check_logical(expr->lhs()) };

        PUSH_TYPE(lhs_type);
    }

    void TypeChecker::walk_binary_cast_postorder(const expr::Expr_ptr expr)
    {
        TOP_TYPE(rhs_type); // here we inspect the type stack, without popping the element

        if (rhs_type->is_boolean()) {
            const auto lhs_type { check_logical(expr->lhs()) };
            (void) lhs_type;

            return;
        }

        if (rhs_type->is_algebraic()) {
            const auto lhs_type { check_arithmetical(expr->lhs()) };
            (void) lhs_type;

            const auto rhs_repr { rhs_type->repr() };
            const auto lhs_repr { lhs_type->repr() };

            DEBUG
                << "Casting from "
                << lhs_repr
                << " to "
                << rhs_repr
                << std::endl;
            ;

            return;
        }

        // if rhs is an enum, lhs must be an enum of the same type
        throw type::BadType(expr->rhs(), rhs_type);
    }

    void TypeChecker::walk_binary_shift_postorder(const expr::Expr_ptr expr)
    {
        const auto rhs_type { check_arithmetical(expr->rhs()) };
        const auto lhs_type { check_arithmetical(expr->lhs()) };
        (void) lhs_type;

        PUSH_TYPE(rhs_type);
    }

    // fun: arithmetical x arithmetical -> boolean
    void TypeChecker::walk_binary_relational_postorder(const expr::Expr_ptr expr)
    {
        auto& tm { type::TypeMgr::INSTANCE() };
        const auto boolean { tm.find_boolean() };

        const auto rhs { check_arithmetical(expr->rhs()) };
        const auto lhs { check_arithmetical(expr->lhs()) };

        // matching types are most definitely ok
        if (rhs == lhs) {
            PUSH_TYPE(boolean);
            return;
        }

        const auto arhs { dynamic_cast<type::AlgebraicType_ptr>(rhs) };
        const auto alhs { dynamic_cast<type::AlgebraicType_ptr>(lhs) };

        // if either type is constant, we're good
        if (arhs->is_constant() || alhs->is_constant()) {
            PUSH_TYPE(boolean);
            return;
        }

        // two algebraic non-constant types, they need to be compatible
        if (arhs->width() == alhs->width()) {
            PUSH_TYPE(boolean);
            return;
        }

        throw type::TypeMismatch(expr, alhs, arhs);
    }

    // fun: logical/arithmetical/enum x logical/arithmetical/enum -> boolean
    void TypeChecker::walk_binary_equality_postorder(const expr::Expr_ptr expr)
    {
        auto& tm { type::TypeMgr::INSTANCE() };
        const auto boolean { tm.find_boolean() };

        POP_TYPE(rhs_type);

        if (rhs_type->is_boolean()) {
            const auto lhs_type { check_logical(expr->lhs()) };
            (void) lhs_type;

            PUSH_TYPE(boolean);
            return;
        }

        if (rhs_type->is_algebraic()) {
            const auto lhs_type { check_arithmetical(expr->lhs()) };

            // if they are the same type, we're good
            if (rhs_type == lhs_type) {
                PUSH_TYPE(boolean);
                return;
            }

            // if either type is constant, we're good
            if (rhs_type->is_constant() || lhs_type->is_constant()) {
                PUSH_TYPE(boolean);
                return;
            }

            // two algebraic non-constant types, they need to be compatible
            if (rhs_type->width() == lhs_type->width()) {
                PUSH_TYPE(boolean);
                return;
            }

            throw type::TypeMismatch(expr, lhs_type, rhs_type);
        }

        if (rhs_type->is_enum()) {
            POP_TYPE(lhs_type);

            /* enums, if they are the same type we're good */
            if (lhs_type == rhs_type) {
                PUSH_TYPE(boolean);
                return;
            }

            throw type::TypeMismatch(expr, lhs_type, rhs_type);
        }

        if (rhs_type->is_array()) {
            POP_TYPE(lhs_type);

            // if the types are the same, we're good
            if (lhs_type == rhs_type) {
                PUSH_TYPE(boolean);
                return;
            }

            // one is an array, the other is not
            if (!lhs_type->is_array()) {
                throw type::TypeMismatch(expr, lhs_type, rhs_type);
            }

            // both are arrays, check their types
            const auto alhs { lhs_type->as_array() };
            const auto arhs { rhs_type->as_array() };

            if (alhs->nelems() != arhs->nelems()) {
                throw type::TypeMismatch(expr, lhs_type, rhs_type);
            }

            // check the types of the elements
            const auto lhs_of { alhs->of() };
            const auto rhs_of { arhs->of() };

            // if either is a constant, we're good
            if (lhs_of->is_constant() || rhs_of->is_constant()) {
                PUSH_TYPE(boolean);
                return;
            }

            // both not constant, they need to be compatible
            if (lhs_of->width() == rhs_of->width()) {
                PUSH_TYPE(tm.find_boolean());
                return;
            }

            throw type::TypeMismatch(expr, lhs_type, rhs_type);
        }

        // if we reach here, we have an unexpected type
        assert(false && "unexpected type in binary equality");
    }

    void TypeChecker::walk_binary_ite_postorder(expr::Expr_ptr expr)
    {
        auto& tm { type::TypeMgr::INSTANCE() };

        POP_TYPE(rhs_type);

        if (rhs_type->is_boolean()) {
            const auto lhs_type { check_logical(expr->lhs()) };
            (void) lhs_type;

            PUSH_TYPE(tm.find_boolean());
            return;
        }

        if (rhs_type->is_algebraic()) {
            const auto lhs_type { check_arithmetical(expr->lhs()) };

            // if either type is constant, we use the other type
            if (rhs_type->is_constant()) {
                PUSH_TYPE(lhs_type);
                return;
            }

            if (lhs_type->is_constant()) {
                PUSH_TYPE(rhs_type);
                return;
            }

            const auto signedness {
                rhs_type->is_signed_algebraic() ||
                lhs_type->is_signed_algebraic()
            };

            // two algebraic non-constant types, they need to be compatible
            if (rhs_type->width() == lhs_type->width()) {
                const auto width { rhs_type->width() };

                PUSH_TYPE(
                    signedness
                        ? tm.find_signed(width)
                        : tm.find_unsigned(width));

                return;
            }

            throw type::TypeMismatch(expr, lhs_type, rhs_type);
        }

        if (rhs_type->is_array()) {
            const auto lhs_type { check_array(expr->lhs()) };

            const auto alhs_type { lhs_type->as_array() };
            const auto alhs_of_type { alhs_type->of() };
            const auto lhs_width { alhs_of_type->width() };
            const auto lhs_elems { alhs_type->nelems() };

            const auto arhs_type { rhs_type->as_array() };
            const auto arhs_of_type { arhs_type->of() };
            const auto rhs_width { arhs_of_type->width() };
            const auto rhs_elems { arhs_type->nelems() };

            if (lhs_width == rhs_width &&
                lhs_elems == rhs_elems) {
                const bool signedness {
                    alhs_type->is_signed_algebraic() ||
                    arhs_type->is_signed_algebraic()
                };

                PUSH_TYPE(
                    signedness
                        ? tm.find_signed_array(rhs_width, rhs_elems)
                        : tm.find_unsigned_array(rhs_width, rhs_elems));

                return;
            }

            throw type::TypeMismatch(expr, lhs_type, rhs_type);
        }

        if (rhs_type->is_enum()) {
            POP_TYPE(lhs_type);

            if (lhs_type == rhs_type) {
                PUSH_TYPE(rhs_type);
                return;
            }

            throw type::TypeMismatch(expr, lhs_type, rhs_type);
        }

        // if we reach here, we have an unexpected type
        assert(false && "unexpected type in binary ite");
    }

    void TypeChecker::memoize_result(expr::Expr_ptr expr)
    {
        auto& em { expr::ExprMgr::INSTANCE() };

        const auto key {
            em.make_dot(f_ctx_stack.back(), expr)
        };
        const auto type { f_type_stack.back() };

#if defined DEBUG_TYPE_CHECKER
        const auto type_repr { type->repr() };

        DEBUG
            << "TYPE ("
            << key
            << ") = "
            << type_repr
            << std::endl;
#endif

        f_map[key] = type;
    }

    type::Type_ptr TypeChecker::type(expr::Expr_ptr expr, expr::Expr_ptr ctx)
    {
        auto& em { expr::ExprMgr::INSTANCE() };
        type::Type_ptr res { nullptr };

        /* to avoid a number of cache misses due to compiler rewrites,
         * we squeeze types in equivalence classes: Relational -> lhs
         * '<' rhs, Arithmetical -> lhs '+' rhs */
        const auto key { em.make_dot(ctx, expr) };
        const auto eye { f_map.find(key) };

        // cache miss, fallback to walker
        if (eye == f_map.end()) {
            res = process(expr, ctx);
        } else {
            res = eye->second;
        }

        assert(nullptr != res);
        return res;
    }

    void TypeChecker::pre_hook()
    {}
    void TypeChecker::post_hook()
    {}

    void TypeChecker::pre_node_hook(expr::Expr_ptr expr)
    {
#if defined DEBUG_TYPE_CHECKER
        DEBUG
            << "Type checking "
            << expr
            << "..."
            << std::endl;
#endif
    }
    void TypeChecker::post_node_hook(expr::Expr_ptr expr)
    {
#if defined DEBUG_TYPE_CHECKER
        DEBUG
            << expr
            << std::endl;

        int depth = 0;
        for (auto ti = f_type_stack.rbegin();
             ti != f_type_stack.rend(); ++depth, ++ti) {

            type::Type_ptr type { *ti };
            expr::Expr_ptr repr { type->repr() };

            DEBUG
                << depth
                << ": "
                << repr
                << std::endl;
        }

        DEBUG
            << "----------"
            << std::endl;
#endif

        memoize_result(expr);
    }

    type::Type_ptr TypeChecker::check_timed(const expr::Expr_ptr expr)
    {
        POP_TYPE(res);
        assert(nullptr != res);

        POP_TYPE(instant);
        assert(nullptr != instant);

        if (instant->is_time()) {
            return res;
        }

        throw type::BadType(expr, res);
    }

    type::Type_ptr TypeChecker::check_logical(const expr::Expr_ptr expr)
    {
        POP_TYPE(res);
        assert(nullptr != res);

        if (res->is_boolean()) {
            return res;
        }

        throw type::BadType(expr, res);
    }

    type::Type_ptr TypeChecker::check_arithmetical(const expr::Expr_ptr expr)
    {
        POP_TYPE(res);
        assert(nullptr != res);

        if (res->is_algebraic()) {
            return res;
        }

        throw type::BadType(expr, res);
    }

    type::Type_ptr TypeChecker::check_scalar(const expr::Expr_ptr expr)
    {
        POP_TYPE(res);
        assert(nullptr != res);

        if (res->is_scalar())
            return res;

        throw type::BadType(expr, res);
    }

    type::Type_ptr TypeChecker::check_any(const expr::Expr_ptr expr)
    {
        POP_TYPE(res);
        assert(nullptr != res);

        (void) expr;

        return res;
    }

    type::Type_ptr TypeChecker::check_array(const expr::Expr_ptr expr)
    {
        POP_TYPE(res);
        assert(nullptr != res);

        if (res->is_array()) {
            return res;
        }

        throw type::BadType(expr, res);
    }

    // services
    bool TypeChecker::cache_miss(const expr::Expr_ptr expr)
    {
        auto& em { expr::ExprMgr::INSTANCE() };
        const auto key {
            em.make_dot(f_ctx_stack.back(), expr)
        };

        const auto eye { f_map.find(key) };

        if (eye != f_map.end()) {
            const type::Type_ptr res { eye->second };
            PUSH_TYPE(res);

#if defined DEBUG_TYPE_CHECKER
            const auto repr { res->repr() };

            DEBUG
                << "cache hit for `"
                << expr
                << "`: "
                << repr
                << std::endl;
#endif

            return false;
        }

        return true;
    }

}; // namespace model

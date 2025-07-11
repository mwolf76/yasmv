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

#include <algorithm>

#define DEBUG_TYPE_CHECKER

namespace model {

    // fun: any -> any
    void TypeChecker::walk_unary_fsm_postorder(const expr::Expr_ptr expr)
    {
        PUSH_TYPE(check_any(expr->lhs()));
    }


    // fun: arithm -> arithm
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

    // fun: arithm, arithm -> arithm
    void TypeChecker::walk_binary_arithmetical_postorder(const expr::Expr_ptr expr)
    {
        type::TypeMgr& tm { type::TypeMgr::INSTANCE() };

        type::Type_ptr rhs { check_arithmetical(expr->rhs()) };
        type::Type_ptr lhs { check_arithmetical(expr->lhs()) };

        // identical types most definitely match
        if (rhs == lhs) {
            PUSH_TYPE(rhs);
            return;
        }

        type::AlgebraicType_ptr arhs { dynamic_cast<type::AlgebraicType_ptr>(rhs) };
        type::AlgebraicType_ptr alhs { dynamic_cast<type::AlgebraicType_ptr>(lhs) };

        // width mismatch is only admissible if either operant is a constant
        if (arhs->width() != alhs->width() &&
            !arhs->is_constant() &&
            !alhs->is_constant()) {
            throw type::TypeMismatch(expr, alhs, arhs);
        }

        bool signedness {
            arhs->is_signed_algebraic() ||
            alhs->is_signed_algebraic()
        };

        unsigned width {
            std::min(
                arhs->width(),
                alhs->width())
        };

        PUSH_TYPE(signedness
                      ? tm.find_signed(width)
                      : tm.find_unsigned(width));
    }

    // fun: logical x logical -> logical
    void TypeChecker::walk_binary_fsm_postorder(const expr::Expr_ptr expr)
    {
        type::Type_ptr rhs_type { check_logical(expr->rhs()) };
        (void) rhs_type;

        type::Type_ptr lhs_type { check_logical(expr->lhs()) };

        PUSH_TYPE(lhs_type);
    }


    // fun: logical x logical -> logical
    void TypeChecker::walk_binary_logical_postorder(const expr::Expr_ptr expr)
    {
        type::Type_ptr rhs_type { check_logical(expr->rhs()) };
        (void) rhs_type;

        type::Type_ptr lhs_type { check_logical(expr->lhs()) };

        PUSH_TYPE(lhs_type);
    }

    void TypeChecker::walk_binary_cast_postorder(const expr::Expr_ptr expr)
    {
        TOP_TYPE(rhs_type);

        if (rhs_type->is_boolean()) {
            type::Type_ptr lhs_type { check_logical(expr->lhs()) };
            (void) lhs_type;
        }

        else if (rhs_type->is_algebraic()) {
            type::Type_ptr lhs_type { check_arithmetical(expr->lhs()) };
            (void) lhs_type;

            expr::Expr_ptr rhs_repr { rhs_type->repr() };
            expr::Expr_ptr lhs_repr { lhs_type->repr() };


            DEBUG
                << "Casting from "
                << lhs_repr
                << " to "
                << rhs_repr
                << std::endl;
            ;
        }

        else
            throw type::BadType(expr->rhs(), rhs_type);
    }

    void TypeChecker::walk_binary_shift_postorder(const expr::Expr_ptr expr)
    {
        type::Type_ptr rhs_type { check_arithmetical(expr->rhs()) };
        type::Type_ptr lhs_type { check_arithmetical(expr->lhs()) };
        (void) lhs_type;

        PUSH_TYPE(rhs_type);
    }

    // fun: arithmetical x arithmetical -> boolean
    void TypeChecker::walk_binary_relational_postorder(const expr::Expr_ptr expr)
    {
        type::TypeMgr& tm { type::TypeMgr::INSTANCE() };
        type::Type_ptr boolean { tm.find_boolean() };

        type::Type_ptr rhs { check_arithmetical(expr->rhs()) };
        type::Type_ptr lhs { check_arithmetical(expr->lhs()) };

        // matching types are most definitely ok
        if (rhs == lhs) {
            PUSH_TYPE(boolean);
            return;
        }

        type::AlgebraicType_ptr arhs { dynamic_cast<type::AlgebraicType_ptr>(rhs) };
        type::AlgebraicType_ptr alhs { dynamic_cast<type::AlgebraicType_ptr>(lhs) };

        // width mismatch admissible only if either operand is a constant
        if (arhs->width() != alhs->width() &&
            !arhs->is_constant() &&
            !alhs->is_constant()) {
            throw type::TypeMismatch(expr, alhs, arhs);
        }

        PUSH_TYPE(boolean);
    }

    // fun: logical/arithmetical/enum x logical/arithmetical/enum -> boolean
    void TypeChecker::walk_binary_equality_postorder(const expr::Expr_ptr expr)
    {
        type::TypeMgr& tm { type::TypeMgr::INSTANCE() };

        POP_TYPE(rhs_type);

        if (rhs_type->is_boolean()) {
            type::Type_ptr lhs_type { check_logical(expr->lhs()) };
            (void) lhs_type;

            PUSH_TYPE(tm.find_boolean());
        } else if (rhs_type->is_algebraic()) {
            type::Type_ptr lhs_type { check_arithmetical(expr->lhs()) };

            /* not necessarily same type, but compatible */
            if (lhs_type->width() ==
                rhs_type->width()) {
                PUSH_TYPE(tm.find_boolean());
                return;
            }

            /* either operand is a constant */
            if (lhs_type->is_constant() ||
                rhs_type->is_constant()) {
                PUSH_TYPE(tm.find_boolean());
                return;
            }

            throw type::TypeMismatch(expr, lhs_type, rhs_type);
        }

        else if (rhs_type->is_enum()) {
            POP_TYPE(lhs_type);
            if (lhs_type != rhs_type) {
                throw type::TypeMismatch(expr, lhs_type, rhs_type);
            }

            PUSH_TYPE(tm.find_boolean());
        } else if (rhs_type->is_array()) {
            POP_TYPE(lhs_type);

            if (lhs_type != rhs_type) {
                if (!lhs_type->is_array()) {
                    throw type::TypeMismatch(expr, lhs_type, rhs_type);
                }

                type::ArrayType_ptr a_lhs { lhs_type->as_array() };
                type::ArrayType_ptr a_rhs { rhs_type->as_array() };

                if (a_lhs->nelems() != a_rhs->nelems()) {
                    throw type::TypeMismatch(expr, lhs_type, rhs_type);
                }

                type::Type_ptr lhs_of { a_lhs->of() };
                type::Type_ptr rhs_of { a_rhs->of() };

                if (lhs_of->width() != rhs_of->width()) {
                    throw type::TypeMismatch(expr, lhs_type, rhs_type);
                }
            }

            PUSH_TYPE(tm.find_boolean());
        } else {
            assert(false);
        }
    }

    void TypeChecker::walk_binary_ite_postorder(expr::Expr_ptr expr)
    {
        type::TypeMgr& tm { type::TypeMgr::INSTANCE() };

        POP_TYPE(rhs_type);

        if (rhs_type->is_boolean()) {
            type::Type_ptr lhs_type { check_logical(expr->lhs()) };
            (void) lhs_type;

            PUSH_TYPE(tm.find_boolean());
            return;
        }

        if (rhs_type->is_algebraic()) {
            type::Type_ptr lhs_type { check_arithmetical(expr->lhs()) };

            // width mismatch is only admissible if either operand is a constant
            if (rhs_type->width() != lhs_type->width() &&
                !rhs_type->is_constant() &&
                !lhs_typs->is_constant())
                throw type::TypeMismatch(expr, lhs_type, rhs_type);

            bool signedness {
                rhs_type->is_signed_algebraic() ||
                lhs_type->is_signed_algebraic()
            };

            unsigned width {
                std::min(
                    rhs_type->width(),
                    lhs_type->width())
            };

            PUSH_TYPE(signedness
                          ? tm.find_signed(width)
                          : tm.find_unsigned(width));

            return;
        }

        if (rhs_type->is_array()) {
            type::Type_ptr lhs_type { check_array(expr->lhs()) };

            type::ArrayType_ptr alhs_type { lhs_type->as_array() };
            type::ScalarType_ptr alhs_of_type { alhs_type->of() };
            unsigned lhs_width { alhs_of_type->width() };
            unsigned lhs_elems { alhs_type->nelems() };

            type::ArrayType_ptr arhs_type { rhs_type->as_array() };
            type::ScalarType_ptr arhs_of_type { arhs_type->of() };
            unsigned rhs_width { arhs_of_type->width() };
            unsigned rhs_elems { arhs_type->nelems() };

            if (lhs_width != rhs_width ||
                lhs_elems != rhs_elems) {
                throw type::TypeMismatch(expr, lhs_type, rhs_type);
            }

            bool signedness {
                alhs_type->is_signed_algebraic() ||
                arhs_type->is_signed_algebraic()
            };

            PUSH_TYPE(
                signedness
                    ? tm.find_signed_array(rhs_width, rhs_elems)
                    : tm.find_unsigned_array(rhs_width, rhs_elems));

            return;
        }

        if (rhs_type->is_enum()) {
            POP_TYPE(lhs_type);
            if (lhs_type != rhs_type) {
                throw type::TypeMismatch(expr, lhs_type, rhs_type);
            }

            PUSH_TYPE(rhs_type);
            return;
        }

        assert(false);
    }

    void TypeChecker::memoize_result(expr::Expr_ptr expr)
    {
        expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };

        expr::Expr_ptr key {
            em.make_dot(f_ctx_stack.back(), expr)
        };
        type::Type_ptr type { f_type_stack.back() };

#if defined DEBUG_TYPE_CHECKER
        expr::Expr_ptr type_repr { type->repr() };

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
        expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };

        /* to avoid a number of cache misses due to compiler rewrites,
         * we squeeze types in equivalence classes: Relationals -> lhs
         * '<' rhs, Arithmetical -> lhs '+' rhs */
        expr::Expr_ptr key { em.make_dot(ctx, expr) };

        TypeReg::const_iterator eye { f_map.find(key) };
        type::Type_ptr res { NULL };

        // cache miss, fallback to walker
        if (eye == f_map.end()) {
            res = process(expr, ctx);
        } else {
            res = (*eye).second;
        }

        assert(NULL != res);
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

    type::Type_ptr TypeChecker::check_timed(expr::Expr_ptr expr)
    {
        POP_TYPE(res);
        assert(NULL != res);

        POP_TYPE(instant);
        assert(NULL != instant);

        if (instant->is_time()) {
            return res;
        }

        throw type::BadType(expr, res);
        return NULL; /* unreachable */
    }

    type::Type_ptr TypeChecker::check_logical(expr::Expr_ptr expr)
    {
        POP_TYPE(res);
        assert(NULL != res);

        if (res->is_boolean()) {
            return res;
        }

        throw type::BadType(expr, res);
        return NULL; /* unreachable */
    }

    type::Type_ptr TypeChecker::check_arithmetical(expr::Expr_ptr expr)
    {
        POP_TYPE(res);
        assert(NULL != res);

        if (res->is_algebraic()) {
            return res;
        }

        throw type::BadType(expr, res);
        return NULL; /* unreachable */
    }

    type::Type_ptr TypeChecker::check_scalar(expr::Expr_ptr expr)
    {
        POP_TYPE(res);
        assert(NULL != res);

        if (res->is_scalar())
            return res;

        throw type::BadType(expr, res);
        return NULL; /* unreachable */
    }

    type::Type_ptr TypeChecker::check_any(expr::Expr_ptr expr)
    {
        POP_TYPE(res);
        assert(NULL != res);

        return res;
    }

    type::Type_ptr TypeChecker::check_array(expr::Expr_ptr expr)
    {
        POP_TYPE(res);
        assert(NULL != res);

        if (res->is_array()) {
            return res;
        }

        throw type::BadType(expr, res);
        return NULL; /* unreachable */
    }

    // services
    bool TypeChecker::cache_miss(const expr::Expr_ptr expr)
    {
        expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };
        expr::Expr_ptr key {
            em.make_dot(f_ctx_stack.back(), expr)
        };

        TypeReg::iterator eye { f_map.find(key) };

        if (eye != f_map.end()) {
            type::Type_ptr res { (*eye).second };
            PUSH_TYPE(res);

#if defined DEBUG_TYPE_CHECKER
            expr::Expr_ptr repr { res->repr() };

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

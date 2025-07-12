/**
 * @file leaves.cc
 * @brief Model compiler subsystem, leaves services.
 *
 * Copyright (C) 2011-2015 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
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

#include <compiler/compiler.hh>

#include <env/environment.hh>

#include <symb/classes.hh>
#include <symb/proxy.hh>

#include <utils/logging.hh>

namespace compiler {

    static inline value_t pow2(unsigned exp);

    void Compiler::walk_instant(const expr::Expr_ptr expr)
    {
        type::TypeMgr& tm { type::TypeMgr::INSTANCE() };

        DRIVEL
            << expr
            << std::endl;

        PUSH_TYPE(tm.find_time());
        PUSH_TIME(expr->value());
    }

    void Compiler::walk_leaf(const expr::Expr_ptr expr)
    {
        expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };
        type::TypeMgr& tm { type::TypeMgr::INSTANCE() };

        TOP_CTX(ctx);

        if (!cache_miss(expr)) {
            return;
        }

        step_t time { f_time_stack.back() };

        /* 0. Explicit boolean consts (TRUE, FALSE) */
        if (em.is_true(expr) || em.is_false(expr)) {
            PUSH_TYPE(tm.find_boolean());
            PUSH_DD(em.is_true(expr)
                        ? f_enc.one()
                        : f_enc.zero());
            return;
        }

        /* 1. Explicit int constants, perform booleanization
         * immediately. An exception will be thrown if conversion
         * could not be completed. */
        if (em.is_int_const(expr)) {
            unsigned ww { 64 };

            PUSH_TYPE(tm.find_constant(ww));
            algebraic_constant(expr, ww);
            return;
        }

        /* ctx-aware symbol resolution */
        expr::Expr_ptr full { em.make_dot(ctx, expr) };

        symb::ResolverProxy resolver;
        symb::Symbol_ptr symb { resolver.symbol(full) };

        /* 2. bool constant leaves */
        if (symb->is_const()) {
            assert(false); // TODO: is this expected to be unreachable?
            symb::Constant& konst { symb->as_const() };

            PUSH_TYPE(konst.type());
            PUSH_DD(f_enc.constant(konst.value()));
            return;
        }

        /* 3. enum literals */
        if (symb->is_literal()) {
            symb::Literal& lit { symb->as_literal() };

            // push into type stack
            type::Type_ptr type { lit.type() };

            // if encoding for variable is available reuse it,
            // otherwise create and cache it.
            expr::TimedExpr key { full, time };
            enc::Encoding_ptr enc { f_enc.find_encoding(key) };

            /* build a new encoding for this symbol if none is available. */
            if (!enc) {
                enc = f_enc.make_encoding(type);
                f_enc.register_encoding(key, enc);
            }

            enc::EnumEncoding_ptr eenc {
                dynamic_cast<enc::EnumEncoding_ptr>(enc)
            };
            assert(NULL != eenc);

            PUSH_TYPE(type);
            PUSH_DD(f_enc.constant(eenc->value(expr)));
            return;
        }

        /* 4. variables, encodings will be created on-the-fly, if
         *    necessary */
        else if (symb->is_variable()) {
            const symb::Variable& var { symb->as_variable() };
            type::Type_ptr type { var.type() };

            /* INPUT vars are in fact bodyless, typed DEFINEs */
            if (var.is_input()) {
                expr::Expr_ptr value {
                    env::Environment::INSTANCE().get(expr)
                };
                (*this)(value);
            }

            /* REVIEW THIS */
            else if (type->is_instance()) {
                assert(false);
                PUSH_TYPE(type);
            }

            else {
                expr::TimedExpr key {
                    full, var.is_frozen() ? FROZEN : time
                };
                enc::Encoding_ptr enc {
                    find_encoding(key, type)
                };

                PUSH_TYPE(type);
                push_dds(enc, type);
            }

            return;
        }

        /* 5. parameters, must be resolved against the Param map which
         *    is maintained by the ModelMgr */
        else if (symb->is_parameter()) {
            expr::Expr_ptr rewrite { f_owner.rewrite_parameter(full) };

            PUSH_CTX(rewrite->lhs());
            (*this)(rewrite->rhs());

            DROP_CTX();
            return;
        }

        /* 6. DEFINEs, simply compile them recursively :-) */
        else if (symb->is_define()) {
            symb::Define& define { symb->as_define() };
            expr::Expr_ptr body { define.body() };

            (*this)(body);
            return;
        }

        /* give up, TODO: exception */
        assert(false);
    }

    /* private service of walk_leaf */
    void Compiler::push_dds(enc::Encoding_ptr enc, type::Type_ptr type)
    {
        assert(NULL != enc);

        dd::DDVector& dds { enc->dv() };
        auto width { dds.size() };
        assert(0 < width);

        /* booleans, monoliths are just one DD */
        if (type->is_monolithic()) {
            PUSH_DD(dds[0]);
        }

        /* algebraics, reversed list of encoding DDs */
        else if (type->is_algebraic()) {
            // type and enc width info has to match
            assert(type->as_algebraic()->width() == width);
            PUSH_DV(dds, width);
        }

        /* array of algebraics, same as above, times nelems */
        else if (type->is_array()) {
            type::ScalarType_ptr scalar_type { type->as_array()->of() };

            if (scalar_type->is_monolithic()) {
                assert(1 == width / type->as_array()->nelems());
            }

            else if (scalar_type->is_algebraic()) {
                assert(type->as_array()->of()->as_algebraic()->width() ==
                       width / type->as_array()->nelems());
            }

            PUSH_DV(dds, width);
        }

        else {
            assert(false); // unexpected
        }
    }

    static inline value_t pow2(unsigned exp)
    {
        value_t res { 1 };

        if (!exp) {
            return res;
        }
        ++res;

        while (--exp) {
            res <<= 1;
        }

        return res;
    }

    /* encodes constant value into a DD vector */
    void Compiler::algebraic_constant(expr::Expr_ptr konst, unsigned width)
    {
        const unsigned base { 2 };
        value_t value { konst->value() };

        if (value < 0) {
            value += pow2(width); // 2's complement
        }

        for (unsigned i = 0; i < width; ++i) {
            ADD digit { f_enc.constant(value % base) };

            f_add_stack.push_back(digit);
            value /= base;
        }

        if (value) {
            throw ConstantTooLarge(konst);
        }
    }

} // namespace compiler

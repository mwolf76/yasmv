/**
 * @file array.cc
 * @brief Expression compiler subsystem, array operators implementations.
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

#include <compiler.hh>
#include <expr.hh>

namespace compiler {

    void Compiler::array_equals(const expr::Expr_ptr expr)
    {
        type::TypeMgr& tm { type::TypeMgr::INSTANCE() };

        POP_TYPE(rhs_type);
        POP_TYPE(lhs_type);

        assert(lhs_type->is_array() &&
               rhs_type->is_array());

        const type::ArrayType_ptr atype { rhs_type->as_array() };
        unsigned elems { atype->nelems() };

        const type::ScalarType_ptr stype { atype->of() };
        unsigned width { stype->width() };

        /* res := AND(lhs[i] == rhs[i]) */
        const type::Type_ptr res_type { tm.find_boolean() };
        PUSH_TYPE(res_type);
        ADD res { f_enc.one() };

        if (stype->is_monolithic()) {
            POP_DV(rhs, elems);
            POP_DV(lhs, elems);

            for (unsigned j = 0; j < elems; ++j) {
                res *= lhs[j].Equals(rhs[j]);
            }
        }

        else if (stype->is_algebraic()) {
            POP_DV(rhs, width * elems);
            POP_DV(lhs, width * elems);

            for (unsigned j = 0; j < elems; ++j) {
                dd::DDVector rhs_fragment;
                rhs_fragment.clear();

                dd::DDVector lhs_fragment;
                lhs_fragment.clear();

                for (unsigned k = 0; k < width; ++k) {
                    lhs_fragment.push_back(lhs[j * width + k]);
                    rhs_fragment.push_back(rhs[j * width + k]);
                }

                FRESH_DV(act, 1);
                InlinedOperatorDescriptor md {
                    make_ios(false, expr::EQ, width), act, lhs_fragment, rhs_fragment
                };
                f_inlined_operator_descriptors.push_back(md);

                res *= act[0];
            }
        }

        else {
            assert(false);
        }

        PUSH_DD(res);
    }

    void Compiler::array_ite(const expr::Expr_ptr expr)
    {
        POP_TYPE(rhs_type);
        POP_TYPE(lhs_type);
        POP_TYPE(cnd_type);

        const type::ArrayType_ptr rhs_atype { rhs_type->as_array() };
        unsigned rhs_width { rhs_atype->of()->width() };
        unsigned rhs_nelems { rhs_atype->nelems() };

        const type::ArrayType_ptr lhs_atype { lhs_type->as_array() };
        unsigned lhs_width { lhs_atype->of()->width() };
        unsigned lhs_nelems { lhs_atype->nelems() };

        assert(rhs_type->is_array() &&
               lhs_type->is_array() &&
               lhs_width == rhs_width &&
               lhs_nelems == rhs_nelems &&
               cnd_type->is_boolean());

        PUSH_TYPE(rhs_type);

        unsigned width(lhs_width * lhs_nelems);

        POP_DV(rhs, width);
        POP_DV(lhs, width);
        POP_DD(cnd);

        FRESH_DV(res, width);
        PUSH_DV(res, width);

        /* Register ITE MUX */
        expr::Expr_ptr parent { expr };
        BinarySelectionUnionFindMap::const_iterator eye { f_bsuf_map.find(expr) };

        if (f_bsuf_map.end() != eye) {
            parent = eye->second;
        }

        /* verify if entry for toplevel already exists. If it doesn't, create it */
        {
            Expr2BinarySelectionDescriptorsMap::const_iterator mi {
                f_expr2bsd_map.find(parent)
            };

            if (f_expr2bsd_map.end() == mi) {
                f_expr2bsd_map.insert(
                    std::pair<expr::Expr_ptr, BinarySelectionDescriptors>(parent, BinarySelectionDescriptors()));
            }
        }

        BinarySelectionDescriptor md {
            width, res, cnd, make_auto_dd(), lhs, rhs
        };

        {
            Expr2BinarySelectionDescriptorsMap::iterator mi {
                f_expr2bsd_map.find(parent)
            };

            assert(f_expr2bsd_map.end() != mi);
            mi->second.push_back(md);
        }
    }
} // namespace compiler

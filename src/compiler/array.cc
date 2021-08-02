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

#include <expr.hh>
#include <compiler.hh>

namespace compiler {

void Compiler::array_equals(const expr::Expr_ptr expr)
{
    const type::Type_ptr rhs_type
        (f_type_stack.back());
    f_type_stack.pop_back();

    const type::Type_ptr lhs_type
        (f_type_stack.back());

    assert( lhs_type -> is_array() &&
            rhs_type -> is_array());

    const type::ArrayType_ptr atype
        (rhs_type -> as_array());

    unsigned width
        (atype -> of() -> width());
    unsigned elems
        (atype -> nelems());

    POP_DV(rhs, width * elems);
    POP_DV(lhs, width * elems);

    ADD res
        (f_enc.one());

    for (unsigned j = 0; j < elems; ++ j) {

        /* extract fragments for LHS and RHS */
        dd::DDVector rhs_fragment;
        rhs_fragment.clear();

        dd::DDVector lhs_fragment;
        lhs_fragment.clear();

        for (unsigned k = 0; k < width; ++ k) {
            lhs_fragment.push_back(lhs[j * width + k]);
            rhs_fragment.push_back(rhs[j * width + k]);
        }

        FRESH_DV(act, 1);
        InlinedOperatorDescriptor md
            (make_ios( false, expr::EQ, width), act,
             lhs_fragment, rhs_fragment);

        f_inlined_operator_descriptors.push_back(md);

        DEBUG
            << "Registered "
            << md
            << std::endl;

        res *= act[0];
    }

    PUSH_DD(res);
}

void Compiler::array_ite(const expr::Expr_ptr expr)
{
    const type::Type_ptr rhs_type
        (f_type_stack.back());
    f_type_stack.pop_back();

    const type::Type_ptr lhs_type
        (f_type_stack.back());
    f_type_stack.pop_back();

    const type::Type_ptr cnd_type
        (f_type_stack.back());
    f_type_stack.pop_back();

    const type::ArrayType_ptr rhs_atype
        (rhs_type -> as_array());
    unsigned rhs_width
        (rhs_atype -> of() -> width());
    unsigned rhs_nelems
        (rhs_atype -> nelems());

    const type::ArrayType_ptr lhs_atype
        (lhs_type -> as_array());
    unsigned lhs_width
        (lhs_atype -> of() -> width());
    unsigned lhs_nelems
        (lhs_atype -> nelems());

    // both operands are algebraic, same width & nelems
    assert( rhs_type -> is_array() &&
            lhs_type -> is_array() &&
            cnd_type -> is_boolean() &&
            lhs_width == rhs_width &&
            lhs_nelems == rhs_nelems);

    f_type_stack.push_back( rhs_type );

    unsigned width
        (lhs_width * lhs_nelems);

    POP_DV(rhs, width);
    POP_DV(lhs, width);

    /* Fetch cnd DD */
    POP_DD(cnd);

    /* Push MUX output DD vector */
    FRESH_DV(res, width);
    PUSH_DV(res, width);

    /* Register ITE MUX */
    expr::Expr_ptr parent
        (expr);

    BinarySelectionUnionFindMap::const_iterator eye
        (f_bsuf_map.find( expr ));

    if (f_bsuf_map.end() != eye)
        parent = eye -> second;

    /* verify if entry for toplevel already exists. If it doesn't, create it */
    {
        Expr2BinarySelectionDescriptorsMap::const_iterator mi
            (f_expr2bsd_map.find(parent));

        if (f_expr2bsd_map.end() == mi)
            f_expr2bsd_map.insert( std::pair< expr::Expr_ptr, BinarySelectionDescriptors >
                                   (parent, BinarySelectionDescriptors()));
    }

    BinarySelectionDescriptor md
        (width, res, cnd, make_auto_dd(), lhs, rhs);

    /* Entry for toplevel does exist for sure */
    {
        Expr2BinarySelectionDescriptorsMap::iterator mi
            (f_expr2bsd_map.find(parent));
        assert( f_expr2bsd_map.end() != mi );

        mi -> second.push_back( md );
    }

    DEBUG
        << "Registered "
        << md
        << std::endl;
}

} // namespace compiler

/**
 *  @file array.cc
 *  @brief Boolean compiler
 *
 *  Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU Lesser General Public
 *  License as published by the Free Software Foundation; either
 *  version 2.1 of the License, or (at your option) any later version.
 *
 *  This library is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public
 *  License along with this library; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/
#include <common.hh>

#include <expr.hh>
#include <compiler.hh>

void Compiler::array_equals(const Expr_ptr expr)
{
    const Type_ptr rhs_type = f_type_stack.back(); f_type_stack.pop_back();
    const Type_ptr lhs_type = f_type_stack.back();

    assert( lhs_type -> is_array() &&
            rhs_type -> is_array() );

    const ArrayType_ptr atype = rhs_type -> as_array();

    unsigned width = atype -> of() -> width();
    unsigned elems = atype -> nelems();

    POP_DV(rhs, width * elems);
    POP_DV(lhs, width * elems);

    ADD res = f_enc.one();
    for (unsigned j = 0; j < elems; ++ j) {

        /* extract fragments for LHS and RHS */
        DDVector rhs_fragment; rhs_fragment.clear();
        DDVector lhs_fragment; lhs_fragment.clear();
        for (unsigned k = 0; k < width; ++ k) {
            lhs_fragment.push_back(lhs[j * width + k]);
            rhs_fragment.push_back(rhs[j * width + k]);
        }

        FRESH_DV(act, 1);
        InlinedOperatorDescriptor md
            (make_ios( false, EQ, width), act,
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


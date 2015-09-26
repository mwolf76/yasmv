/**
 *  @file enumerative.cc
 *  @brief Boolean compiler - enumerative manipulations
 *
 *  This module contains definitions and services that implement the
 *  booolean expressions compilation into a form which is suitable for
 *  the SAT analysis. Current implementation uses ADDs to perform
 *  expression manipulation and booleanization. Expressions are
 *  assumed to be type-safe, only boolean expressions on arithmetic
 *  predicates are supported. The final result of expression
 *  compilation must be a 0-1 ADD which is suitable for CNF clauses
 *  injection directly into the SAT solver. The compilation engine is
 *  implemented using a simple walker pattern: (a) on preorder, return
 *  true if the node has not yet been visited; (b) always do in-order
 *  (for binary nodes); (c) perform proper compilation in post-order
 *  hooks.
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

void Compiler::enumerative_equals(const Expr_ptr expr)
{
    POP_DD(rhs);
    POP_DD(lhs);
    PUSH_DD(lhs.Equals(rhs));

    f_type_stack.pop_back(); // consume one, leave the other
}

void Compiler::enumerative_not_equals(const Expr_ptr expr)
{
    POP_DD(rhs);
    POP_DD(lhs);
    PUSH_DD(lhs.Equals(rhs).Cmpl());

    f_type_stack.pop_back(); // consume one, leave the other
}

void Compiler::enumerative_ite(const Expr_ptr expr)
{
    POP_DD(rhs);
    POP_DD(lhs);
    POP_DD(cnd);
    PUSH_DD(cnd.Ite(lhs, rhs));

    // consume all, push rhs type
    Type_ptr type = f_type_stack.back();
    f_type_stack.pop_back();
    f_type_stack.pop_back();
    f_type_stack.pop_back();
    f_type_stack.push_back(type);
}

void Compiler::enumerative_subscript(const Expr_ptr expr)
{
    EncodingMgr& bm
        (f_enc);

    // index
    Type_ptr t0
        (f_type_stack.back());
    f_type_stack.pop_back(); // consume index
    assert(t0 -> is_algebraic());

    Type_ptr itype
        (t0 -> as_algebraic());
    unsigned iwidth
        (itype -> width());

    POP_DV(index, iwidth);
    assert(iwidth == bm.word_width()); // needed?

    // array
    Type_ptr t1
        (f_type_stack.back());
    f_type_stack.pop_back(); // consume array
    assert(t1 -> is_array());

    ArrayType_ptr atype
        (t1 -> as_array());
    ScalarType_ptr type
        (atype -> of());
    assert(type -> is_enum());

    unsigned elem_width
        (type -> width());
    assert(elem_width == 1);
    unsigned elem_count
        (atype -> nelems());
    POP_DV(lhs, elem_width * elem_count);

    /* Build selection DDs */
    DDVector cnd_dds;
    DDVector act_dds;
    unsigned j_, j = 0; do {

        unsigned i;
        ADD cnd
            (bm.one());

        i = 0; j_ = j; while (i < iwidth) {
            ADD bit
                ((j_ & 1) ? bm.one() : bm.zero());
            unsigned ndx
                (iwidth - i - 1);
            j_ >>= 1;

            cnd *= index[ ndx ].Xnor(bit);
            ++ i;
        }

        cnd_dds.push_back(cnd);
        act_dds.push_back(make_auto_dd());
    } while (++ j < elem_count);

    /* Push MUX output DD vector */
    FRESH_DV(dv, elem_width);
    PUSH_DV(dv, elem_width);

    PUSH_TYPE(type);

    MultiwaySelectionDescriptor msd
        (elem_width, elem_count, dv, cnd_dds, act_dds, lhs);

    f_multiway_selection_descriptors.push_back(msd);

    DEBUG
        << "Registered " << msd
        << std::endl;
}

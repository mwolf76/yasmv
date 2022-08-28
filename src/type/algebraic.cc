/**
 * @file algebraic.cc
 * @brief Algebraic type classes implementation
 *
 * This module contains the implementation for Alegbraic type classes.
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

#include <type.hh>
#include <type_mgr.hh>

namespace type {

    unsigned ConstantType::width() const
    {
        assert(0 != f_width);
        return f_width;
    }

    ConstantType::ConstantType(TypeMgr& owner, unsigned width)
        : AlgebraicType(owner)
        , f_width(width)
    {
        f_repr = f_owner.em().make_const_int_type(width);
    }

    SignedAlgebraicType::SignedAlgebraicType(TypeMgr& owner,
                                             unsigned width,
                                             ADD* dds)
        : AlgebraicType(owner)
        , f_width(width)
        , f_dds(dds)
    {
        f_repr = f_owner.em().make_signed_int_type(width);
    }

    unsigned SignedAlgebraicType::width() const
    {
        assert(0 != f_width);
        return f_width;
    }

    UnsignedAlgebraicType::UnsignedAlgebraicType(TypeMgr& owner,
                                                 unsigned width,
                                                 ADD* dds)
        : AlgebraicType(owner)
        , f_width(width)
        , f_dds(dds)
    {
        f_repr = f_owner.em().make_unsigned_int_type(width);
    }

    unsigned UnsignedAlgebraicType::width() const
    {
        assert(0 != f_width);
        return f_width;
    }

    // -- Arrays ------------------------------------------------------------
    ArrayType::ArrayType(TypeMgr& owner, ScalarType_ptr of, unsigned nelems)
        : Type(owner)
        , f_of(of)
        , f_nelems(nelems)
    {
        // 0 is reserved for abstract arrays
        assert(0 < nelems);

        // valid type
        assert(NULL != of);

        // scalar type, only. Make sure we know how to calculate size()
        assert(f_of->is_scalar());

        f_repr = f_owner.em().make_subscript(of->repr(),
                                             f_owner.em().make_const(nelems));
    }

    unsigned ArrayType::width() const
    {
        assert(0 != f_nelems);
        return f_nelems * f_of->width();
    }

}; // namespace type

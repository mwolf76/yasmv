/**
 * @file array.cc
 * @brief Array type class implementation
 *
 * This module contains the implementation for the Array type class.
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

    ArrayType::ArrayType(TypeMgr& owner, ScalarType_ptr of, unsigned nelems)
        : Type(owner)
        , f_of(of)
        , f_nelems(nelems)
    {
	TypeMgr& tm { f_owner };
	expr::ExprMgr& em { tm.em() };

        // 0 is reserved for abstract arrays
        assert(0 < nelems);

        // valid type
        assert(NULL != of);

        // scalar types only allowed here. Make sure we know how to calculate size()
        assert(f_of->is_scalar());

        f_repr = em.make_subscript(of->repr(),
				   em.make_const(nelems));
    }

    unsigned ArrayType::width() const
    {
        assert(0 != f_nelems);
        return f_nelems * f_of->width();
    }

} // namespace type

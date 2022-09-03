/**
 * @file unit.cc
 * @brief Expression compiler subsystem, output unit classes implementation.
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

#include <compiler/streamers.hh>
#include <compiler/typedefs.hh>

#include <type/type.hh>

namespace compiler {

    InlinedOperatorDescriptor::InlinedOperatorDescriptor(InlinedOperatorSignature ios,
                                                         dd::DDVector& z, dd::DDVector& x)
        : f_ios(ios)
        , f_z(z)
        , f_x(x)
    {}

    InlinedOperatorDescriptor::InlinedOperatorDescriptor(InlinedOperatorSignature ios,
                                                         dd::DDVector& z, dd::DDVector& x, dd::DDVector& y)
        : f_ios(ios)
        , f_z(z)
        , f_x(x)
        , f_y(y)
    {}

    BinarySelectionDescriptor::BinarySelectionDescriptor(unsigned width, dd::DDVector& z,
                                                         ADD cnd, ADD aux, dd::DDVector& x, dd::DDVector& y)
        : f_width(width)
        , f_z(z)
        , f_cnd(cnd)
        , f_aux(aux)
        , f_x(x)
        , f_y(y)
    {}

    MultiwaySelectionDescriptor::MultiwaySelectionDescriptor(unsigned elem_width,
                                                             unsigned elem_count,
                                                             dd::DDVector& z, dd::DDVector& cnds,
                                                             dd::DDVector& acts, dd::DDVector& x)
        : f_elem_width(elem_width)
        , f_elem_count(elem_count)
        , f_z(z)
        , f_cnds(cnds)
        , f_acts(acts)
        , f_x(x)
    {}

    long InlinedOperatorSignatureHash::operator()(const InlinedOperatorSignature& k) const
    {
        const long prime = 31;

        long res = 1;
        res = prime * res + (k.get<0>() ? 1231 : 1237);
        res = prime * res + k.get<1>();
        res = prime * res + k.get<2>();

        return res;
    }

    bool InlinedOperatorSignatureEq::operator()(const InlinedOperatorSignature& x,
                                                const InlinedOperatorSignature& y) const
    {
        return x.get<0>() == y.get<0>() &&
               x.get<1>() == y.get<1>() &&
               x.get<2>() == y.get<2>();
    }

} // namespace compiler

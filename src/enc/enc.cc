/**
 * @file enc.cc
 * @brief Encoding subsystem implementation.
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

#include <enc/enc.hh>

namespace enc {

// shared dctor
Encoding::~Encoding()
{}

// low-level service for bits allocation
ADD Encoding::make_bit()
{
    ADD res = f_mgr.bit();

    /* keep track of every bit in the encoding, this is used later,
       when evaluating the scalar value of a bit combination. */
    f_bits.push_back(res);

    return res;
}

// base service, has to be in superclass for visibility
ADD Encoding::make_monolithic_encoding(unsigned nbits)
{
    ADD res = make_bit();
    ADD two = f_mgr.constant(2);

    assert(0 < nbits);
    unsigned i = 1;

    while (i < nbits) {
        res *= two;
        res += make_bit();

        ++ i;
    }

    return res;
}

};

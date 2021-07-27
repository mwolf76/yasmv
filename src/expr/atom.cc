/**
 * @file atom.cc
 * @brief Expression management, pooling subsystem implementation.
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
#include <atom.hh>

namespace expr {

long AtomHash::operator() (const Atom& k) const
{
    unsigned long hash = 0;
    unsigned long x    = 0;

    for (std::size_t i = 0; i < k.length(); i++) {

        hash = (hash << 4) + k[i];
        if((x = hash & 0xF0000000L) != 0) {
            hash ^= (x >> 24);
        }
        hash &= ~x;
    }

    return hash;
}

bool AtomEq::operator() (const Atom& x, const Atom& y) const
{
    return x == y;
}

};

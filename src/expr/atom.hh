/**
 *  @file atom.hh
 *  @brief Atomession management
 *
 *  This module contains definitions and services that implement an
 *  optimized storage for atoms. Atoms are stored in a Directed
 *  Acyclic Graph (DAG) for data sharing.
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
#ifndef ATOM_H
#define ATOM_H

// using STL string as basic atom class
typedef string Atom;
typedef Atom* Atom_ptr;

// Atom pool
struct AtomHash {
    long operator() (const Atom& k) const
    {
        unsigned long hash = 0;
        unsigned long x    = 0;

        for(std::size_t i = 0; i < k.length(); i++)
            {
                hash = (hash << 4) + k[i];
                if((x = hash & 0xF0000000L) != 0)
                    {
                        hash ^= (x >> 24);
                    }
                hash &= ~x;
            }

        return hash;
    }
};

struct AtomEq {
    bool operator() (const Atom& x, const Atom& y) const
    { return x == y; }
};

typedef unordered_set<Atom, AtomHash, AtomEq> AtomPool;
typedef pair<AtomPool::iterator, bool> AtomPoolHit;

#endif

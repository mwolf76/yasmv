/**
 *  @file atom.hh
 *  @brief Expression management
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
#ifndef ATOM_POOL_H
#define ATOM_POOL_H

#include <string>
#include <boost/unordered_set.hpp>

/* using STL string as basic atom class */
typedef std::string Atom;
typedef Atom* Atom_ptr;

struct AtomHash {
    long operator() (const Atom& k) const;
};

struct AtomEq {
    bool operator() (const Atom& x, const Atom& y) const;
};

typedef boost::unordered_set<Atom, AtomHash, AtomEq> AtomPool;
typedef std::pair<AtomPool::iterator, bool> AtomPoolHit;

#endif

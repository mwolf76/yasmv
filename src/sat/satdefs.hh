/**
 *  @file defs.hh
 *  @brief DEFS interface
 *
 *  This module contains the interface for services that implement an
 *  CNF clauses generation in a form that is suitable for direct
 *  injection into the SAT solver.
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
#ifndef DEFS_H
#define DEFS_H
#include <common.hh>
#include <SolverTypes.hh>

namespace Minisat {

    typedef unsigned id_t;

    typedef enum {
        STATUS_SAT,
        STATUS_UNSAT,
        STATUS_UNKNOWN,
    } status_t;

    // move me!
    template<class K>
    struct ptr_hasher  {
        uint32_t operator()(const K& k) const {
            return (uint32_t)(reinterpret_cast<size_t>(k));
        }
    };

    // formulae groups
    typedef class Group* Group_ptr;
    class Group {
        id_t f_id;

    public:
        Group(id_t id)
            : f_id(id)
        {}

        inline id_t id()
        { return f_id; }
    };
    typedef vector<Group> Groups;
    static Group MAINGROUP(0);

    // interpolation colors
    typedef class Color* Color_ptr;
    class Color {
        id_t f_id;

    public:
        Color(id_t id)
            : f_id(id)
        {}

        inline id_t id()
        { return f_id; }
    };
    typedef vector<struct Color> Colors;
    static Color BACKGROUND(0);

    typedef vector<Var> Variables;
    typedef vector<Lit> Literals;
};

#endif

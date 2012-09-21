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
#include <Set.hh>
#include <cuddObj.hh>

namespace Minisat {

    typedef unsigned id_t;

    typedef enum {
        STATUS_SAT,
        STATUS_UNSAT,
        STATUS_UNKNOWN,
    } status_t;

    ostream& operator<<(ostream& os, status_t status);

    // move me!
    template<class K>
    struct ptr_hasher  {
        uint32_t operator()(const K& k) const {
            return (uint32_t)(reinterpret_cast<size_t>(k));
        }
    };

    // // formulae groups
    // typedef class Group* Group_ptr;
    // class Group {
    //     id_t f_id;

    // public:
    //     Group(id_t id)
    //         : f_id(id)
    //     {}

    //     inline id_t id()
    //     { return f_id; }
    // };
    // typedef Set<Group> Groups;
    // static Group MAINGROUP(0);
    typedef unsigned group_t;
    static group_t MAINGROUP(0);
    typedef Set<group_t> Groups;

    // interpolation colors
    // typedef class Color* Color_ptr;
    // class Color {
    //     id_t f_id;

    // public:
    //     Color(id_t id)
    //         : f_id(id)
    //     {}

    //     inline id_t id()
    //     { return f_id; }
    // };
    // typedef Set<struct Color> Colors;
    // static Color BACKGROUND(0);
    typedef unsigned color_t;
    static color_t BACKGROUND(0);
    typedef Set<color_t> Colors;

    typedef vector<Var> Variables;
    typedef vector<Lit> Literals;

    typedef ADD Term;
    typedef unordered_set<ADD> Terms;

    // this CNFization algorithm requires Term to be 0-1 ADDs
    struct TermHash {
        inline long operator() (Term term) const
        {
            DdNode *tmp = term.getRegularNode();
            return (long) (tmp);
        }
    };
    struct TermEq {
        inline bool operator() (const Term phi,
                                const Term psi) const
        { return phi == psi; }
    };
    typedef unordered_map<Term, Var, TermHash, TermEq> Term2VarMap;

    struct VarHash {
        inline long operator() (Var v) const
        { return (long) (v); }
    };
    struct VarEq {
        inline bool operator() (const Var x,
                                const Var y) const
        { return x == y; }
    };
    typedef unordered_map<Var, Term, VarHash, VarEq> Var2TermMap;

    struct GroupHash {
        inline long operator() (group_t group) const
        { return (long) (group); }
    };
    struct GroupEq {
        inline bool operator() (const group_t x,
                                const group_t y) const
        { return x == y; }
    };
    typedef unordered_map<group_t, Var, GroupHash, GroupEq> Group2VarMap;
};

#endif

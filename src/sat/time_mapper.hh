/**
 *  @file time_mapper.hh
 *  @brief SAT interface (Time Mapper sub-component)
 *
 *  This module contains the interface for services that implement the
 *  Time Mapper. This service is used to keep a bidirectional mapping
 *  between Timed Canonical Bit Identifiers (or TCBIs) and actual
 *  Minisat Variables.
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
#ifndef SAT_TIME_MAPPER_H
#define SAT_TIME_MAPPER_H

#include <expr.hh>
#include <pool.hh>

#include <common.hh>

#include "core/SolverTypes.hh"

namespace Minisat {

    class SAT; // fwd decl

    typedef unordered_map<TCBI, Var, TCBIHash, TCBIEq> TCBI2VarMap;
    typedef unordered_map<Var, TCBI, IntHash, IntEq> Var2TCBIMap;

    class TimeMapper : public IObject {

        /* ctor and dctor are available only to SAT owner */
        friend class SAT;

    public:
        Var var(const TCBI& tcbi );
        const TCBI& tcbi( Var var );

    private:
        TimeMapper(SAT& owner);
        ~TimeMapper();

        SAT& f_owner;

        /* Bidirectional mapping */
        TCBI2VarMap f_tcbi2var_map;
        Var2TCBIMap f_var2tcbi_map;
    };

}; /* namespace */

#endif

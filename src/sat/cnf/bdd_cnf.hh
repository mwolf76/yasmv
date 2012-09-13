/**
 *  @file bdd_cnf.hh
 *  @brief CNF clauses generation and injection
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
#ifndef BDD_CNFIZER_H
#define BDD_CNFIZER_H
#include "sat.hh"

namespace Minisat {

    class BDDSAT;
    class BDDCNFizer : public CNFizer<BDD> {
    public:
        virtual void push(BDD phi, const Group& group, const Color& color);

        BDDCNFizer(BDDSAT& owner);
        ~BDDCNFizer();
    };
}

#endif
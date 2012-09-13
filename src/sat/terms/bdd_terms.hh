/**
 *  @file bdd_terms.hh
 *  @brief Generic bddterms support
 *
 *  This module contains the definitions for terms manipulation,
 *  specialized for cudd BDDs.
 *
 *  Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the bddterms of the GNU Lesser General Public
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
#ifndef BDD_TERMS_H_INCLUDED
#define BDD_TERMS_H_INCLUDED
#include "terms/terms.hh"
#include <cuddObj.hh>  // BDD Term implementantion

namespace Minisat {

    class BDDTermFactory : public TermFactory<BDD> {
    public:
        BDDTermFactory(Cudd& cudd)
            : f_cudd(cudd)
        {}

        virtual ~BDDTermFactory() {};

        // constants
        virtual BDD make_true()
        { return f_cudd.bddOne(); }
        virtual bool is_true(BDD t)
        { return f_cudd.bddIsOne(t); }

        virtual BDD make_false()
        { return f_cudd.bddZero(); }
        virtual BDD is_false(BDD t)
        { return f_cudd.bddIsZero(t); }

        // variables
        virtual BDD make_var(Var v)
        { return f_cudd.bddVar(v); }

        // operators
        virtual BDD make_and(BDD t1, BDD t2)
        { return t1 & t2; }
        virtual BDD make_or(BDD t1, BDD t2)
        { return t1 | t2; }

        virtual BDD make_not(BDD t)
        { return ~ t; }

    private:
        Cudd& f_cudd;
    };

} // namespace Minisat

#endif

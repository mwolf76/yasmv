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
#include <cudd.hh>     // Cudd capsule
#include <cuddObj.hh>  // BDD Term implementantion
#include <cuddInt.h>

namespace Minisat {

    class BDDTermFactory : public TermFactory<BDD> {
    public:
        BDDTermFactory(Cudd& cudd)
            : f_cudd(cudd)
        {
            TRACE << "Initialized BDD Term Factory @ " << this << endl;
        }

        virtual ~BDDTermFactory()
        {
            TRACE << "Deinitialized BDD Term Factory @ " << this << endl;
        };

        // constants
        virtual BDD make_true()
        { return f_cudd.bddOne(); }
        virtual bool is_true(BDD bdd)
        { return bdd.IsOne(); }

        virtual BDD make_false()
        { return f_cudd.bddZero(); }
        virtual bool is_false(BDD bdd)
        { return bdd.IsZero(); }

        // variables
        virtual BDD make_var(Var v)
        { return f_cudd.bddVar(v); }

        // operators
        virtual BDD make_and(BDD a, BDD b)
        { return a & b; }
        virtual BDD make_or(BDD a, BDD b)
        { return a | b; }

        virtual BDD make_not(BDD a)
        { return ~ a; }

        virtual BDD make_then(BDD a)
        {
            DdNode *node = a.getRegularNode();
            assert (! cuddIsConstant(node));
            return BDD( f_cudd, cuddT(node));
        }
        virtual BDD make_else(BDD a)
        {
            DdNode *node = a.getRegularNode();
            assert (! cuddIsConstant(node));
            return BDD( f_cudd, cuddE(node));
        }

    private:
        Cudd& f_cudd;
    };

} // namespace Minisat

#endif

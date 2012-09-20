/**
 *  @file bdd_terms.hh
 *  @brief Generic bddterms support
 *
 *  This module contains the definitions for terms manipulation,
 *  specialized for cudd ADDs.
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
#ifndef ADD_TERMS_H_INCLUDED
#define ADD_TERMS_H_INCLUDED
#include "terms/terms.hh"
#include <cudd.hh>     // Cudd capsule
#include <cuddObj.hh>  // ADD Term implementantion
#include <cuddInt.h>

namespace Minisat {

    class ADDTermFactory : public TermFactory<ADD> {
    public:
        ADDTermFactory(Cudd& cudd)
            : f_cudd(cudd)
        { TRACE << "Initialized ADD Term Factory @ " << this << endl; }

        virtual ~ADDTermFactory()
        { TRACE << "Deinitialized ADD Term Factory @ " << this << endl; }

        // constants
        virtual ADD make_true()
        { return f_cudd.addOne(); }
        virtual bool is_true(ADD phi)
        { return phi.IsOne(); }

        virtual ADD make_false()
        { return f_cudd.addZero(); }
        virtual bool is_false(ADD phi)
        { return phi.IsZero(); }

        // variables
        virtual ADD make_var(Var v)
        { return f_cudd.addVar(v); }

        // operators
        virtual ADD make_and(ADD phi, ADD psi)
        { return phi & psi; }
        virtual ADD make_or(ADD phi, ADD psi)
        { return phi | psi; }

        virtual ADD make_not(ADD phi)
        { return ~ phi; }

        virtual ADD make_then(ADD phi)
        {
            DdNode *node = phi.getRegularNode();
            assert (! cuddIsConstant(node));
            return ADD( f_cudd, cuddT(node));
        }
        virtual ADD make_else(ADD phi)
        {
            DdNode *node = phi.getRegularNode();
            assert (! cuddIsConstant(node));
            return ADD( f_cudd, cuddE(node));
        }

    private:
        Cudd& f_cudd;
    };

} // namespace Minisat

#endif

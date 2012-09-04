/**
 *  @file addterms.hh
 *  @brief Generic addterms support
 *
 *  This module contains the definitions for terms manipulation,
 *  specialized for cudd ADDs.
 *
 *  Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the addterms of the GNU Lesser General Public
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
namespace Minisat {

    class ADDTermFactory : public TermFactory<ADD> {
    public:
        ADDTermFactory(Cudd& cudd)
            : f_cudd(cudd)
        {}

        virtual ~ADDTermFactory() {};

        // constants
        virtual ADD make_true()
        { return f_cudd.addOne(); }

        virtual ADD make_false()
        { return f_cudd.addZero(); }

        // variables
        virtual ADD make_var(Var v)
        { return f_cudd.addVar(v); }

        // operators
        virtual ADD make_and(ADD t1, ADD t2)
        { return t1 & t2; }
        virtual ADD make_or(ADD t1, ADD t2)
        { return t1 | t2; }

        virtual ADD make_not(ADD t)
        { return ~ t; }

    private:
        Cudd& f_cudd;
    };

} // namespace Minisat

#endif

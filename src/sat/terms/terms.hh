#if 0

/**
 * @file terms.hh
 * @brief Generic terms support
 *
 * This module contains the definitions for abstract terms
 * manipulation.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA
 *
 **/

#ifndef TERMS_H_INCLUDED
#define TERMS_H_INCLUDED

namespace Minisat {

    template<class Term> class TermFactory {

    public:
        virtual ~TermFactory() {};

        // constants (makers and predicates)
        virtual Term make_true() =0;
        virtual bool is_true(Term t) =0;

        virtual Term make_false() =0;
        virtual bool is_false(Term t) =0;

        // variables
        virtual Term make_var(Var v) =0;

        // operators
        virtual Term make_and(Term t1, Term t2) =0;
        virtual Term make_or(Term t1, Term t2) =0;
        virtual Term make_not(Term t) =0;
    };

} // namespace Minisat

#endif /* TERMS_H_INCLUDED */

#endif

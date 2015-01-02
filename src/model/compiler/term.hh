/**
 *  @file term.hh
 *  @brief Engine-compatible propositional expression
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

#ifndef TERM_H
#define TERM_H

#include <dd_walker.hh>
#include <micro.hh>

class Term {
public:
    Term()
        : f_formula()
        , f_descriptors()
    {}

    Term(DDVector& formula, MicroDescriptors& descriptors)
        : f_formula(formula)
        , f_descriptors(descriptors)
    {}

    inline const DDVector& formula() const
    { return f_formula; }

    inline const MicroDescriptors& descriptors() const
    { return f_descriptors; }

private:
    DDVector f_formula;
    MicroDescriptors f_descriptors;
};
typedef vector<Term> Terms;

#endif

/**
 *  @file interpolator.hh
 *  @brief Craig interpolation
 *
 *  This module contains the definitions for Craig
 *  interpolation-related interfaces and classes.
 *
 *  Authors: Alberto Griggio, Marco Pensallorto
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
#ifndef BDD_INTERPOLATOR_H_INCLUDED
#define BDD_INTERPOLATOR_H_INCLUDED
#include "sat.hh"

namespace Minisat {

    // the owner instance type (fwd decl)
    class BDDSAT;

    class BDDInterpolator : public Interpolator<BDD>
    {
    public:
        BDDInterpolator(BDDSAT& owner);
        ~BDDInterpolator();
    };

}

#endif // BDD_INTERPOLATOR_H_INCLUDED

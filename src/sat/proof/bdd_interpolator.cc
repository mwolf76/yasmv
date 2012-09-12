/**
 *  @file bdd_interpolator.cc
 *  @brief Craig interpolation implementation
 *
 *  This module contains the definitions for Craig
 *  interpolation-related interfaces and classes.
 *
 *  Authors: Marco Pensallorto
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
#include "bdd_interpolator.hh"
#include "bdd_sat.hh"

namespace Minisat {

    BDDInterpolator::BDDInterpolator(BDDSAT& owner)
        : Interpolator<BDD>(dynamic_cast<SAT<BDD> &>(owner))
    {}

    // BDDInterpolator::BDDInterpolator(SAT<BDD>& owner)
    //     : Interpolator<BDD>(owner)
    // { TRACE << "Initialized BDD interpolator instance @" << this << endl; }

    BDDInterpolator::~BDDInterpolator()
    {
        // Cache elements needs no cleanup here because allocated memory
        // belongs to the term factory, thus it is its own responsibility
        // to free it.
    }

} // namespace Minisat

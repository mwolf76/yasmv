/**
 *  @file sat.cc
 *  @brief SAT interface implementation
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
#include "bdd_sat.hh"
#include "cnf/bdd_cnf.hh"
#include "proof/bdd_interpolator.hh"
#include "model/bdd_model.hh"

namespace Minisat {

    BDDSAT::BDDSAT(BDDTermFactory& factory)
        : f_solver()
        , f_factory(&factory)
        , f_cnfizer(new BDDCNFizer(*this))
        , f_interpolator(new BDDInterpolator((*this)))
        , f_model_extractor(new BDDModelExtractor(*this))
        , f_next_group(0)
        , f_next_color(0)
    {}

    Group& BDDSAT::new_group()
    {
        Group_ptr res = new Group( ++ f_next_group );
        f_groups.push_back(*res);

        return *res;
    }

    Groups& BDDSAT::groups()
    { return f_groups; }

    Color& BDDSAT::new_color()
    {
        Color_ptr res = new Color( ++ f_next_color );
        f_colors.push_back(*res);

        return *res;
    }

    Colors& BDDSAT::colors()
    { return f_colors; }

    void BDDSAT::push(BDD phi, Group& group, Color& color)
    {
        f_cnfizer->push(phi, group, color);
    }

    void BDDSAT::solve()
    {
    }

    void BDDSAT::solve(const Groups& groups)
    {
    }

    status_t BDDSAT::status()
    {
    }

    BDD BDDSAT::model()
    {
    }

    BDD BDDSAT::interpolate(const Colors& a)
    {
    }

};

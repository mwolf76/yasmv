/**
 *  @file MC Algorithm.cc
 *  @brief MC Algorithm
 *
 *  This module contains definitions and services that implement an
 *  optimized storage for expressions. Expressions are stored in a
 *  Directed Acyclic Graph (DAG) for data sharing.
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
#include <mc.hh>
using namespace Minisat;

MCAlgorithm::MCAlgorithm(IModel& model, Expr_ptr property)
    : Algorithm(model)
    , f_property(property)
    , f_witness(NULL)
{
    set_param("alg_name", "test");
    DEBUG  << "Creating MC algoritm instance "
           << get_param("alg_name")
           << " @" << this
           << endl;

    /* pre-compilation */
    prepare();
}

MCAlgorithm::~MCAlgorithm()
{
    DEBUG << "Destroying MC algoritm instance"
          << get_param("alg_name")
          << " @" << this
          << endl;
}

mc_status_t MCAlgorithm::status() const
{ return f_status; }

bool MCAlgorithm::has_witness() const
{ return NULL != f_witness; }

Witness& MCAlgorithm::get_witness() const
{
    assert (has_witness());
    return *f_witness;
}

void MCAlgorithm::set_status(mc_status_t status)
{ f_status = status; }

void MCAlgorithm::prepare()
{
    /* Invariant */
    f_invariant_add = compiler().process( em().make_main(), f_property);

    /* Violation (negation of Invarion) */
    f_violation_add = compiler().process( em().make_main(),
                                          em().make_not( f_property));
}

void MCAlgorithm::assert_violation(step_t time, group_t group, color_t color)
{
    // TODO: macro to wrap code to be benchmarked (cool!)
    clock_t t0 = clock();
    TRACE << "CNFizing Violation @"
          << time << endl;

    engine().push( f_violation_add, time, group, color);

    clock_t elapsed = clock() - t0;
    double secs = (double) elapsed / (double) CLOCKS_PER_SEC;
    TRACE << "Done. (took " << secs << " seconds)" << endl;
}

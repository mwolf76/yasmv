/**
 *  @file solver.cc
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
#include <sat.hh>
#include <cstdlib>

/**
 * @brief SAT instancte ctor
 */
SAT::SAT()
    : f_enc_mgr(EncodingMgr::INSTANCE())
    , f_mapper(* new TimeMapper(*this))
    , f_registry(* new CNFRegistry(*this))
    , f_solver()
{
    /* MAINGROUP (=0) is already there. */
    f_groups.push(new_sat_var());

    DEBUG
        << "Initialized SAT instance @" << this
        << endl;
}

status_t SAT::sat_solve_groups(const Groups& groups)
{
    vec<Lit> assumptions;

    clock_t t0 = clock();
    for (int i = 0; i < groups.size(); ++ i) {
        Var grp = groups[i];

        /* Assumptions work like "a -> phi", thus a non-negative
           value enables group, whereas a negative value disables it. */
        assumptions.push( mkLit( abs(grp), grp < 0));
    }

    DEBUG
        << "Solving with following assumptions..."
        << assumptions
        << endl;

    f_status = f_solver.solve(assumptions)
        ? STATUS_SAT
        : STATUS_UNSAT
        ;

    clock_t elapsed = clock() - t0;
    double secs = (double) elapsed / (double) CLOCKS_PER_SEC;

    DEBUG
        << "Took "
        << secs
        << " seconds. Status is "
        << f_status << "."
        << endl;

    return f_status;
}

void SAT::push(CompilationUnit cu, step_t time, group_t group)
{
    /* push DDs */
    {
        const DDVector& dv( cu.dds());
        unsigned n = dv.size();
        DEBUG
            << "CNFizing " << n
            << " fragments"
            << endl;

        DDVector::const_iterator i;
        for (i = dv.begin(); dv.end() != i; ++ i) {
            // TODO: additional CNF algorithms
            cnf_push_single_cut( *i, time, group );
        }
    }

    /* push microcode */
    {
        const MicroDescriptors& micro_descriptors (cu.micro_descriptors());
        unsigned n = micro_descriptors.size();
        DEBUG
            << "Injecting " << n
            << " microcode instances"
            << endl;

        MicroDescriptors::const_iterator i;
        for (i = micro_descriptors.begin(); micro_descriptors.end() != i; ++ i)  {
            cnf_inject_microcode( *i, time, group );
        }
    }

    /* push muxes */
    {
        const MuxDescriptors& mux_descriptors (cu.mux_descriptors());
        unsigned n = mux_descriptors.size();
        DEBUG
            << "Injecting " << n
            << " MUX instances"
            << endl;

        MuxDescriptors::const_iterator i;
        for (i = mux_descriptors.begin(); mux_descriptors.end() != i; ++ i)  {
            cnf_inject_muxcode( *i, time, group );
        }
    }
}

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

namespace Minisat {

    status_t SAT::sat_solve_groups(const Groups& groups)
    {
        clock_t t0 = clock();
        TRACE << "Solving ... " << endl;

        vec<Lit> assumptions;

        // MTL Set interface is a bit clumsy here :-/
        int bckt, bckts = groups.bucket_count();
        for (bckt = 0; bckt < bckts ; ++ bckt) {
            const vec<group_t>& gs = groups.bucket(bckt);
            for (int i = 0; i < gs.size(); ++ i) {
                assumptions.push(mkLit(gs[i], false)); // a -> phi
            }
        }

        f_status = f_solver.solve(assumptions)
            ? STATUS_SAT
            : STATUS_UNSAT
            ;

        clock_t elapsed = clock() - t0;
        double secs = (double) elapsed / (double) CLOCKS_PER_SEC;
        TRACE << "Took " << secs << " seconds. Status is " << f_status << "." << endl;

        return f_status;
    }

};

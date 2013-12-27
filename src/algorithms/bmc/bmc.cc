/**
 *  @file MC Algorithm.hh
 *  @brief SAT BMC Algorithm
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
#include <bmc/bmc.hh>

BMC::BMC(IModel& model, Expr_ptr property)
    : MCAlgorithm(model, property)
{
}

BMC::~BMC()
{}

void BMC::process()
{
    step_t k = 0; // to infinity...
    bool leave = false; // TODO: somebody telling us to stop

    assert_fsm_init(0);
    assert_violation(0, engine().new_group());

    TRACE << "Looking for a BMC CEX of length 0" << endl;
    if (STATUS_UNSAT == engine().solve()) {

        do {
            /* TODO: tell the children last valid k */

            /* disable last violation */
            engine().toggle_last_group();

            assert_fsm_trans(k ++);
            assert_violation(k, engine().new_group());

            TRACE << "Looking for a BMC CEX of length "
                  << k << endl;

        } while (STATUS_UNSAT == engine().solve() && ! leave);
    }

    if (STATUS_SAT == engine().status()) {
        set_status(MC_FALSE);

        TRACE << "Found BMC CEX witness (k = " << k
              << "), invariant is FALSE." << endl;

        /* CEX extraction */
        ostringstream oss; oss << "CEX for '"
                               << property() << "'";

        // Witness& trace = * new BMCCounterExample(property(), model(),
        //                                          engine(), k, false);

        // TODO: register
    }

    TRACE << "Done." << endl;
}

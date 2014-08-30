/**
 *  @file bmc.cc
 *  @brief SAT-based BMC Algorithms for property checking
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
    : Algorithm(model)
    , f_property(property)
{
    Analyzer analyzer( ModelMgr::INSTANCE());
    f_strategy = analyzer.process( property);
    if (f_strategy == PURE_PROPOSITIONAL) {
        DEBUG << property
              << " is a pure propositional property"
              << endl;
    }
    else if (f_strategy == INVARIANT_PROPERTY) {
        DEBUG << property
              << " is an invariant (i.e. G-only) LTL property"
              << endl;
    }
    else {
        assert (f_strategy == FULL_LTL_PROPERTY);
        DEBUG << property
              << " is a full LTL property"
              << endl;
    }

    TRACE << "done." << endl;
}

BMC::~BMC()
{}

void BMC::prepare()
{
    Algorithm::prepare();

    Compiler& cmpl(compiler()); // just a local ref
    cmpl.preprocess( em().make_main(), f_property);
    cmpl.preprocess( em().make_main(), em().make_not( f_property));
}

void BMC::compile()
{
    Algorithm::compile();

    // Compiler& cmpl(compiler()); // just a local ref
    // cmpl.process(em().make_main(), f_property, false);
    // while (cmpl.has_next()) {
    //     f_invariant_adds.push_back(cmpl.next());
    // }

    // cmpl.process( em().make_main(),
    //               em().make_not( f_property), false);
    // while (cmpl.has_next()) {
    //     f_violation_adds.push_back(cmpl.next());
    // }
    assert (0); // XXX
}

void BMC::bmc_propositional_check()
{
    f_status = MC_UNKNOWN;
    assert_fsm_init(0);
    assert_fsm_invar(0);
    assert_formula(0, f_violation, engine().new_group());

    TRACE << "Looking for a BMC CEX of length 0" << endl;
    status_t response = engine().solve();

    if ( STATUS_UNSAT == response) {
        f_status = MC_TRUE;
    }
    else if ( STATUS_SAT == response) {
        f_status = MC_FALSE;
    }
    else {
        assert( STATUS_UNKNOWN == response);
    }
}

void BMC::bmc_invarspec_check()
{
    step_t k = 0; // to infinity...
    bool leave = false; // TODO: somebody telling us to stop

    assert_fsm_init(0);
    assert_fsm_invar(0);
    assert_formula(0, f_violation, engine().new_group());

    TRACE << "Looking for a BMC CEX of length 0" << endl;
    if (STATUS_UNSAT == engine().solve()) {

        do {
            /* disable last violation */
            engine().toggle_last_group();

            /* permanently push invariant on last known state */
            assert_formula(k, f_invariant);

            assert_fsm_trans(k ++);
            assert_fsm_invar(k);
            assert_formula(k, f_violation, engine().new_group());

            TRACE << "Looking for a BMC CEX of length "
                  << k << endl;

        } while ( STATUS_UNSAT == engine().solve() && ! leave);
    }

    if (STATUS_SAT == engine().status()) {
        f_status = MC_FALSE;

        TRACE << "Found BMC CEX witness (k = " << k
              << "), invariant is FALSE." << endl;

        /* CEX extraction */
        ostringstream oss; oss << "CEX for '"
                               << property() << "'";

        // Witness& trace = * new BMCCounterExample(property(), model(),
        //                                          engine(), k, false);

        // TODO: register
    }
}

void BMC::bmc_ltlspec_check()
{
    assert(false); // TODO: not yet implemented
}

void BMC::process()
{
    TRACE << "Phase 1" << endl;
    prepare();

    TRACE << "Phase 2" << endl;
    compile();

    TRACE << "Phase 3" << endl;
    if (PURE_PROPOSITIONAL == f_strategy) {
        bmc_propositional_check();
    }

    else if (INVARIANT_PROPERTY == f_strategy) {
        bmc_invarspec_check();
    }

    else if (FULL_LTL_PROPERTY == f_strategy) {
        bmc_ltlspec_check();
    }

    else {
        assert (false); /* unreachable */
    }

    TRACE << "Done." << endl;
}


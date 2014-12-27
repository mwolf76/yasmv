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
#include <witness_mgr.hh>

BMC::BMC(IModel& model, Expr_ptr property, ExprVector& constraints)
    : Algorithm(model)
    , f_property(property)
    , f_constraints(constraints)
{
}

BMC::~BMC()
{}

void BMC::bmc_invarspec_check(Expr_ptr property)
{
    assert( em().is_G( property));
    Expr_ptr ctx = em().make_main();
    Expr_ptr invariant = property->lhs();
    Expr_ptr violation = em().make_not( invariant );

    Compiler& cmpl(compiler()); // just a local ref

    cmpl.preprocess( ctx, invariant );
    Term ii (cmpl.process( ctx, invariant ));

    cmpl.preprocess( ctx, violation);
    Term vv (cmpl.process( ctx, violation ));

    step_t k = 0; // to infinity...
    bool leave = false; // TODO: somebody telling us to stop

    assert_fsm_init(0);
    assert_fsm_invar(0);
    assert_formula(0, vv, engine().new_group());

    TRACE
        << "Looking for a BMC CEX of length 0"
        << endl;

    if (STATUS_UNSAT == engine().solve()) {
        do {
            /* disable last violation */
            engine().toggle_last_group();

            /* permanently push invariant on last known state */
            assert_formula(k, ii);

            assert_fsm_trans(k ++);
            assert_fsm_invar(k);
            assert_formula(k, vv, engine().new_group());

            TRACE << "Looking for a BMC CEX of length "
                  << k << endl;

        } while ( STATUS_UNSAT == engine().solve() && ! leave);
    }

    if (STATUS_SAT == engine().status()) {
        WitnessMgr& wm = WitnessMgr::INSTANCE();

        f_status = MC_FALSE;

        TRACE
            << "Found CEX witness (k =" << k << "), invariant " << invariant
            << " is FALSE."
            << endl;

        Witness& w(* new BMCCounterExample(property, model(),
                                           engine(), k, false));
        wm.register_witness(w);
    }

    else assert(false);

}

void BMC::bmc_ltlspec_check( Expr_ptr property )
{
    assert(false); // TODO: not yet implemented
}

void BMC::process()
{
    prepare();

    compile();

    Normalizer normalizer( ModelMgr::INSTANCE());
    normalizer.process( f_property );
    if (normalizer.is_invariant()) {
        TRACE << f_property
              << " is an invariant (i.e. G-only) LTL property"
              << endl;

        bmc_invarspec_check( normalizer.property() );
    }
    else {
        TRACE << f_property
              << " is a full LTL property"
              << endl;

        bmc_ltlspec_check( normalizer.property() );
    }
    TRACE << "Done." << endl;
}


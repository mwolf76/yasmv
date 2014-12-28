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

// reserved for witnesses
static unsigned progressive = 0;
static const char *cex_trace_prfx = "cex_";

BMC::BMC(ICommand& command, IModel& model, Expr_ptr property, ExprVector& constraints)
    : Algorithm(command, model)
    , f_property(property)
    , f_constraints(constraints)
{}

BMC::~BMC()
{}

void BMC::bmc_invarspec_check(Expr_ptr property)
{
    assert( em().is_G( property));

    // local refs
    SAT& eng(engine());
    Compiler& cmpl(compiler());

    Expr_ptr ctx = em().make_main();
    Expr_ptr invariant = property->lhs();
    Expr_ptr violation = em().make_not(invariant);

    cmpl.preprocess( ctx, violation );
    Term vv (cmpl.process( ctx, violation ));

    step_t j, k = 0; // to infinity...
    bool leave = false; // TODO: somebody telling us to stop

    group_t init_fsm_group (eng.new_group());
    assert (1 == init_fsm_group && 1 == eng.groups()[1]);

    assert_fsm_init(0, init_fsm_group);
    assert_fsm_invar(0, init_fsm_group);

    do {
        /* disable initial states group */
        eng.groups()[1] *= -1;

        /* assert violation in a separate group */
        assert_formula(k, vv, eng.new_group());

        TRACE
            << "Looking for proof or counterexample (k = " << k  << ")"
            << endl;

        if (STATUS_UNSAT == eng.solve()) {
            TRACE
                << "Found k-induction proof (k = " << k << "), invariant `" << invariant
                << "` is TRUE."
                << endl;

            f_status = MC_TRUE;
            break;
        }

        /*enable initial states group */
        eng.groups()[1] *= -1;

        DEBUG
            << "Checking for violation @"
            << k
            << endl;

        if (STATUS_SAT == eng.solve()) {
            WitnessMgr& wm = WitnessMgr::INSTANCE();

            TRACE
                << "Found CEX witness (k = " << k << "), invariant `" << invariant
                << "` is FALSE."
                << endl;

            Witness& w(* new BMCCounterExample(property, model(),
                                               eng, k, false));
            {
                ostringstream oss;
                oss
                    << cex_trace_prfx
                    << (++ progressive);
                w.set_id(oss.str());
            }
            {
                ostringstream oss;
                oss
                    << "CEX witness for property `"
                    << property << "`";
                w.set_desc(oss.str());
            }

            wm.register_witness(w);
            set_witness(w);

            f_status = MC_FALSE;
            break;
        }

        /* disable violation */
        eng.groups().last() *= -1;

        /* unrolling */
        assert_fsm_trans(k ++);
        assert_fsm_invar(k);

        /* build state uniqueness constraint for each pair of states (j, k), where j < k */
        for (j = 0; j < k; ++ j)
            assert_fsm_uniqueness(j, k);

    } while (! leave);
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


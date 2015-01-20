/**
 *  @file BMC Simulation witnesses
 *  @brief BMC Simulation witnesses
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
#include <simulation.hh>

#include <witness/witness.hh>
#include <witness/witness_mgr.hh>

SimulationWitness::SimulationWitness(Model& model, Engine& engine, step_t k)
    : Witness()
{
    EncodingMgr& bm
        (EncodingMgr::INSTANCE());

    ExprMgr& em
        (ExprMgr::INSTANCE());

    int inputs[bm.nbits()];

    /* Collecting symbols for the witness' language */
    SymbIter si (model);
    while (si.has_next()) {
        std::pair <Expr_ptr, Symbol_ptr> pair
            (si.next());
        Expr_ptr ctx
            (pair.first);
        Symbol_ptr symb
            (pair.second);
        Expr_ptr full_name
            ( em.make_dot( ctx, symb->name()));

        f_lang.push_back( full_name );
    }

    /* just step `k` */
    TimeFrame& tf
        (extend());

    SymbIter symbols
        (model, NULL);

    while (symbols.has_next()) {

        std::pair <Expr_ptr, Symbol_ptr> pair
            (symbols.next());

        Expr_ptr ctx
            (pair.first);

        Symbol_ptr symb
            (pair.second);

        Expr_ptr symb_name
                (symb->name());

        Expr_ptr key
            (em.make_dot( ctx, symb_name));

        if (symb->is_variable()) {

            /* time it, and fetch encoding for enc mgr */
            Encoding_ptr enc
                (bm.find_encoding( TimedExpr(key, 0)) );

            /* not in COI, skipping... */
            if ( ! enc )
                continue;

            /* 1. for each bit int the encoding, fetch UCBI, time it
               into TCBI, fetch its value in solver model and set the
               corresponding entry in inputs array. */
            DDVector::const_iterator di;
            unsigned ndx;
            for (ndx = 0, di = enc->bits().begin();
                 enc->bits().end() != di; ++ ndx, ++ di) {

                unsigned bit
                    ((*di).getNode()->index);
                const UCBI& ucbi
                    (bm.find_ucbi(bit));
                const TCBI tcbi
                    (TCBI(ucbi, k));
                Var var
                    (engine.tcbi_to_var(tcbi));
                int value
                    (engine.value(var)); /* Don't care is assigned to 0 */

                inputs[bit] = value;
            }

            /* 2. eval the encoding DDs with inputs and put resulting
               value into time frame container. */
            Expr_ptr value
                (enc->expr(inputs));

            if (value)
                tf.set_value( key, value );
        }

        else if (symb->is_define()) {

            WitnessMgr& wm
                (WitnessMgr::INSTANCE());

            const Define& define
                (symb->as_define());

            Expr_ptr value
                (wm.eval( *this, ctx, define.body(), 0));

            tf.set_value( key, value );
        }
    }
}

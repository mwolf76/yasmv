/**
 * @file reach/witness.cc
 * @brief SAT-based BMC reachability analysis, BMC CEX witness class implementation.
 *
 * This module contains definitions and services that implement the
 * extraction of a CEX (CounterEXample) witness for SAT-based BMC
 * reachability algorithm.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA
 *
 **/

#include <algorithms/base.hh>
#include <algorithms/reach/reach.hh>
#include <algorithms/reach/witness.hh>

#include <symb/symb_iter.hh>

#include <witness/witness.hh>
#include <witness/witness_mgr.hh>

namespace reach {

ReachabilityCounterExample::ReachabilityCounterExample(Expr_ptr property, Model& model,
                                                       Engine& engine, unsigned k, bool reversed)
    : Witness()
{
    EncodingMgr& bm
        (EncodingMgr::INSTANCE());

    ExprMgr& em
        (ExprMgr::INSTANCE());

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

        f_lang.push_back(full_name);
    }

    step_t step
        (reversed ? k : 0);

    do {

        TimeFrame& tf
            (extend());

        SymbIter symbols
            (model);

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

                Variable& var
                    (symb->as_variable());

                /* time it, and fetch encoding for enc mgr */
                Encoding_ptr enc
                    (bm.find_encoding( TimedExpr(key, var.is_frozen() ? FROZEN : 0)) );

                if ( ! enc )
                    continue;

                int inputs[bm.nbits()];
                memset(inputs, 0, sizeof(inputs));

                /* 1. for each bit int the encoding, fetch UCBI, time
                   it into TCBI, fetch its value in MiniSAT model and
                   set the corresponding entry in input. */
                DDVector::const_iterator di;
                unsigned ndx;
                for (ndx = 0, di = enc->bits().begin();
                     enc->bits().end() != di; ++ ndx, ++ di) {

                    unsigned bit
                        ((*di).getNode()->index);

                    const UCBI& ucbi
                        (bm.find_ucbi(bit));

                    const TCBI tcbi
                        (TCBI(ucbi, reversed
                              ? FINAL_STATE - step
                              : FIRST_STATE + step));

                    Var var
                        (engine.tcbi_to_var(tcbi));

                    int value
                        (engine.value(var)); /* XXX: don't cares assigned to 0 */

                    inputs[bit] = value;
                }

                /* 2. eval the encoding DDs with inputs and put
                   resulting value into time frame container. */
                Expr_ptr value
                    (enc->expr(inputs));

                /* NULL values here indicate UNDEFs */
                if (value)
                    tf.set_value( key, value, symb->format());
            }

            else if (symb->is_define()) {

                WitnessMgr& wm
                    (WitnessMgr::INSTANCE());

                const Define& define
                    (symb->as_define());

                Expr_ptr value
                    (wm.eval( *this, ctx, define.body(), 0));

                /* NULL values here indicate UNDEFs */
                if (value)
                    tf.set_value( key, value, symb->format());
            }
        }

        step += reversed ? -1 :  1 ;
        if ((reversed && step == FINAL_STATE) ||
            (! reversed && step > k))
            break;
    } while (1);
} /* ReachabilityCounterExample::ReachabilityCounterExample() */

};
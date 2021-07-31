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

ReachabilityCounterExample::ReachabilityCounterExample(expr::Expr_ptr property, model::Model& model,
                                                       sat::Engine& engine, unsigned k, bool reversed)
    : Witness()
{
    enc::EncodingMgr& bm
        (enc::EncodingMgr::INSTANCE());

    expr::ExprMgr& em
        (expr::ExprMgr::INSTANCE());

    /* Collecting symbols for the witness' language */
    symb::SymbIter si (model);
    while (si.has_next()) {
        std::pair <expr::Expr_ptr, symb::Symbol_ptr> pair
            (si.next());

        expr::Expr_ptr ctx
            (pair.first);

        symb::Symbol_ptr symb
            (pair.second);

        expr::Expr_ptr full_name
            ( em.make_dot( ctx, symb->name()));

        f_lang.push_back(full_name);
    }

    step_t step
        (reversed ? k : 0);

    do {

        witness::TimeFrame& tf
            (extend());

        symb::SymbIter symbols
            (model);

        while (symbols.has_next()) {
            std::pair <expr::Expr_ptr, symb::Symbol_ptr> pair
                (symbols.next());

            expr::Expr_ptr ctx
                (pair.first);

            symb::Symbol_ptr symb
                (pair.second);

            expr::Expr_ptr symb_name
                (symb->name());

            expr::Expr_ptr key
                (em.make_dot( ctx, symb_name));

            if (symb->is_variable()) {
                symb::Variable& var
                    (symb->as_variable());

                /* time it, and fetch encoding for enc mgr */
                enc::Encoding_ptr enc
                    (bm.find_encoding( expr::TimedExpr(key, var.is_frozen() ? FROZEN : 0)) );

                if ( ! enc )
                    continue;

                int inputs[bm.nbits()];
                memset(inputs, 0, sizeof(inputs));

                /* 1. for each bit int the encoding, fetch UCBI, time
                   it into TCBI, fetch its value in MiniSAT model and
                   set the corresponding entry in input. */
                dd::DDVector::const_iterator di;
                unsigned ndx;
                for (ndx = 0, di = enc->bits().begin();
                     enc->bits().end() != di; ++ ndx, ++ di) {

                    unsigned bit
                        ((*di).getNode()->index);

                    const enc::UCBI& ucbi
                        (bm.find_ucbi(bit));

                    const enc::TCBI tcbi
                        (enc::TCBI(ucbi, reversed
                              ? UINT_MAX - step
                              : step));

                    Var var
                        (engine.tcbi_to_var(tcbi));

                    int value
                        (engine.value(var)); /* XXX: don't cares assigned to 0 */

                    inputs[bit] = value;
                }

                /* 2. eval the encoding DDs with inputs and put
                   resulting value into time frame container. */
                expr::Expr_ptr value
                    (enc->expr(inputs));

                /* NULL values here indicate UNDEFs */
                if (value)
                    tf.set_value( key, value, symb->format());
            }

            else if (symb->is_define()) {
                witness::WitnessMgr& wm
                    (witness::WitnessMgr::INSTANCE());

                const symb::Define& define
                    (symb->as_define());

                expr::Expr_ptr value
                    (wm.eval( *this, ctx, define.body(), 0));

                /* NULL values here indicate UNDEFs */
                if (value)
                    tf.set_value( key, value, symb->format());
            }
        }

        step += reversed ? -1 :  1 ;
        if ((reversed && step == UINT_MAX) ||
            (! reversed && step > k))
            break;
    } while (1);
} /* ReachabilityCounterExample::ReachabilityCounterExample() */

};

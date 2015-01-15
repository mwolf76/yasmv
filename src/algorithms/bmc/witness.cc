/**
 *  @file BMC CEX
 *  @brief BMC CounterEXample extraction class
 *
 *  This module contains definitions and services that implements
 *  extraction of a CEX (CounterEXample) witness for SAT BMC
 *  algorithms.
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
#include <base.hh>
#include <bmc.hh>

BMCCounterExample::BMCCounterExample(Expr_ptr property, Model& model,
                                     Engine& engine, unsigned k,
                                     bool use_coi)
    : Witness()
{
#if 0
    EncodingMgr& enc_mgr(EncodingMgr::INSTANCE());
    int inputs[enc_mgr.nbits()];

    /* Language */
    SymbIter si (model);
    while (si.has_next()) {
        Symbol_ptr symb = si.next();
        f_lang.push_back( symb -> expr());
    }

    /* up to k (included) */
    for (step_t step = 0; step <= k; ++ step) {
        TimeFrame& tf = extend();

        SymbIter symbs( model, use_coi ? property : NULL );
        while (symbs.has_next()) {
            Symbol_ptr symb = symbs.next();

            if (symb->is_variable()) {
                Expr_ptr ctx  (symb->ctx());
                Expr_ptr expr (symb->expr());

                /* time it, and fetch encoding for enc mgr */
                FQExpr key(ctx, expr);
                Encoding_ptr enc = enc_mgr.find_encoding(key);
                if ( NULL == enc ) {
                    // TRACE << symb->ctx()
                    //       << "::" << symb->expr()
                    //       << " not in COI, skipping..."
                    //       << endl;

                    continue;
                }

                /* 1. for each bit int the encoding, fetch UCBI, time it
                   into TCBI, fetch its value in MiniSAT model and set
                   the corresponding entry in input. */
                DDVector::const_iterator di;
                unsigned ndx;

                for (ndx = 0, di = enc->bits().begin();
                     enc->bits().end() != di; ++ ndx, ++ di) {

                    unsigned bit = (*di).getNode()->index;

                    const UCBI& ucbi = enc_mgr.find_ucbi(bit);
                    const TCBI& tcbi = TCBI(ucbi.ctx(), ucbi.expr(),
                                            ucbi.time(), ucbi.bitno(),
                                            step);

                    Var var = engine.tcbi_to_var(tcbi);
                    int value = engine.value(var); /* Don't care is assigned to 0 */

                    inputs[bit] = value;
                }

                /* 2. eval the encoding ADD with inputs and put
                   resulting value into time frame container. */
                Expr_ptr value = enc->expr(inputs);
                tf.set_value( expr, value );
            }
        }
    }
#endif
}

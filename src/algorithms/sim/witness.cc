/**
 * @file witness.cc
 * @brief BMC Simulation algorithm, Witness class implementation.
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

#include <common/common.hh>

#include <env/environment.hh>

#include <witness/witness.hh>
#include <witness/witness_mgr.hh>

#include <sim/simulation.hh>

#include <symb/classes.hh>
#include <symb/symb_iter.hh>
#include <symb/typedefs.hh>

namespace sim {

    SimulationWitness::SimulationWitness(model::Model& model, sat::Engine& engine, step_t k)
        : Witness(&engine)
    {
        enc::EncodingMgr& bm { enc::EncodingMgr::INSTANCE() };
        expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };

        int inputs[bm.nbits()];

        /* Collecting symbols for the witness' language */
        symb::SymbIter si { model };
        while (si.has_next()) {
            std::pair<expr::Expr_ptr, symb::Symbol_ptr> pair { si.next() };

            expr::Expr_ptr ctx { pair.first };
            symb::Symbol_ptr symb { pair.second };

            expr::Expr_ptr full_name { em.make_dot(ctx, symb->name()) };
            f_lang.push_back(full_name);
        }

        /* just step `k` */
        witness::TimeFrame& tf { extend() };
        symb::SymbIter symbols { model };

        while (symbols.has_next()) {

            std::pair<expr::Expr_ptr, symb::Symbol_ptr> pair { symbols.next() };
            expr::Expr_ptr ctx { pair.first };
            symb::Symbol_ptr symb { pair.second };
            expr::Expr_ptr symb_name { symb->name() };
            expr::Expr_ptr key { em.make_dot(ctx, symb_name) };

            if (symb->is_variable()) {
                const symb::Variable& var { symb->as_variable() };

                /* INPUT vars are in fact bodyless, typed DEFINEs */
                if (var.is_input()) {
                    expr::Expr_ptr value { env::Environment::INSTANCE().get(symb_name) };

                    if (value) {
                        tf.set_value(key, value, symb->format());
                    }
                }

                else {
                    /* time it, and fetch encoding for enc mgr */
                    enc::Encoding_ptr enc { bm.find_encoding(expr::TimedExpr(key, 0)) };

                    /* not in COI, skipping... */
                    if (!enc) {
                        continue;
                    }

                    /* 1. for each bit int the encoding, fetch UCBI,
		     * time it into TCBI, fetch its value in solver
		     * model and set the corresponding entry in inputs
		     * array. */
                    dd::DDVector::const_iterator di;
                    unsigned ndx;
                    for (ndx = 0, di = enc->bits().begin();
                         enc->bits().end() != di; ++ndx, ++di) {

                        unsigned bit { (*di).getNode()->index };
                        const enc::UCBI& ucbi { bm.find_ucbi(bit) };
                        const enc::TCBI tcbi { enc::TCBI(ucbi, k) };
                        Var var { engine.tcbi_to_var(tcbi) };
                        int value { engine.value(var) }; /* Don't care is
							   assigned to
							   0 */

                        inputs[bit] = value;
                    }

                    /* 2. eval the encoding DDs with inputs and put
		     * resulting value into time frame container. */
                    expr::Expr_ptr value { enc->expr(inputs) };

                    if (value) {
                        tf.set_value(key, value, symb->format());
                    }
                }
            }

            else if (symb->is_define()) {
                witness::WitnessMgr& wm { witness::WitnessMgr::INSTANCE() };
                const symb::Define& define { symb->as_define() };
                expr::Expr_ptr body { define.body() };

                try {
                    expr::Expr_ptr value { wm.eval(*this, ctx, body, 0) };
                    if (value) {
                        tf.set_value(key, value);
                    }
                }

                catch (witness::NoValue& nv) {
                    WARN
                        << "Cannot evaluate define `"
                        << key
                        << " `"
                        << std::endl;
                }
            }
        }
    }

} // namespace sim

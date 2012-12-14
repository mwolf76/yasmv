/**
 *  @file MC Algorithm.hh
 *  @brief SAT BMC Algorithm
 *
 *  This module contains definitions and services that implement an
 *  optimized storage for expressions. Expressions are stored in a
 *  Directed Acyclic Graph (DAG) for data sharing.
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
#include <satbmc.hh>
using namespace Minisat;

SATBMCFalsification::SATBMCFalsification(IModel& model, Expr_ptr property)
    : MCAlgorithm(model, property)
  , f_factory(CuddMgr::INSTANCE().dd())
  , f_engine(f_factory)
  , f_compiler()
{}

SATBMCFalsification::~SATBMCFalsification()
{}

void SATBMCFalsification::push_timed_formulas(ADDVector& formulas, step_t time)
{
    for (ADDVector::iterator i = formulas.begin(); formulas.end() != i; ++ i) {
        ADD phi = *i;
        f_engine.push(phi, time,
                      MAINGROUP,
                      BACKGROUND); // TODO group and color
    }
}

void SATBMCFalsification::prepare()
{
    f_init_adds.clear();
    const Modules& modules = f_model.modules();
    for (Modules::const_iterator m = modules.begin();
         m != modules.end(); ++ m) {

        Module& module = dynamic_cast <Module&> (*m->second);

        /* INIT */
        const ExprVector init = module.init();
        for (ExprVector::const_iterator init_eye = init.begin();
             init_eye != init.end(); ++ init_eye) {

            Expr_ptr ctx = module.expr();
            Expr_ptr body = (*init_eye);

            /* Compiler produces an ADD */
            f_init_adds.push_back(f_compiler.process(ctx, body));
        }

        /* TRANS */
        const ExprVector trans = module.trans();
        for (ExprVector::const_iterator trans_eye = trans.begin();
             trans_eye != trans.end(); ++ trans_eye) {

            Expr_ptr ctx = module.expr();
            Expr_ptr body = (*trans_eye);

            /* Compiler produces an ADD */
            f_trans_adds.push_back(f_compiler.process(ctx, body));
        }
    }
}

void SATBMCFalsification::assert_fsm_init()
{
    clock_t t0 = clock();
    unsigned n = f_init_adds.size();
    TRACE << "CNFizing INITs ... ("
          << n << " formulas)"
          << endl;

    push_timed_formulas(f_init_adds, 0);

    clock_t elapsed = clock() - t0;
    double secs = (double) elapsed / (double) CLOCKS_PER_SEC;
    TRACE << "Done. (took " << secs << " seconds)" << endl;
}

void SATBMCFalsification::assert_fsm_trans(step_t time)
{
    clock_t t0 = clock();
    unsigned n = f_trans_adds.size();

    TRACE << "CNFizing TRANSes @" << time
          << "... (" << n << " formulas)"
          << endl;

    push_timed_formulas(f_trans_adds, time);

    clock_t elapsed = clock() - t0;
    double secs = (double) elapsed / (double) CLOCKS_PER_SEC;
    TRACE << "Done. (took " << secs << " seconds)" << endl;
}

void SATBMCFalsification::assert_violation(step_t time)
{ /* TODO!!! */ }

void SATBMCFalsification::process()
{
    step_t i, k = 50; // TODO

    /* Prepare formulas for time injection */
    prepare();

    assert_fsm_init();
    for (i = 0; i < k; ++ i) {
        assert_fsm_trans(i);
    }

    assert_violation(k);

    if (STATUS_SAT == f_engine.solve()) {
        f_status = MC_FALSE;

        /* cex extraction */
        ostringstream oss; oss << "CEX for '" << f_property << "'";
        Witness& cex = * new BMCCounterExample(f_property, model(), f_engine, k, false);

        // TODO: register
    }

    TRACE << "Done." << endl;

}

BMCCounterExample::BMCCounterExample(Expr_ptr property, IModel& model,
                                     Minisat::SAT& engine, unsigned k,
                                     bool use_coi)
    : Witness()
{
    ostringstream oss; oss << "BMC CTX witness for property " << property;
    set_name(oss.str());

    EncodingMgr& enc_mgr(EncodingMgr::INSTANCE());
    int inputs[enc_mgr.nbits()];

    /* up to k (included) */
    for (step_t step = 0; step <= k; ++ step) {
        TimeFrame& tf = new_frame();

        SymbIter symbs( model, use_coi ? property : NULL );
        while (symbs.has_next()) {
            ISymbol_ptr symb = symbs.next();

            if (symb->is_variable()) {

                /* time it, and fetch encoding for enc mgr */
                FQExpr key(symb->ctx(), symb->expr(), 0);
                IEncoding_ptr enc = enc_mgr.find_encoding(key);
                if ( NULL == enc ) {
                    TRACE << symb->ctx()  << "::"
                          << symb->expr() << " not in COI, skipping..." << endl;
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

                DEBUG << "value (" << key << ") = " << value << endl;
                tf.set_value( key, value );

            } // if (is_variable)
        } // while (symbs.has_next())
    } // foreach time frame
}

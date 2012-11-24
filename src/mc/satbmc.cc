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

void SATBMCFalsification::push_formula(ADD phi)
{
    clock_t t0 = clock();
    TRACE << "CNFizing ..." << endl;

    f_engine.push(phi);

    clock_t elapsed = clock() - t0;
    double secs = (double) elapsed / (double) CLOCKS_PER_SEC;
    TRACE << "Done. (took " << secs << " seconds)" << endl;
}

void SATBMCFalsification::assert_fsm_init()
{
    const Modules& modules = f_model.modules();
    for (Modules::const_iterator m = modules.begin();
         m != modules.end(); ++ m) {

        Module& module = dynamic_cast <Module&> (*m->second);
        const ExprVector init = module.init();

        for (ExprVector::const_iterator init_eye = init.begin();
             init_eye != init.end(); ++ init_eye) {

            Expr_ptr ctx = module.expr();
            Expr_ptr body = (*init_eye);

            ADD add = f_compiler.process(ctx, body, 0);
            push_formula(add);
        }
    }
}

void SATBMCFalsification::assert_fsm_trans(step_t time)
{
    const Modules& modules = f_model.modules();
    for (Modules::const_iterator m = modules.begin();
         m != modules.end(); ++ m) {

        Module& module = dynamic_cast <Module&> (*m->second);
        const ExprVector trans = module.trans();

        for (ExprVector::const_iterator trans_eye = trans.begin();
             trans_eye != trans.end(); ++ trans_eye) {

            Expr_ptr ctx = module.expr();
            Expr_ptr body = (*trans_eye);

            ADD add = f_compiler.process(ctx, body, time);
            push_formula(add);
        }
    }
}

void SATBMCFalsification::assert_violation(step_t time)
{ /* TODO!!! */ }

void SATBMCFalsification::process()
{
    step_t i, k = 1; // TODO

    assert_fsm_init();
    for (i = 0; i < k; ++ i) {
        assert_fsm_trans(i);
    }

    assert_violation(k);

    TRACE << "Solving..." << endl;
    if (STATUS_SAT == f_engine.solve()) {
        f_status = MC_FALSE;

        /* ctx extraction */
        ostringstream oss; oss << "CTX for '" << f_property << "'";
        Witness& ctx = * new BMCCounterExample(f_property, model(), f_engine, k, false);

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

    /* it's not necessary to fully populate the inputs array
       before proceeding to evaluation (this is why we're usiong
       calloc here), so everything can be done in just one pass. */
    int *inputs = (int *) calloc( enc_mgr.nbits(), sizeof(int));

    for (unsigned i = 0; i < k; ++ i) {
        TimeFrame& tf = new_frame();

        SymbIter symbs( model, use_coi ? property : NULL );
        while (symbs.has_next()) {
            ISymbol_ptr symb = symbs.next();

            if (symb->is_variable()) {

                /* time it, and fetch encoding for enc mgr */
                FQExpr key(symb->ctx(), symb->expr(), i);
                IEncoding_ptr enc = enc_mgr.find_encoding(key);

                /* possible casts */
                AlgebraicEncoding_ptr ae;

                // ...
                if (NULL != (ae = dynamic_cast<AlgebraicEncoding_ptr> (enc))) {

                    for (unsigned i = 0; i < ae->width(); ++ i) {

                        /* filtered customs on vector iterator to
                           fetch i-th digit bits of an algebraic,
                           update relevant bits of the inputss
                           array. */
                        DDVector::const_iterator begin = ae->bits_begin(i);
                        DDVector::const_iterator end = ae->bits_end(i);
                        for (DDVector::const_iterator di = begin; di != end; ++ di) {

                            ADD bit(*di);
                            int index = bit.getNode()->index;
                            int value = (Minisat::toInt(engine.value(index)) == 0);
                            inputs[index] = value;
                        }
                    }
                } // is algebraic

                else {
                    // ....
                }


                /* put final value into time frame container */
                Expr_ptr value = enc->expr(inputs);
                DEBUG << "value (" << key << ") = " << value << endl;
                tf.set_value( key, value );

            } // if (is_variable)

        } // while (symbs.has_next())
    } // foreach time frame

    free ( inputs );

}

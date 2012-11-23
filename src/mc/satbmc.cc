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

void SATBMCFalsification::assert_fsm_init()
{
    const Modules& modules = f_model.modules();
    for (Modules::const_iterator m = modules.begin();
         m != modules.end(); ++ m) {

        Module& module = dynamic_cast <Module&> (*m->second);
        TRACE << "processing module '" << module << "' " << endl;

        const ExprVector init = module.init();
        for (ExprVector::const_iterator init_eye = init.begin();
             init_eye != init.end(); init_eye ++) {

            Expr_ptr ctx = module.expr();
            Expr_ptr body = (*init_eye);
            TRACE << "compiling INIT " << ctx << "::" << body << endl;

            ADD add = f_compiler.process(ctx, body, 0);

            TRACE << "CNFizing ..." << endl;
            f_engine.push(add);
            TRACE << "Done." << endl;
        } // for init

    } // modules
}

void SATBMCFalsification::assert_fsm_trans(step_t time)
{
    const Modules& modules = f_model.modules();
    for (Modules::const_iterator m = modules.begin();
         m != modules.end(); ++ m) {

        Module& module = dynamic_cast <Module&> (*m->second);
        DEBUG << "processing module '" << module << "' " << endl;

        const ExprVector trans = module.trans();
        for (ExprVector::const_iterator trans_eye = trans.begin();
             trans_eye != trans.end(); trans_eye ++) {

            Expr_ptr ctx = module.expr();
            Expr_ptr body = (*trans_eye);
            TRACE << "compiling @" << time << " TRANS " << ctx << "::" << body << endl;

            ADD add = f_compiler.process(ctx, body, time);

            TRACE << "CNFizing ..." << endl;
            f_engine.push(add);
            TRACE << "Done." << endl;
        } // for trans

    } // modules
}

void SATBMCFalsification::assert_violation(step_t time)
{
}

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
        cerr << "CTX" << endl;
        // cerr << ctx << endl;
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

    for (unsigned i = 0; i < k; ++ i) {
        TimeFrame& tf = new_frame();

        SymbIter symbs( model, use_coi ? property : NULL );
        while (symbs.has_next()) {
            ISymbol_ptr symb = symbs.next();

            if (symb->is_variable()) {
                /* time it */
                FQExpr key(symb->ctx(), symb->expr(), i);
                IEncoding_ptr enc = enc_mgr.find_encoding(key);

                /* the ADDs */
                DDVector& dds = enc->dv();
                DDVector  assignment;

                for (DDVector::const_iterator ddi = dds.begin();
                     ddi != dds.end(); ++ ddi) {

                    ADD add = (*ddi);
                    int index = add.getNode()->index;

                    ADD bitvalue = (Minisat::toInt(engine.value(index)) == 0)
                        ? enc_mgr.one()
                        : enc_mgr.zero()
                        ;

                    assignment.push_back( bitvalue );
                }
                assert( assignment.size() == dds.size() );

                /* put final value into time frame container */
                Expr_ptr value = enc->expr(assignment);
                tf.set_value( key, value );
            }
        }
    }
}

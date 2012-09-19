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
#include <sat.hh>

using namespace Minisat;

SATBMCFalsification::SATBMCFalsification(IModel& model)
  : MCAlgorithm(model)
  // , f_compiler()
{
  TRACE << "Creating SATBMCFalsification algorithm instance "
        << get_param("alg_name") << " @" << this
        << endl;
}

SATBMCFalsification::~SATBMCFalsification()
{
  TRACE << "Destroying SATBMCFalsification algorithm instance"
        << get_param("alg_name") << " @" << this
        << endl;
}

void SATBMCFalsification::process()
{
    BDDTermFactory tf(CuddMgr::INSTANCE().dd());
    SAT<BDD> engine (tf);

    const Modules& modules = f_model.modules();
    {
        time_t step = 0;
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

                BDD bdd = f_compiler.process(ctx, body, step);
                engine.push(bdd);
            } // for init
        } // modules

        engine.solve();
    }

    // Colors colors;
    // BDD a = engine->interpolant(colors);
    // BDD b = engine->model();


    for (time_t t = 0; t < 10; ++ t) {

    }
}

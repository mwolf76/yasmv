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
    BDDTermFactory tf(* new Cudd());
    SAT<BDD> *engine = new SAT<BDD> (tf);

    Colors colors;
    BDD a = engine->interpolant(colors);
    BDD b = engine->model();

    delete engine;
}

//     // const Modules& modules = model.modules();
//     // for (step_t i = 0; i < 10; ++ i) {
//     //     for (Modules::iterator module = modules.begin();
//     //          module != modules.end(); ++ module) {

//     //         ExprVector& init = module->init();
//     //         for (ExprVector::iterator expr = init.begin();
//     //              expr != init.end(); ++ expr) {

//     //             ADD add = f_compiler.process(*expr, 0);
//     //             f_sat.inject(add);
//     //         }
//     //     }

//     //     // invar, ... unrolling, blah blah blah
//     //     f_sat.process();

//     //    }
// }

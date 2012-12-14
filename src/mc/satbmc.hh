/**
 *  @file BMC Algorithm.hh
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

#ifndef BMC_FALSIFICATION_ALGORITHM_H
#define BMC_FALSIFICATION_ALGORITHM_H

#include <mc.hh>
#include <sat.hh>

#include <compilers/compiler.hh>

#include <witness.hh>

class SATBMCFalsification : public MCAlgorithm {

public:
    SATBMCFalsification(IModel& model, Expr_ptr formula);
    ~SATBMCFalsification();

    void process();

private:
    Minisat::DDTermFactory f_factory;
    Minisat::SAT f_engine;
    Compiler f_compiler;

    // services
    void prepare();

    void assert_fsm_init();
    void assert_fsm_trans(step_t time);
    void assert_violation(step_t time);

    void push_timed_formulas(ADDVector& formulas, step_t time);

    ADDVector f_init_adds;
    ADDVector f_trans_adds;
};

/* Specialized for BMC ctx */
class BMCCounterExample : public Witness {
public:
    BMCCounterExample(Expr_ptr property, IModel& model,
                      Minisat::SAT& engine, unsigned k, bool use_coi);
};

#endif

/**
 *  @file kind.hh
 *  @brief SAT K-induction algorithms
 *
 *  This module contains definitions and services that implement the
 *  SAT based K-induction algorithms (forward and backward variants)
 *  for the verification of invariant properties.
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

#ifndef KIND_FALSIFICATION_ALGORITHM_H
#define KIND_FALSIFICATION_ALGORITHM_H

#include <mc.hh>
#include <sat.hh>

#include <compilers/compiler.hh>

#include <witness.hh>

class KInduction: public MCAlgorithm {

public:
    KInduction(IModel& model, Expr_ptr formula);
    ~KInduction();

    void process();

protected:
    ADDVector f_not_init_adds;
    void assert_fsm_not_init (step_t time,
                              group_t group = MAINGROUP,
                              color_t color = BACKGROUND);
};

#endif

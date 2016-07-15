/**
 *  @file bmc.hh
 *  @brief SAT-based BMC Algorithms for property checking
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

#ifndef BMC_ALGORITHM_H
#define BMC_ALGORITHM_H

#include <expr/expr.hh>

#include <algorithms/base.hh>

#include <witness/witness.hh>

class BMC : public Algorithm {

public:
    BMC(Command& command, Model& model);
    ~BMC();

    void process(const Expr_ptr phi);

    mc_status_t status();

    mc_status_t sync_status();
    void sync_set_status(mc_status_t status);

    step_t sync_k(void);
    void sync_set_k(step_t k);

private:
    boost::mutex f_status_mutex;
    mc_status_t f_status;
    step_t f_k;

    /**
     * strategies
     */

    /* is there a k-path leading to a violation of P? */
    void forward( Expr_ptr phi, CompilationUnit& ii, CompilationUnit& vv);

    /* is there a loop-free k-path leading to a violation of P? This
       is sound provided that no CEX exists up to k - 1. */
    void backward( Expr_ptr phi, CompilationUnit& ii, CompilationUnit& vv);
};

/* Specialized for BMC CEX */
class BMCCounterExample : public Witness {
public:
    BMCCounterExample(Expr_ptr property, Model& model,
                      Engine& engine, unsigned k, bool use_coi);
};

#endif

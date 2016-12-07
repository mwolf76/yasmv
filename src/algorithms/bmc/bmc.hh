/**
 * @file bmc.hh
 * @brief SAT-based BMC reachability algorithm for invariant properties checking
 *
 * This header file contains the declarations required to implement
 * the BMC reachability checking algorithm.
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

#ifndef BMC_ALGORITHM_H
#define BMC_ALGORITHM_H

#include <expr/expr.hh>

#include <algorithms/base.hh>

#include <witness/witness.hh>

typedef enum {
    BMC_REACHABLE,
    BMC_UNREACHABLE,
    BMC_UNKNOWN,
    BMC_ERROR,
} reachability_status_t;

class BMC : public Algorithm {

public:
    BMC(Command& command, Model& model);
    ~BMC();

    void process(const Expr_ptr phi);

    reachability_status_t status();

    reachability_status_t sync_status();
    void sync_set_status(reachability_status_t status);

    step_t sync_fwd_k(void);
    void sync_set_fwd_k(step_t k);

    step_t sync_bwd_k(void);
    void sync_set_bwd_k(step_t k);

private:
    boost::mutex f_status_mutex;
    reachability_status_t f_status;

    boost::mutex f_fwd_k_mutex;
    step_t f_fwd_k;

    boost::mutex f_bwd_k_mutex;
    step_t f_bwd_k;

    Expr_ptr f_phi; /* GOAL */

    /**
     * search strategies
     */
    void forward_reachability(CompilationUnit& goal);
    void forward_unreachability(); /* unused */

    void backward_reachability(CompilationUnit& goal);
    void backward_unreachability(CompilationUnit& goal);
};

/* Specialized for BMC CEX */
class BMCCounterExample : public Witness {
public:
    BMCCounterExample(Expr_ptr property, Model& model,
                      Engine& engine, unsigned k);
};

class BMCReversedCounterExample : public Witness {
public:
    BMCReversedCounterExample(Expr_ptr property, Model& model,
                              Engine& engine, unsigned k);
};


#endif /* BMC_ALGORITHM_H */

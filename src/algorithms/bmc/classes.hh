/**
 * @file bmc/classes.hh
 * @brief SAT-based BMC reachability algorithm.
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

#ifndef BMC_ALGORITHM_CLASSES_H
#define BMC_ALGORITHM_CLASSES_H

#include <algorithms/base.hh>
#include <algorithms/bmc/typedefs.hh>

class BMC : public Algorithm {

public:
    BMC(Command& command, Model& model);
    ~BMC();

    void process(const Expr_ptr phi);

    inline reachability_status_t status()
    { return sync_status(); }

    reachability_status_t sync_status();
    void sync_set_status(reachability_status_t status);

private:
    boost::mutex f_status_mutex;
    reachability_status_t f_status;

    Expr_ptr f_phi; /* GOAL */

    /* strategies */
    void forward_strategy(CompilationUnit& goal);
    void backward_strategy(CompilationUnit& goal);
};

#endif /* BMC_ALGORITHM_CLASSES_H */

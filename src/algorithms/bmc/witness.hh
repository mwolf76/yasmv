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

#ifndef BMC_ALGORITHM_WITNESS_H
#define BMC_ALGORITHM_WITNESS_H

#include <algorithms/base.hh>
#include <algorithms/bmc/typedefs.hh>
#include <algorithms/bmc/witness.hh>

#include <expr/expr.hh>

#include <witness/witness.hh>

/* Specialized for BMC CEX */
class BMCCounterExample : public Witness {
public:
    BMCCounterExample(Expr_ptr property, Model& model, Engine& engine,
                      unsigned k, bool reversed = false);
};

#endif /* BMC_ALGORITHM_WITNESS_H */

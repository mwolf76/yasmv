/**
 * @file bmc.hh
 * @brief SAT-based SBMC algorithm for LTL properties checking
 *
 * This header file contains the declarations required to implement
 * the LTL SAT-based SBMC model checking algorithm.
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

#ifndef CHECK_ALGORITHM_H
#define CHECK_ALGORITHM_H

#include <cmd/command.hh>

#include <expr/expr.hh>

#include <algorithms/base.hh>
#include <witness/witness.hh>

namespace check {

    typedef enum {
        CHECK_FALSE,
        CHECK_TRUE,
        CHECK_UNKNOWN,
        CHECK_ERROR,
    } ltl_status_t;

    class Check: public algorithms::Algorithm {

    public:
        Check(cmd::Command& command, model::Model& model);
        ~Check();

        void process(const expr::Expr_ptr phi);

        inline ltl_status_t status() const
        {
            return f_status;
        }

        inline void set_status(ltl_status_t status)
        {
            f_status = status;
        }

    private:
        ltl_status_t f_status;
    };

    /* Specialized for LTL CEX */
    class CheckCounterExample: public witness::Witness {
    public:
        CheckCounterExample(expr::Expr_ptr property, model::Model& model,
                            sat::Engine& engine, unsigned k);
    };

} // namespace check

#endif /* CHECK_ALGORITHM_H */

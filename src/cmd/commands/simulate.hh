/**
 * @file simulate.hh
 * @brief Command-interpreter subsystem related classes and definitions.
 *
 * This header file contains the handler interface for the `simulate`
 * command.
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

#ifndef SIMULATE_H_CMD
#define SIMULATE_H_CMD

#include <algorithms/sim/simulation.hh>
#include <cmd/command.hh>

namespace cmd {

    class Simulate final: public Command {
    public:
        explicit Simulate(Interpreter& owner);
        ~Simulate() override;

        utils::Variant operator()() override;

        void add_constraint(expr::Expr_ptr constraint);

        void set_until_condition(expr::Expr_ptr until_condition);
        inline expr::Expr_ptr until_condition() const
        {
            return f_until_condition;
        }

        void set_k(step_t k);
        inline step_t k() const
        {
            return f_k;
        }

        void set_trace_uid(pconst_char trace_uid);
        inline pconst_char trace_uid() const
        {
            return f_trace_uid;
        }

    private:
        std::ostream& f_out;

        /* (optional) additional constraints */
        expr::ExprVector f_constraints;

        /* HALT condition (optional) */
        expr::Expr_ptr f_until_condition;

        /* Number of simulation steps to be performed (optional) */
        step_t f_k;

        /* Simulation trace uid (optional) */
        pchar f_trace_uid;
    };

    typedef Simulate* Simulate_ptr;

    class SimulateTopic final: public CommandTopic {
    public:
        explicit SimulateTopic(Interpreter& owner);
        ~SimulateTopic() override;

        void usage() override;
    };

};     // namespace cmd
#endif /* SIMULATE_H_CMD */

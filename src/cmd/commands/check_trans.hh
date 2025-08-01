/**
 * @file check_trans.hh
 * @brief Command-interpreter subsystem related classes and definitions.
 *
 * This header file contains the handler interface for the `check-trans`
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

#ifndef CHECK_TRANS_CMD_H
#define CHECK_TRANS_CMD_H

#include <algorithms/fsm/fsm.hh>
#include <cmd/command.hh>

namespace cmd {

    class CheckTrans: public Command {

    public:
        CheckTrans(Interpreter& owner);
        virtual ~CheckTrans();

        /** cmd params */
        void add_constraint(expr::Expr_ptr constraint);
        void set_limit(value_t value);

        /* run() */
        utils::Variant virtual operator()();

    private:
        std::ostream& f_out;

        /* (optional) additional constraints */
        expr::ExprVector f_constraints;

        /* max depth of FSM consistency check */
        value_t f_limit;

        // -- helpers -------------------------------------------------------------
        bool check_requirements();
    };

    typedef CheckTrans* CheckTrans_ptr;

    class CheckTransTopic: public CommandTopic {
    public:
        CheckTransTopic(Interpreter& owner);
        virtual ~CheckTransTopic();

        void virtual usage();
    };

}; // namespace cmd

#endif /* CHECK_TRANS_CMD_H */

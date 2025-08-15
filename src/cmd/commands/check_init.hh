/**
 * @file check_init.hh
 * @brief Command-interpreter subsystem related classes and definitions.
 *
 * This header file contains the handler interface for the `check-init`
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

#ifndef CHECK_INIT_CMD_H
#define CHECK_INIT_CMD_H

#include <cmd/command.hh>

namespace cmd {

    class CheckInit final: public Command {
    public:
        explicit CheckInit(Interpreter& owner);
        ~CheckInit() override;

        /** cmd params */
        void add_constraint(expr::Expr_ptr constraint);

        /* run() */
        utils::Variant operator()() override;

    private:
        std::ostream& f_out;

        /* (optional) additional constraints */
        expr::ExprVector f_constraints;

        // -- helpers -------------------------------------------------------------
        bool check_requirements();
    };

    typedef CheckInit* CheckInit_ptr;

    class CheckInitTopic: public CommandTopic {
    public:
        explicit CheckInitTopic(Interpreter& owner);
        ~CheckInitTopic() override;

        void usage() override;
    };

}; // namespace cmd

#endif /* CHECK_INIT_CMD_H */

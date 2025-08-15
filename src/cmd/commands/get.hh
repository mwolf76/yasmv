/**
 * @file get.hh
 * @brief Command-interpreter subsystem related classes and definitions.
 *
 * This header file contains the handler interface for the `get`
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
#ifndef GET_CMD_H
#define GET_CMD_H

#include <cmd/command.hh>
#include <env/environment.hh>

namespace cmd {

    class Get final: public Command {

        expr::Expr_ptr f_identifier;

    public:
        explicit Get(Interpreter& owner);
        ~Get() override;

        void set_identifier(expr::Expr_ptr id);
        utils::Variant operator()() override;

    private:
        void print_all_assignments(std::ostream& os);
        utils::Variant print_one_assignment(std::ostream& os, expr::Expr_ptr id);

        void print_assignment(std::ostream& os, expr::Expr_ptr id);
    };

    typedef Get* Get_ptr;

    class GetTopic final: public CommandTopic {
    public:
        explicit GetTopic(Interpreter& owner);
        ~GetTopic() override;

        void usage() override;
    };

}; // namespace cmd

#endif // GET_CMD_H

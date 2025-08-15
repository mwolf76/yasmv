/**
 * @file quit.hh
 * @brief Command-interpreter subsystem related classes and definitions.
 *
 * This header file contains the handler interface for the `quit`
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
#ifndef QUIT_CMD_H
#define QUIT_CMD_H

#include <cmd/command.hh>
#include <cmd/commands/commands.hh>

namespace cmd {

    class Quit final: public Command {

        int f_retcode;

    public:
        explicit Quit(Interpreter& owner);
        ~Quit() override;

        void set_retcode(int retcode);

        utils::Variant operator()() override;
    };

    class QuitTopic final: public CommandTopic {
    public:
        explicit QuitTopic(Interpreter& owner);
        ~QuitTopic() override;

        void usage() override;
    };

};     // namespace cmd
#endif // QUIT_CMD_H

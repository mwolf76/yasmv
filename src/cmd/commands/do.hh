/**
 * @file do.hh
 * @brief Command-interpreter subsystem related classes and definitions.
 *
 * This header file contains the handler inteface for the `do`
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

#ifndef DO_H
#define DO_H

#include <cmd/command.hh>

namespace cmd {

    typedef CommandTopic* CommandTopic_ptr;

    using Commands = std::vector<Command_ptr>;
    class Do: public Command {
        Commands f_commands;

    public:
        Do(Interpreter& owner);
        virtual ~Do();
        void add_command(Command_ptr command);

        utils::Variant virtual operator()();
    };
    typedef Do* Do_ptr;

    class DoTopic: public CommandTopic {
    public:
        DoTopic(Interpreter& owner);
        virtual ~DoTopic();

        void virtual usage();
    };

};     // namespace cmd
#endif /* DO_H */

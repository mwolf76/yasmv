/*
 * @file command.hh
 * @brief Command-interpreter subsystem related classes and definitions.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/
#ifndef COMMAND_H
#define COMMAND_H

#include <common.hh>

namespace Command {

    class ICommand : IObject {
    public:
        // abstract dctor
        virtual ~ICommand() =0;

        // functor-pattern
        virtual operator()() =0;
    };

    // -- command definitions --------------------------------------------------
    class Command : public class ICommand {
    public:
        Command();
        virtual ~Command();
    };

    class FormatCommand : Command {
    public:
        FormatCommand(const char *fmt, ...);
        virtual ~FormatCommand();

    private:
        const char *fmt;
    };

    class QuitCommand : Command {
    public:
        QuitCommand(int retcode);
        virtual ~QuitCommand();

    private:
        int f_retcode;
    };

};

#endif

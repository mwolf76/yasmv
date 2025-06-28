/**
 * @file time.hh
 * @brief Command-interpreter subsystem related classes and definitions.
 *
 * This header file contains the handler interface for the `time`
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

#ifndef TIME_CMD_H
#define TIME_CMD_H

#include <cmd/command.hh>

namespace cmd {

    class Time: public Command {
    public:
        Time(Interpreter& owner);
        virtual ~Time();

        utils::Variant virtual operator()();
    };


    class TimeTopic: public CommandTopic {
    public:
        TimeTopic(Interpreter& owner);
        virtual ~TimeTopic();

        void virtual usage();
    };

};     // namespace cmd
#endif /* TIME_CMD_H */

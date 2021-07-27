/**
 * @file list_traces.hh
 * @brief Command-interpreter subsystem related classes and definitions.
 *
 * This header file contains the handler inteface for the `list-traces`
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

#ifndef LIST_TRACES_CMD_H
#define LIST_TRACES_CMD_H

#include <cmd/command.hh>

namespace cmd {

class ListTraces : public Command {
public:
    ListTraces (Interpreter& owner);
    virtual ~ListTraces();

    Variant virtual operator()();
};

class ShowTracesTopic : public CommandTopic {
public:
    ShowTracesTopic(Interpreter& owner);
    virtual ~ShowTracesTopic();

    void virtual usage();
};

};
#endif /* LIST_TRACES_CMD_H */

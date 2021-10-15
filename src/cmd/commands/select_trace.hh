/**
 * @file SELECT_TRACE.hh
 * @brief Command-interpreter subsystem related classes and definitions.
 *
 * This header file contains the handler interface for the `select-trace`
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

#ifndef SELECT_TRACE_CMD_H
#define SELECT_TRACE_CMD_H

#include <cmd/command.hh>
#include <witness/witness.hh>

namespace cmd {

    class SelectTrace : public Command {

        /* the trace id */
        pchar f_trace_id;

    public:
        void set_trace_id(pconst_char trace_id);
        inline pconst_char trace_id() const
        { return f_trace_id; }

        SelectTrace (Interpreter& owner);
        virtual ~SelectTrace();

        utils::Variant virtual operator()();
    };

    typedef SelectTrace* SelectTrace_ptr;

    class SelectTraceTopic : public CommandTopic {
    public:
        SelectTraceTopic(Interpreter& owner);
        virtual ~SelectTraceTopic();

        void virtual usage();
    };

} // namespace cmd

#endif /* SELECT_TRACE_CMD_H */

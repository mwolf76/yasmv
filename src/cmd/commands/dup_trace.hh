/*
 * @file dup_trace.hh
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
#ifndef DUP_TRACE_CMD_H
#define DUP_TRACE_CMD_H

#include <cmd/command.hh>

namespace cmd {

class DupTrace : public Command {

    pchar f_trace_id;
    pchar f_duplicate_id;

public:
    DupTrace (Interpreter& owner);
    virtual ~DupTrace();

    void set_trace_id(pconst_char trace_id);
    void set_duplicate_id(pconst_char duplicate_id);

    utils::Variant virtual operator()();
};
typedef DupTrace* DupTrace_ptr;

class DupTraceTopic : public CommandTopic {
public:
    DupTraceTopic(Interpreter& owner);
    virtual ~DupTraceTopic();

    void virtual usage();
};

};

#endif // DUP_TRACE_CMD_H

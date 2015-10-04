/*
 * @file dump_trace.hh
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
#ifndef DUMP_TRACE_CMD_H
#define DUMP_TRACE_CMD_H

#include <cmd/command.hh>
#include <witness/witness.hh>

/** Raised when the type checker detects a wrong type */
class UnsupportedFormat : public CommandException {

    pchar f_format;

public:
    UnsupportedFormat(pconst_char format);
    ~UnsupportedFormat() throw();

    const char* what() const throw();
};

class DumpTrace : public Command {

    /* the trace id (optional) */
    pchar f_trace_id;

    /* the format to use for dumping (must be one of "plain", "json", ...) */
    pconst_char f_format;

    /* the output filepath (optional) */
    pchar f_output;

public:
    void set_trace_id(pconst_char trace_id);
    inline pconst_char trace_id() const
    { return f_trace_id; }

    void set_format  (pconst_char format);
    inline pconst_char format() const
    { return f_format; }

    void set_output  (pconst_char filepath);
    inline pconst_char output() const
    { return f_output; }

    DumpTrace (Interpreter& owner);
    virtual ~DumpTrace();

    Variant virtual operator()();
    void virtual usage();

private:
    void dump_plain(std::ostream& os, Witness& w);
    void dump_json(std::ostream& os, Witness& w);
};

#endif

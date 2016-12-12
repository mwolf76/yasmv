/**
 * @file dump_trace.hh
 * @brief Command-interpreter subsystem related classes and definitions.
 *
 * This header file contains the handler inteface for the `dump-trace`
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

#ifndef DUMP_TRACE_CMD_H
#define DUMP_TRACE_CMD_H

#include <cmd/command.hh>
#include <witness/witness.hh>

/** Raised when the type checker detects a wrong type */
class UnsupportedFormat : public CommandException {
public:
    UnsupportedFormat(pconst_char format);
};

/* Model ordering-preserving comparison helper */
class OrderingPreservingComparisonFunctor {
    Model& f_model;

public:
    OrderingPreservingComparisonFunctor(Model& model)
        : f_model(model)
    {}

    bool operator() (Expr_ptr a, Expr_ptr b)
    {
        assert(a);
        assert(b);

        Expr_ptr lhs_a
            (a->lhs());

        Expr_ptr lhs_b
            (b->lhs());

        return
            f_model.symbol_index(lhs_a) <
            f_model.symbol_index(lhs_b) ;
    }
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

private:
    void dump_plain(std::ostream& os, Witness& w);
    void dump_plain_section(std::ostream&os,
                            const char* section,
                            ExprVector& ev);

    void dump_json(std::ostream& os, Witness& w);
    void dump_json_section(std::ostream&os,
                           const char* section,
                           ExprVector& ev);

    void dump_xml(std::ostream& os, Witness& w);
    void dump_xml_section(std::ostream&os,
                          const char* section,
                          ExprVector& ev);

    /* these values actually come from the current environment */
    void process_input(Witness& w,
                       ExprVector& input_vars_assignments);

    /* these values actually belong to the trace */
    void process_time_frame(Witness& w, step_t time,
                            ExprVector& state_vars_assignments,
                            ExprVector& defines_assignments);

};

class DumpTraceTopic : public CommandTopic {
public:
    DumpTraceTopic(Interpreter& owner);
    virtual ~DumpTraceTopic();

    void virtual usage();
};

#endif /* DUMP_TRACE_CMD_H */

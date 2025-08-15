/**
 * @file dump_trace.hh
 * @brief Command-interpreter subsystem related classes and definitions.
 *
 * This header file contains the handler interface for the `dump-trace`
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
#include <expr/atom.hh>

#include <witness/witness.hh>
#include <witness/witness_mgr.hh>

#include <jsoncpp/json/json.h>

namespace cmd {

    /** Raised when the type checker detects a wrong type */
    class UnsupportedFormat: public CommandException {
    public:
        explicit UnsupportedFormat(pconst_char format);
    };

    /** Raised when both -a and a trace id are specified */
    class BadRequest: public CommandException {
    public:
        explicit BadRequest();
    };

    /* Model ordering-preserving comparison helper */
    class OrderingPreservingComparisonFunctor {
        model::Model& f_model;

    public:
        explicit OrderingPreservingComparisonFunctor(model::Model& model)
            : f_model(model)
        {}

        bool operator()(const expr::Expr_ptr a, const expr::Expr_ptr b) const
        {
            assert(a);
            assert(b);

            const expr::Expr_ptr lhs_a { a->lhs() };
            assert(lhs_a != nullptr);

            const expr::Expr_ptr lhs_b { b->lhs() };
            assert(lhs_b != nullptr);

            return f_model.symbol_index(lhs_a) <
                   f_model.symbol_index(lhs_b);
        }
    };

    class DumpTrace final: public Command {

        /* the trace ids selected for dumping */
        expr::AtomVector f_trace_ids;

        /* the format to use for dumping (must be one of "plain", "json") */
        pconst_char f_format;

        /* the output filepath (optional) */
        pchar f_output;

        /* dump all traces */
        bool f_all;

    public:
        void add_trace_id(pconst_char trace_id);
        const expr::AtomVector& trace_ids() const
        {
            return f_trace_ids;
        }

        void set_format(pconst_char format);
        pconst_char format() const
        {
            return f_format;
        }

        void set_output(pconst_char filepath);
        pconst_char output() const
        {
            return f_output;
        }

        void set_all(bool value);
        bool all() const
        {
            return f_all;
        }

        explicit DumpTrace(Interpreter& owner);
        ~DumpTrace() override;

        utils::Variant operator()() override;

    private:
        std::ostream* f_outfile { nullptr };
        std::ostream& get_output_stream();

        /* PLAIN format helpers */
        void dump_plain(std::ostream& os, const witness::WitnessList& witness_list);
        void dump_plain_section(std::ostream& os, const char* section, expr::ExprVector& assignments);

        /* JSON format helpers */
        void dump_json(std::ostream& os, const witness::WitnessList& witness_list);
        Json::Value section_to_json(expr::ExprVector& assignments);

        /* these values actually come from the current environment */
        void process_input(witness::Witness& w,
                           expr::ExprVector& input_vars_assignments);

        /* these values actually belong to the trace */
        void process_time_frame(witness::Witness& w, step_t time,
                                expr::ExprVector& state_vars_assignments,
                                expr::ExprVector& defines_assignments);
    };

    typedef DumpTrace* DumpTrace_ptr;

    class DumpTraceTopic final: public CommandTopic {
    public:
        explicit DumpTraceTopic(Interpreter& owner);
        ~DumpTraceTopic() override;

        void usage() override;
    };

} // namespace cmd

#endif /* DUMP_TRACE_CMD_H */

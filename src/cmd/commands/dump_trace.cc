/*
 * @file dump_trace.cc
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
#include <cstdlib>
#include <cstring>

#include <cmd/commands/dump_trace.hh>

#include <expr/expr.hh>
#include <expr/expr_mgr.hh>

#include <witness/witness.hh>
#include <witness/witness_mgr.hh>

#include <iostream>

UnsupportedFormat::UnsupportedFormat(pconst_char format)
    : f_format(strdup(format))
{}

const char* UnsupportedFormat::what() const throw()
{
    std::ostringstream oss;

    oss
        << "CommandError: format `"
        << f_format << "` is not supported.";

    return strdup(oss.str().c_str());
}

UnsupportedFormat::~UnsupportedFormat() throw()
{
    free(f_format);
}

DumpTrace::DumpTrace(Interpreter& owner)
    : Command(owner)
    , f_trace_id(NULL)
    , f_format(strdup(TRACE_FMT_DEFAULT))
    , f_output(NULL)
{}

DumpTrace::~DumpTrace()
{
    free(f_trace_id);
    free( (pchar) f_format);
    free(f_output);
}

void DumpTrace::set_format(pconst_char format)
{
    f_format = strdup(format);

    if (strcmp(f_format, TRACE_FMT_PLAIN) &&
        strcmp(f_format, TRACE_FMT_JSON) &&
        strcmp(f_format, TRACE_FMT_XML))

        throw UnsupportedFormat(f_format);
}

void DumpTrace::set_trace_id(pconst_char trace_id)
{
    free(f_trace_id);
    f_trace_id = strdup(trace_id);
}

void DumpTrace::set_output(pconst_char output)
{
    free(f_output);
    f_output = strdup(output);
}

void DumpTrace::dump_plain(std::ostream& os, Witness& w)
{
    ExprMgr& em
        (ExprMgr::INSTANCE());

    os
        << "Witness: "
        << w.id()
        << std::endl;

    for (step_t time = w.first_time(); time <= w.last_time(); ++ time) {

        os
            << "-- @"
            << time
            << std::endl;

        TimeFrame& tf
            (w[ time ]);

        SymbIter symbs( ModelMgr::INSTANCE().model(), NULL );
        while (symbs.has_next()) {

            std::pair< Expr_ptr, Symbol_ptr > pair
                (symbs.next());

            Symbol_ptr symb
                (pair.second);
            if (symb -> is_hidden())
                continue;

            Expr_ptr ctx
                (pair.first);
            Expr_ptr name
                (symb->name());
            Expr_ptr value
                (NULL);
            Expr_ptr full
                (em.make_dot( ctx, name));

            if (symb->is_variable())  {
                try {
                    value = tf.value(full);
                    os
                        << full << " = "
                        << value << std::endl;
                }
                catch (NoValue nv) {
                    // value = ExprMgr::INSTANCE().make_undef();
                }
            }
            else if (symb->is_define()) {
                Expr_ptr expr(symb->name());

                try {
                    value = WitnessMgr::INSTANCE().eval( w, ctx, expr, time);
                    os
                        << full  << " = "
                        << value << std::endl;
                }
                catch (NoValue nv) {
                    // value = ExprMgr::INSTANCE().make_undef();
                }
            }
            else
                continue;
        }

        os << std::endl;
    }
}

void DumpTrace::dump_json(std::ostream& os, Witness& w)
{
    ExprMgr& em
        (ExprMgr::INSTANCE());

    const char* FIRST_LVL
        ("    ");
    const char* SECOND_LVL
        ("              ");
    const char *THIRD_LVL
        ("                ");

    os
        << "{"
        << std::endl << FIRST_LVL << "\"id\": " << "\"" << w.id() << "\"" << ","
        << std::endl << FIRST_LVL << "\"steps\": [{" << std::endl;

    for (step_t time = w.first_time(); time <= w.last_time(); ++ time) {

        TimeFrame& tf
            (w[ time ]);

        SymbIter symbs
            ( ModelMgr::INSTANCE().model(), NULL );

        bool first
            (true);

        while (symbs.has_next()) {

            std::pair< Expr_ptr, Symbol_ptr > pair
                (symbs.next());

            Symbol_ptr symb
                (pair.second);

            if (symb -> is_hidden())
                continue;

            if ( !first )
                os
                    << ", "
                    << std::endl
                    ;

            else
                first = false;

            Expr_ptr ctx
                (pair.first);
            Expr_ptr name
                (symb->name());
            Expr_ptr value
                (NULL);
            Expr_ptr full
                (em.make_dot( ctx, name));

            if (symb->is_variable())  {
                try {
                    value = tf.value(full);
                    os
                        << THIRD_LVL
                        << "\"" << full << "\"" << ": "
                        << "\"" << value << "\""
                        ;
                }
                catch (NoValue nv) {
                    // value = ExprMgr::INSTANCE().make_undef();
                }
            }
            else if (symb->is_define()) {
                Expr_ptr expr(symb->name());

                try {
                    value = WitnessMgr::INSTANCE().eval( w, ctx, expr, time);
                    os
                        << THIRD_LVL
                        << "\"" << full << "\"" << ": "
                        << "\"" << value << "\""
                        ;
                }
                catch (NoValue nv) {
                    // value = ExprMgr::INSTANCE().make_undef();
                }
            }
            else
                continue;
        }

        os
            << std::endl;

        if (time < w.last_time())
            os
                << SECOND_LVL << "}, {"
                << std::endl;
        else
            os
                << SECOND_LVL << "}]"
                << std::endl;
    }

    os
        << "}"
        << std::endl;
}


void DumpTrace::process_time_frame(Witness& w, step_t time,
                                   ExprVector& input_vars_assignments,
                                   ExprVector& state_vars_assignments,
                                   ExprVector& defines_assignments)
{
    ExprMgr& em
        (ExprMgr::INSTANCE());

    WitnessMgr& wm
        (WitnessMgr::INSTANCE());

    TimeFrame& tf
        (w[time]);

    SymbIter symbs
        ( ModelMgr::INSTANCE().model(), NULL );

    while (symbs.has_next()) {

        std::pair< Expr_ptr, Symbol_ptr > pair
            (symbs.next());

        Symbol_ptr symb
            (pair.second);

        if (symb -> is_hidden())
            continue;

        Expr_ptr ctx
            (pair.first);
        Expr_ptr name
            (symb->name());
        Expr_ptr value
            (NULL);
        Expr_ptr full
            (em.make_dot( ctx, name));

        if (symb -> is_variable())  {

            Variable& var
                (symb -> as_variable());

            try {
                value = tf.value(full);
                if (var.is_input())
                    input_vars_assignments.push_back( em.make_eq( full, value));
                else
                    state_vars_assignments.push_back( em.make_eq( full, value));
            }
            catch (NoValue nv) {}
        }
        else if (symb -> is_define()) {
            Expr_ptr expr(symb->name());

            try {
                value = wm.eval( w, ctx, expr, time);
                defines_assignments.push_back( em.make_eq( full, value));
            }
            catch (NoValue nv) {}
        }
        else
            continue;
    }
}


void DumpTrace::dump_xml(std::ostream& os, Witness& w)
{
    ExprMgr& em
        (ExprMgr::INSTANCE());

    const char* FIRST_LVL
        ("    ");
    const char* SECOND_LVL
        ("        ");
    const char *THIRD_LVL
        ("            ");

    os
        << "<?xml version=\"1.0\">" << std::endl
        << "<witness id=\"" << w.id() << "\"" << ">" << std::endl
        ;

    for (step_t time = w.first_time(); time <= w.last_time(); ++ time) {
        os
            << FIRST_LVL
            << "<step time=\"" << time << "\">"
            << std::endl;

        ExprVector input_vars_assignments;
        ExprVector state_vars_assignments;
        ExprVector defines_assignments;
        process_time_frame(w, time,
                           input_vars_assignments,
                           state_vars_assignments,
                           defines_assignments);

         // -- input variables
         if (! input_vars_assignments.empty()) {

             os
                 << SECOND_LVL
                 << "<input-variables>"
                 << std::endl;

             for (ExprVector::const_iterator ei = input_vars_assignments.begin();
                  ei != input_vars_assignments.end(); ++ ei) {

                 Expr_ptr eq
                     (*ei);

                 os
                     << THIRD_LVL
                     << "<item name=\"" << eq -> lhs() << "\" "
                     << "value=\"" << eq -> rhs() << "\">"
                     << std::endl;
             }

             os
                 << SECOND_LVL
                 << "</input-variables>"
                 << std::endl;
         }

         // -- state variables
         if (! state_vars_assignments.empty()) {

             os
                 << SECOND_LVL
                 << "<state-variables>"
                 << std::endl;

             for (ExprVector::const_iterator ei = state_vars_assignments.begin();
                  ei != state_vars_assignments.end(); ++ ei) {

                 Expr_ptr eq
                     (*ei);

                 os
                     << THIRD_LVL
                     << "<item name=\"" << eq -> lhs() << "\" "
                     << "value=\"" << eq -> rhs() << "\">"
                     << std::endl;
             }

             os
                 << SECOND_LVL
                 << "</state-variables>"
                 << std::endl;
         }

         // -- defines
         if (! defines_assignments.empty()) {

             os
                 << SECOND_LVL
                 << "<defines>"
                 << std::endl;

             for (ExprVector::const_iterator ei = defines_assignments.begin();
                  ei != defines_assignments.end(); ++ ei) {

                 Expr_ptr eq
                     (*ei);

                 os
                     << THIRD_LVL
                     << "<item name=\"" << eq -> lhs() << "\" "
                     << "value=\"" << eq -> rhs() << "\">"
                     << std::endl;
             }

             os
                 << SECOND_LVL
                 << "</defines>"
                 << std::endl;
         }

         os
             << FIRST_LVL
             << "</step>"
             << std::endl;
    }

    os
        << "</witness>" << std::endl;
}

Variant DumpTrace::operator()()
{
    std::ostream &os
        (std::cout);

    Atom wid
        (f_trace_id
         ? f_trace_id
         : (char *) WitnessMgr::INSTANCE().current().id().c_str());

    Witness& w
        (WitnessMgr::INSTANCE().witness(wid));

    if (! strcmp( f_format, TRACE_FMT_PLAIN))
        dump_plain(os, w);

    else if (!strcmp( f_format, TRACE_FMT_JSON))
        dump_json(os, w);

    else if (!strcmp( f_format, TRACE_FMT_XML))
        dump_xml(os, w);

    else assert(false); /* unsupported */


    return Variant("Ok");
}

void DumpTrace::usage()
{
    std::cout
        << "dump-trace <trace_uid> - Dumps given trace."
        << std::endl;
}

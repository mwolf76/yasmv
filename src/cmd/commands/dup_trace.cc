/**
 * @file dup_trace.cc
 * @brief Command `dup-trace` class implementation.
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

#include <cstdlib>
#include <cstring>

#include <cmd/commands/commands.hh>
#include <cmd/commands/dup_trace.hh>

#include <expr/expr.hh>
#include <expr/expr_mgr.hh>

#include <witness/witness.hh>
#include <witness/witness_mgr.hh>

DupTrace::DupTrace(Interpreter& owner)
    : Command(owner)
    , f_trace_id(NULL)
    , f_duplicate_id(NULL)
{}

DupTrace::~DupTrace()
{
    if (f_trace_id)
        free (f_trace_id);

    if (f_duplicate_id)
        free (f_duplicate_id);
}

void DupTrace::set_trace_id(pconst_char trace_id)
{
    free(f_trace_id);
    f_trace_id = strdup(trace_id);
}

void DupTrace::set_duplicate_id(pconst_char duplicate_id)
{
    free(f_duplicate_id);
    f_duplicate_id = strdup(duplicate_id);
}

Variant DupTrace::operator()()
{
    /* FIXME: implement stream redirection for std{out,err} */
    std::ostream& out
        (std::cout);

    out
        << outPrefix
        << "WARNING: this commands currently does nothing!"
        << std::endl;

    return Variant(okMessage);
}

DupTraceTopic::DupTraceTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

DupTraceTopic::~DupTraceTopic()
{
    TRACE
        << "Destroyed dup-trace topic"
        << std::endl;
}

void DupTraceTopic::usage()
{
    std::cout
        << "dup-trace <trace_uid> - Dups given trace." ;
}

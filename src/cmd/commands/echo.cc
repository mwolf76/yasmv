
/**
 * @file echo.cc
 * @brief Command `echo` class implementation.
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

#include <algorithm>

#include <cmd/interpreter.hh>

#include <expr/expr_mgr.hh>

#include <witness/witness.hh>
#include <witness/witness_mgr.hh>

#include <cmd/commands/commands.hh>
#include <cmd/commands/echo.hh>

#include <iomanip>

Echo::Echo(Interpreter& owner)
    : Command(owner)
{}

Echo::~Echo()
{
}

void Echo::append_expression(Expr_ptr expr)
{
    f_expressions.push_back(expr);
}

Variant Echo::operator()()
{
    OptsMgr& om { OptsMgr::INSTANCE() } ;
    WitnessMgr& wm { WitnessMgr::INSTANCE() } ;

    /* FIXME: implement stream redirection for std{out,err} */
    std::ostream& out { std::cout };

    if (! om.quiet()) {
        out
            << outPrefix;
    }

    std::for_each(f_expressions.begin(),
                  f_expressions.end(),
                  [&](auto e)
                  {
                      Witness& current { wm.current() } ;
                      out
                          << wm.eval(current,
                                     ExprMgr::INSTANCE().make_empty(),
                                     e, current.last_time())
                          << " " ;
                  });

    out
        << std::endl;

    return Variant(okMessage);
}

EchoTopic::EchoTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

EchoTopic::~EchoTopic()
{
    TRACE
        << "Destroyed echo topic"
        << std::endl;
}

void EchoTopic::usage()
{
    std::cout
        << "echo <arg-1> . [...] <arg-n> - write arguments to the standard output.\n\n"
        << "Each argument can either be a string or a valid expression in current environment.\n" ;
}

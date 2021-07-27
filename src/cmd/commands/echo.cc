
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

namespace cmd {

Echo::Echo(Interpreter& owner)
    : Command(owner)
{}

Echo::~Echo()
{}

void Echo::append_expression(expr::Expr_ptr expr)
{
    f_expressions.push_back(expr);
}

utils::Variant Echo::operator()()
{
    opts::OptsMgr& om
        (opts::OptsMgr::INSTANCE());

    witness::WitnessMgr& wm
        (witness::WitnessMgr::INSTANCE());

    /* FIXME: implement stream redirection for std{out,err} */
    std::ostream& out
        (std::cout);

    if (! om.quiet()) {
        out
            << outPrefix;
    }

    /* TODO: not really compatible with the grammar... restrict to 1 expr */
    std::for_each(f_expressions.begin(),
                  f_expressions.end(),
                  [&](expr::Expr_ptr expr)
                  {
                      witness::Witness& current
                          (wm.current());

                      out
                          << wm.eval(current,
                                     expr::ExprMgr::INSTANCE().make_empty(),
                                     expr, current.last_time())
                          << " " ;
                  });

    out
        << std::endl;

    return utils::Variant(okMessage);
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
{ display_manpage("echo"); }

};

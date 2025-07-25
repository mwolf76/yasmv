/**
 * @file debug.cc
 * @brief Debug helpers.
 *
 * Copyright (C) 2012-2025 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
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
#include <cmd/cmd.hh>

#include <expr/expr.hh>
#include <expr/printer/printer.hh>

#include <model/model.hh>

#include <opts/opts_mgr.hh>

#include <parser/grammars/smvLexer.h>
#include <parser/grammars/smvParser.h>

#include <sat/sat.hh>

#include <boost/chrono.hpp>

std::string se(expr::Expr_ptr e)
{
    std::ostringstream oss;
    oss << e;
    return oss.str();
}

std::string sf(expr::TimedExpr e)
{
    std::ostringstream oss;
    oss << e;
    return oss.str();
}


std::string su(enc::UCBI& ucbi)
{
    std::ostringstream oss;
    oss << ucbi;
    return oss.str();
}

std::string st(enc::TCBI& tcbi)
{
    std::ostringstream oss;
    oss << tcbi;
    return oss.str();
}

std::string sd(compiler::InlinedOperatorDescriptor& md)
{
    std::ostringstream oss;
    oss << md;
    return oss.str();
}

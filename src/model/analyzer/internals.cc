 /**
 * @file internals.cc
 * @brief Semantic analyzer, internals implementation.
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

#include <common/common.hh>

#include <expr/expr.hh>
#include <type/type.hh>
#include <symb/proxy.hh>

#include <model/model_mgr.hh>
#include <model/analyzer/analyzer.hh>

void Analyzer::pre_hook()
{}
void Analyzer::post_hook()
{}

void Analyzer::pre_node_hook(Expr_ptr expr)
{
    f_expr_stack.push_back(expr);
}
void Analyzer::post_node_hook(Expr_ptr expr)
{
    f_expr_stack.pop_back();
}

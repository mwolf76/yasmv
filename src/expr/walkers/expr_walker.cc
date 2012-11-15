/**
 * @file expr_walker.cc
 * @brief Expression walker
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
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/
#include <common.hh>

#include <expr.hh>
#include <expr_walker.hh>

Walker::Walker()
{ // DRIVEL << "Initialized walker @" << this << endl;
}

Walker::~Walker()
{ // DRIVEL << "Deinitialized walker @" << this << endl;
}

Walker& Walker::operator() (const Expr_ptr expr)
{
    // pre-walking hook
    this->pre_hook();

    activation_record call(expr);

    // setup toplevel act. record and perform walk
    f_recursion_stack.push(call);
    walk();

    // post-walking hook
    this->post_hook();

    return *this;
}

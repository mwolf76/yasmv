/**
 *  @file printer.hh
 *  @brief Expr printer
 *
 *  This module contains definitions and services that implement an
 *  optimized storage for expressions. Expressions are stored in a
 *  Directed Acyclic Graph (DAG) for data sharing.
 *
 *  Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU Lesser General Public
 *  License as published by the Free Software Foundation; either
 *  version 2.1 of the License, or (at your option) any later version.
 *
 *  This library is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public
 *  License along with this library; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/

#ifndef PRINTER_H
#define PRINTER_H

#include <string>
#include <walker/walker.hh>

class Printer : public ExprWalker {
    std::ostream& f_os;

public:
    Printer(); // defaults to std::cout
    Printer(std::ostream& os);

    ~Printer();

    Printer& operator<<(const std::string& str);

    Printer& operator<<(Expr& expr);
    Printer& operator<<(Expr_ptr expr);

protected:
    void pre_hook();
    void post_hook();

    // support for LTL ops
    LTL_HOOKS;

    // support for basic ops
    OP_HOOKS;

    void walk_leaf(const Expr_ptr expr);
};

#endif

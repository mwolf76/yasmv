/**
 * @file echo.hh
 * @brief Command-interpreter subsystem related classes and definitions.
 *
 * This header file contains the handler inteface for the `echo`
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

#ifndef ECHO_H
#define ECHO_H

#include <cmd/command.hh>
class Echo : public Command {
    using expressions = std::vector<Expr_ptr>;
    expressions f_expressions;

public:
    Echo(Interpreter& owner);
    virtual ~Echo();

    void append_expression(Expr_ptr expression);

    Variant virtual operator()();
};
typedef Echo* Echo_ptr;

class EchoTopic : public CommandTopic {
public:
    EchoTopic(Interpreter& owner);
    virtual ~EchoTopic();

    void virtual usage();
};
#endif /* ECHO_H */

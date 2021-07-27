/**
 * @file set.hh
 * @brief Command-interpreter subsystem related classes and definitions.
 *
 * This header file contains the handler inteface for the `set`
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

#ifndef SET_CMD_H
#define SET_CMD_H

#include <cmd/command.hh>
#include <env/environment.hh>

class Set : public Command {

    expr::Expr_ptr f_identifier;
    expr::Expr_ptr f_value;

public:
    Set(Interpreter& owner);
    virtual ~Set();

    void set_identifier(expr::Expr_ptr id);
    void set_value(expr::Expr_ptr value);
    utils::Variant virtual operator()();
};
typedef Set* Set_ptr;

class SetTopic : public CommandTopic {
public:
    SetTopic(Interpreter& owner);
    virtual ~SetTopic();

    void virtual usage();
};

#endif /* SET_CMD_H */

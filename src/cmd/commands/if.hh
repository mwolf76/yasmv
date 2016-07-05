/*
 * @file if.hh
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
#ifndef IF_CMD_H
#define IF_CMD_H

#include <cmd/command.hh>
#include <algorithms/bmc/bmc.hh>

class If : public Command {

    /* the assigned symbol */
    Expr_ptr f_condition;

    /* laxy parsing? */
    Expr_ptr f_then_block;
    Expr_ptr f_else_block;

public:
    If(Interpreter& owner);
    virtual ~If();

    void set_condition(Expr_ptr f_condition);
    void set_then(Expr_ptr f_then_block);
    void set_else(Expr_ptr f_else_block);

    Variant virtual operator()();
};

class IfTopic : public CommandTopic {
public:
    IfTopic(Interpreter& owner);
    virtual ~IfTopic();

    void virtual usage();
};

#endif // IF_CMD_H

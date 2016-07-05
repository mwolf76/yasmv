/*
 * @file while.hh
 * @brief Command-interpreter subsystem related classes and definitions.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modwhiley it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; while not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fwhileth Floor, Boston, MA  02110-1301  USA
 *
 **/
#ifndef WHILE_CMD_H
#define WHILE_CMD_H

#include <cmd/command.hh>
#include <algorithms/bmc/bmc.hh>

class While : public Command {

    /* the assigned symbol */
    Expr_ptr f_condition;

    /* laxy parsing? */
    Expr_ptr f_inner_block;

public:
    While(Interpreter& owner);
    virtual ~While();

    void set_condition(Expr_ptr f_condition);
    void set_inner(Expr_ptr f_inner_block);

    Variant virtual operator()();
};

class WhileTopic : public CommandTopic {
public:
    WhileTopic(Interpreter& owner);
    virtual ~WhileTopic();

    void virtual usage();
};

#endif // WHILE_CMD_H

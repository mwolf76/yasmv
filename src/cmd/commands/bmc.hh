/**
 * @file bmc.hh
 * @brief Command-interpreter subsystem related classes and definitions.
 *
 * This header file contains the handler inteface for the `bmc`
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

#ifndef BMC_CMD_H
#define BMC_CMD_H

#include <cmd/command.hh>

class Bmc : public Command {
public:
    Bmc(Interpreter& owner);
    virtual ~Bmc();

    /** cmd params */
    void set_property(Expr_ptr property);
    void add_constraint(Expr_ptr constraint);

    /* run() */
    Variant virtual operator()();

private:
    std::ostream& f_out;

    /* the property to be verified */
    Expr_ptr f_property;

    /* (optional) additional constraints */
    ExprVector f_constraints;

    // -- helpers -------------------------------------------------------------
    bool check_requirements();
};

typedef Bmc* Bmc_ptr;

class BmcTopic : public CommandTopic {
public:
    BmcTopic(Interpreter& owner);
    virtual ~BmcTopic();

    void virtual usage();
};

#endif /* BMC_CMD_H */

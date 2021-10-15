/**
 * @file pick_state.hh
 * @brief Command-interpreter subsystem related classes and definitions.
 *
 * This header file contains the handler inteface for the `pick-state`
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

#ifndef PICK_STATE_CMD_H
#define PICK_STATE_CMD_H

#include <cmd/command.hh>
#include <algorithms/sim/simulation.hh>

namespace cmd {

class PickState : public Command {
public:
    PickState(Interpreter& owner);
    virtual ~PickState();

    /** cmd params */
    void add_constraint(expr::Expr_ptr constraint);

    void set_allsat(bool value);
    inline bool allsat() const
    { return f_allsat; }

    void set_count(bool value);
    inline bool count() const
    { return f_count; }

    void set_limit(value_t limit);
    inline value_t limit() const
    { return f_limit; }

    utils::Variant virtual operator()();

private:
    std::ostream& f_out;

    /* (optional) additional constraints */
    expr::ExprVector f_constraints;

    /* perform ALLSAT enumeration? */
    bool f_allsat;

    /* perform ALLSAT counting */
    bool f_count;

    /* ALLSAT enumeration/counting limit (optional) */
    unsigned f_limit;

    // -- helpers -------------------------------------------------------------
    bool check_requirements();

    void wrn_prefix();
    void out_prefix();
};

typedef PickState* PickState_ptr;

class PickStateTopic : public CommandTopic {
public:
    PickStateTopic(Interpreter& owner);
    virtual ~PickStateTopic();

    void virtual usage();
};

};
#endif /* PICK_STATE_CMD_H */

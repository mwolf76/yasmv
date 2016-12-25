/*
 * @file interpreter.hh
 * @brief Command interpreter subsystem declarations.
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

#ifndef INTERPRETER_H
#define INTERPRETER_H

#include <common/common.hh>

#include <iostream>
#include <boost/unordered_map.hpp>

#include <utils/pool.hh>

#include <opts/opts_mgr.hh>

#include <cmd/command.hh>

#include <env/environment.hh>

typedef class Interpreter* Interpreter_ptr;

class Command;
typedef Command* Command_ptr;

class CommandTopic;
typedef CommandTopic* CommandTopic_ptr;

class Interpreter {
public:
    // singleton
    static Interpreter& INSTANCE();

    // external commands (will be consumed and destroyed)
    Variant& operator()(Command_ptr cmd);

    // cmd loop
    Variant& operator()();

    inline Variant& last_result()
    { return f_last_result; }

    // true iff system is shutting down
    inline bool is_leaving() const
    { return f_leaving; }

    // process retcode
    inline int retcode() const
    { return f_retcode; }

    void quit(int retcode);

    inline unsigned epoch() const
    { return f_epoch; }

protected:
    friend class Command;

    Interpreter();
    virtual ~Interpreter();

    // for streams redirection
    inline std::istream& in() const
    { return *f_in; }

    inline std::ostream& out() const
    { return *f_out; }

    inline std::ostream& err() const
    { return *f_err; }

    int f_retcode;
    bool f_leaving;

    std::istream *f_in;
    std::ostream *f_out;
    std::ostream *f_err;

    Variant f_last_result;

    static Interpreter_ptr f_instance;
    unsigned f_epoch;
};

#endif /* INTERPRETER_H */

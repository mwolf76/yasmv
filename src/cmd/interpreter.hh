/*
 * @file interpreter.hh
 * @brief Command interpreter subsystem related classes and definitions.
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
#ifndef INTERPRETER_H
#define INTERPRETER_H

#include <common.hh>
#include <opts.hh>

#include <cmd/icommand.hh>
#include <cmd/job.hh>

typedef class Interpreter* Interpreter_ptr;
class Interpreter {
public:
    // singleton
    static Interpreter& INSTANCE();

    // external commands (will be consumed and destroyed)
    Variant& operator()(ICommand_ptr cmd);

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

    // background jobs
    inline const Jobs& jobs() const
    { return f_jobs; }

    void quit(int retcode);

protected:
    friend class ICommand;

    Interpreter();
    virtual ~Interpreter();

    // for streams redirection
    inline istream& in() const
    { return *f_in; }

    inline ostream& out() const
    { return *f_out; }

    inline ostream& err() const
    { return *f_err; }

    inline void prompt() const
    {
        bool color (OptsMgr::INSTANCE().color());
        if (color) {
            (*f_out) << normal << ">> ";
        }
        else {
            (*f_out) <<  ">> ";
        }
    }

    // jobs mgmt
    Jobs f_jobs;

    void register_job( Job& job );

    int f_retcode;
    bool f_leaving;

    istream *f_in;
    ostream *f_out;
    ostream *f_err;

    Variant f_last_result;

    static Interpreter_ptr f_instance;
};

#endif

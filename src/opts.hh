/**
 * @file opts.cc
 * @brief Command line options management
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
 **/
class OptsMgr;
typedef OptsMgr* OptsMgr_ptr;

#include <common.hh>
#include <boost/program_options.hpp>
namespace options = boost::program_options;

class OptsMgr {

public:
    static OptsMgr& INSTANCE() {
        if (! f_instance) f_instance = new OptsMgr();
        return (*f_instance);
    }

    // the usage message
    string usage() const;

    // true iff help has been required
    bool help() const;

    // required level of verbosity (defaults to 0)
    int verbosity() const;

    // model filename
    string model() const;

    // to be invoked by main
    void parse_command_line(int argc, const char **argv);

protected:
    OptsMgr();

private:
    static OptsMgr_ptr f_instance;

    /* local data */
    options::options_description f_desc;
    options::positional_options_description f_pos;
    options::variables_map f_vm;

    bool f_help;
};

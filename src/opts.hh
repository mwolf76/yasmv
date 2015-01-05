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

#ifndef OPTS_H
#define OPTS_H

class OptsMgr;
typedef OptsMgr* OptsMgr_ptr;

#include <common.hh>
#include <logging.hh>
#include <boost/program_options.hpp>

namespace options = boost::program_options;

// -- system defaults
const unsigned DEFAULT_WORD_WIDTH     = 16;
const unsigned DEFAULT_VERBOSITY      = 0;

class OptsMgr {

public:
    static OptsMgr& INSTANCE() {
        if (! f_instance)
            f_instance = new OptsMgr();

        return (*f_instance);
    }

    // the usage message
    string usage() const;

    // true iff help has been required
    bool help() const;

    // level of verbosity
    unsigned verbosity() const;

    // colorized
    bool color() const;

    // native word size in bits, used for algebrization of constant ITEs and arrays
    unsigned word_width() const;
    void set_word_width(unsigned);

    // model filename
    string model() const;

    // to be invoked by main
    void parse_command_line(int argc, const char **argv);

    // delegate
    axter::verbosity get_verbosity_level_tolerance();

protected:
    OptsMgr();

private:
    static OptsMgr_ptr f_instance;

    /* local data */
    options::options_description f_desc;
    options::positional_options_description f_pos;
    options::variables_map f_vm;

    bool f_help;
    bool f_color;
    bool f_started;
    unsigned f_word_width;
};

#endif

/**
 * @file opts.hh
 * @brief Command line options management
 *
 * This header file contains the declarations required by the options
 * management system.
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

#ifndef OPTS_H
#define OPTS_H

#include <boost/program_options.hpp>
#include <common/common.hh>

namespace opts {

    class OptsMgr;
    typedef OptsMgr* OptsMgr_ptr;

    // -- system defaults
    const unsigned DEFAULT_WORD_WIDTH = 16;
    const unsigned DEFAULT_PRECISION = 0;
    const unsigned DEFAULT_VERBOSITY = 0;

    class OptsMgr {

    public:
        static OptsMgr& INSTANCE()
        {
            if (!f_instance)
                f_instance = new OptsMgr();

            return (*f_instance);
        }

        // the usage message
        std::string usage() const;

        // true iff help has been required
        bool help() const;

        // level of verbosity
        unsigned verbosity() const;

        // quiet
        bool quiet() const;

        // colorized
        bool color() const;

        // native word size in bits, used for algebrization of constant ITEs and arrays
        unsigned word_width() const;
        void set_word_width(unsigned);

        // precision in bits, used for algebrization of constant ITEs and arrays
        unsigned precision() const;
        void set_precision(unsigned);

        // model filename
        std::string model() const;

        // to be invoked by main
        void parse_command_line(int argc, const char** argv);

        // delegate
        axter::verbosity get_verbosity_level_tolerance();

    protected:
        OptsMgr();

    private:
        static OptsMgr_ptr f_instance;

        /* local data */
        boost::program_options::options_description f_desc;
        boost::program_options::positional_options_description f_pos;
        boost::program_options::variables_map f_vm;

        bool f_help;
        bool f_quiet;
        bool f_color;
        bool f_started;
        bool f_version;

        unsigned f_word_width;
        unsigned f_precision;
    };

}; // namespace opts

#endif

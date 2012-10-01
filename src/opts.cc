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
#include "opts.hh"

// static initialization
OptsMgr_ptr OptsMgr::f_instance = NULL;

OptsMgr::OptsMgr()
    : f_desc("Program options")
    , f_pos()
    , f_vm()
    , f_help(false)
{
    f_desc.add_options()

        (
         "help",
         "produce help message"
         )

        (
         "verbosity",
         options::value<int>()->default_value(0),
         "verbosity level"
         )

        (
         "model",
         options::value<string>(),
         "input model"
         )
        ;

    // arguments are models
    f_pos.add("model", -1);
}

void OptsMgr::parse_command_line(int argc, const char **argv)
{
    options::store(options::command_line_parser(argc, const_cast<char **>(argv)).
                options(f_desc).positional(f_pos).run(), f_vm);

    options::notify(f_vm);
    if (f_vm.count("help")) {
        f_help = true;
    }
}

int OptsMgr::verbosity() const
{
    int res = f_vm["verbosity"].as<int>();
    return res;
}

string OptsMgr::model() const
{
    string res = "";

    if (f_vm.count("model")) {
        res = f_vm["model"].as<string>();
    }

    return res;
}

bool OptsMgr::help() const
{
    return f_help;
}

string OptsMgr::usage() const
{
    ostringstream oss;
    oss << f_desc;
    return oss.str();
}

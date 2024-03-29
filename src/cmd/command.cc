/*
 * @file command.cc
 * @brief Command-interpreter subsystem
 *
 * This header file contains the declarations required by the Command
 * class.
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

#include "command.hh"
#include <boost/filesystem.hpp>

#include <utils/logging.hh>

namespace cmd {

    void CommandTopic::display_manpage(const char* topic)
    {
        boost::filesystem::path fullpath { getenv(YASMV_HOME_PATH) };

        fullpath += "/help/";
        fullpath += topic;
        fullpath += ".nroff";

        std::stringstream oss;
        oss
            << "nroff "
            << fullpath.native()
            << " | less"
            << std::endl;

        const std::string& s { oss.str() };

        const char* tmp { s.c_str() };

        DEBUG
            << "##"
            << tmp
            << std::endl;

        execlp("bash", "bash", "-c", tmp, NULL);
    }

} // namespace cmd

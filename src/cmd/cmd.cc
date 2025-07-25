/*
 * @file cmd.cc
 * @brief Command-interpreter subsystem related classes and definitions.
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

#include <cmd.hh>

#include <boost/filesystem.hpp>

namespace cmd {
    CommandMgr_ptr CommandMgr::f_instance { NULL };
    CommandMgr& CommandMgr::INSTANCE()
    {
        if (!f_instance)
            f_instance = new CommandMgr();

        return (*f_instance);
    }

    CommandMgr::CommandMgr()
        : f_interpreter(Interpreter::INSTANCE())
    {
        const void* instance { this };

        DEBUG
            << "Initialized CommandMgr @"
            << instance
            << std::endl;
    }

    CommandMgr::~CommandMgr()
    {
        DEBUG
            << "Destroyed CommandMgr"
            << std::endl;
    }

    CommandTopics CommandMgr::topics() const
    {
        CommandTopics res;

        char* yasmv_home_path { getenv(YASMV_HOME_PATH) };
        if (NULL == yasmv_home_path) {
            ERR
                << "YASMV_HOME must be set to a valid directory."
                << std::endl;
            exit(1);
        }

        boost::filesystem::path help_path { yasmv_home_path };
        help_path += "/help/";

        TRACE
            << help_path
            << std::endl;

        try {
            if (exists(help_path) && is_directory(help_path)) {
                for (auto di = boost::filesystem::directory_iterator(help_path);
                     di != boost::filesystem::directory_iterator(); ++di) {

                    auto entry { di->path() };
                    if (entry.extension() != ".nroff") {
                        continue;
                    }

                    res.insert(entry.filename().stem().string());
                }
            } else {
                ERR
                    << "Path "
                    << help_path
                    << " does not exist or is not a readable directory."
                    << std::endl;

                /* leave immediately */
                exit(1);
            }
        } catch (const boost::filesystem::filesystem_error& fse) {
            pconst_char what { fse.what() };

            ERR
                << what
                << std::endl;

            /* leave immediately */
            exit(1);
        }

        return res;
    }

} // namespace cmd

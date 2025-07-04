/**
 * @file logging.hh
 * @brief Logging support
 *
 * This header file contains logging-related definitions and services
 * used throughout the whole program.
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

#ifndef LOGGING_H
#define LOGGING_H

#include <string>
#include <iostream>
#include <sstream>

#include <3rdparty/ezlogger/ezlogger_misc.hpp>
#include <time.h>

#include <common/strings.hh>

namespace axter {
    // custom format
    class ezlogger_format_policy  {

    public:
        inline static
        std::string get_log_prefix_format(const char*FileName,
                                          int LineNo, const char*FunctionName,
                                          ext_data levels_format_usage_data)
        {
            struct timespec now;
            clock_gettime(CLOCK_REALTIME, &now);

            std::string time_str { ctime(&now.tv_sec) };
            rtrim(time_str);

            std::ostringstream oss;
            oss
                << "[" << time_str << " +" << (now.tv_nsec / 1000000) << " ms] "
                << FileName << ":" << LineNo
                << " (" << FunctionName << ") ";

            return oss.str();
        }
    };

    extern std::string get_log_prefix_format(const char*FileName,
                                             int LineNo, const char*FunctionName,
                                             ext_data levels_format_usage_data);
};

#include <3rdparty/ezlogger/ezlogger_output_policy.hpp>
#include <3rdparty/ezlogger/ezlogger_verbosity_level_policy.hpp>
#include <3rdparty/ezlogger/ezlogger.hpp>
#include <3rdparty/ezlogger/ezlogger_macros.hpp>

// custom loggers
#define ERR                                                     \
    EZLOGGERVLSTREAM2(axter::log_verbosity_not_set, std::cerr)  \
    << "E :: "

#define WARN                                            \
    EZLOGGERVLSTREAM2(axter::log_always, std::cerr)     \
    << "W :: "

#define TRACE                                           \
    EZLOGGERVLSTREAM2(axter::log_often, std::cerr)      \
    << "T :: "

#define INFO                                            \
    EZLOGGERVLSTREAM2(axter::log_regularly, std::cerr)  \
    << "I :: "

#define DEBUG                                           \
    EZLOGGERVLSTREAM2(axter::log_rarely, std::cerr)     \
    << "D :: "

#define DRIVEL                                              \
    EZLOGGERVLSTREAM2(axter::log_very_rarely, std::cerr)    \
    << "V :: "

#endif /* LOGGING_H */

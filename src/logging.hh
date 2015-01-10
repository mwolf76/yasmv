/**
 * @file logging.hh
 * @brief Logging support
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

#ifndef LOGGING_H
#define LOGGING_H

#include <iostream>
#include <sstream>
#include <string>

#include "ezlogger_misc.hpp"
#include <sys/timeb.h>

namespace axter {
    // custom format
    class ezlogger_format_policy  {

    public:
        inline static
        std::string get_log_prefix_format(const char*FileName,
                                          int LineNo, const char*FunctionName,
                                          ext_data levels_format_usage_data)
        {
            struct timeb now;

            const std::string filename(FileName);
            const std::string funcname(FunctionName);

            std::ostringstream oss;

            ftime(&now);
            std::string timestr = ctime(&now.time);
            if (timestr.size()) timestr[timestr.size() -1] = ']';

            oss << "[" << timestr << "." << now.millitm << " "
                << filename << ":" << LineNo << " :: "  ;

            return oss.str().c_str();
        }
    };

    extern std::string get_log_prefix_format(const char*FileName,
                                             int LineNo, const char*FunctionName,
                                             ext_data levels_format_usage_data);
};


#include "ezlogger_output_policy.hpp"
#include "ezlogger_verbosity_level_policy.hpp"
#include "ezlogger.hpp"
#include "ezlogger_macros.hpp"

// custom loggers
#define ERR  EZLOGGERVLSTREAM2(axter::log_verbosity_not_set, std::cerr)
#define WARN EZLOGGERVLSTREAM2(axter::log_always, std::cerr)
#define TRACE EZLOGGERVLSTREAM2(axter::log_often, std::cerr)
#define INFO EZLOGGERVLSTREAM2(axter::log_regularly, std::cerr)
#define DEBUG EZLOGGERVLSTREAM2(axter::log_rarely, std::cerr)
#define DRIVEL EZLOGGERVLSTREAM2(axter::log_very_rarely, std::cerr)
#endif

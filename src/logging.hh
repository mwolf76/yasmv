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

#include "ezlogger_misc.hpp"

namespace axter {
    // custom format
    class ezlogger_format_policy  {

    public:
        inline static
        std::string get_log_prefix_format(const char*FileName,
                                          int LineNo, const char*FunctionName,
                                          ext_data levels_format_usage_data)
        {
            const string filename(FileName);
            const string funcname(FunctionName);

            ostringstream oss;

            time_t t = time(0) ;
            string tmp = ctime(&t);
            if (tmp.size()) tmp[tmp.size() -1] = ']';

            oss << "[" << tmp << "] "
                << filename << ":" << LineNo << " "
                << "(lvl = " << levels_format_usage_data.m_severity_level << ") :: "
                ;

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
#define ERR  EZLOGGERVLSTREAM2(axter::log_verbosity_not_set, cerr)
#define WARN EZLOGGERVLSTREAM2(axter::log_always, cerr)
#define TRACE EZLOGGERVLSTREAM2(axter::log_often, cerr)
#define INFO EZLOGGERVLSTREAM2(axter::log_regularly, cerr)
#define DEBUG EZLOGGERVLSTREAM2(axter::log_rarely, cerr)
#define DRIVEL EZLOGGERVLSTREAM2(axter::log_very_rarely, cerr)
#endif

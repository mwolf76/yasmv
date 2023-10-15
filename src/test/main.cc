/**
 * @file tests
 * @brief Program main body for the unit tests executable.
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

#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE tests

#include <boost/test/unit_test.hpp>

/* tests placeholders */
BOOST_AUTO_TEST_SUITE(tests)
BOOST_AUTO_TEST_SUITE_END()

#include <expr/expr.hh>

#include <common/common.hh>
#include <common/logging.hh>

// just for debugging purposes within gdb
void pe(expr::Expr_ptr e)
{
    std::cerr
        << e
        << std::endl;
}

// logging subsystem settings
namespace axter {
    std::string get_log_prefix_format(const char* FileName,
                                      int LineNo, const char* FunctionName,
                                      ext_data levels_format_usage_data)
    {

        return ezlogger_format_policy::
            get_log_prefix_format(FileName, LineNo, FunctionName,
                                  levels_format_usage_data);
    }

    std::ostream& get_log_stream()
    {
        return ezlogger_output_policy::get_log_stream();
    }

    verbosity get_verbosity_level_tolerance()
    {
        return log_always; // log_very_rarely; //
    }
}; // namespace axter

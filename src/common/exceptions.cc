/**
 * @file common/exceptions.cc
 * @brief System-wide definitions, base exception class implementation.
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

#include <common/exceptions.hh>

#include <string>
#include <sstream>

Exception::Exception(const std::string& type,
                     const std::string& subtype,
                     const std::string& message)
{
    std::ostringstream oss;

    oss
        << type
        << "/"
        << subtype;

    if (0 < message.length()) {
        oss
            << ": "
            << message ;
    }

    f_what = oss.str();
}

Exception::~Exception() throw()
{}

const char* Exception::what() const throw()
{
    return f_what.c_str();
}


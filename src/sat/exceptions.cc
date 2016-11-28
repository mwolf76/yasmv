/**
 * @file sat/exceptions.cc
 * @brief SAT implementation, exception classes implementation.
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

#include <sat/exceptions.hh>
#include <utils/misc.hh>

InlinedOperatorLoaderException::InlinedOperatorLoaderException(const InlinedOperatorSignature& ios)
    : f_ios(ios)
{}

const char* InlinedOperatorLoaderException::what() const throw()
{
    std::ostringstream oss;

    oss
        << "InlinedOperatorLoaderException: can not instantiate loader for operator `"
        << f_ios << "`";

    return oss2cstr(oss);
}


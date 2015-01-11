/**
 *  @file exceptions.cc
 *
 *  Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU Lesser General Public
 *  License as published by the Free Software Foundation; either
 *  version 2.1 of the License, or (at your option) any later version.
 *
 *  This library is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public
 *  License along with this library; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/
#include <sstream>

#include <type/type.hh>

BadType::BadType(Type_ptr tp)
    : f_repr(tp -> repr())
{}

BadType::~BadType() throw()
{}

const char* BadType::what() const throw()
{
    std::ostringstream oss;
    oss
        << "TypeError: operand has invalid type `"
        << f_repr << "`";

    return oss.str().c_str();
}

TypeMismatch::TypeMismatch(Type_ptr lhs, Type_ptr rhs)
    : f_repr_a(lhs -> repr())
    , f_repr_b(rhs -> repr())
{
    // Ehm?!?
    std::cout << "thomas";
}

TypeMismatch::~TypeMismatch() throw()
{}

const char* TypeMismatch::what() const throw()
{
    std::ostringstream oss;
    oss << "TypeError: "
        << f_repr_a << " and "
        << f_repr_b << " do not match";

    return oss.str().c_str();
}


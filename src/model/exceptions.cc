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

#include <model.hh>

ModuleNotFound::ModuleNotFound(Expr_ptr module_name)
    : f_module_name(module_name)
{}

const char* ModuleNotFound::what() const throw()
{
    std::ostringstream oss;
    oss
        << "Module not found: `"
        << f_module_name << "`";

    return oss.str().c_str();
}

DuplicateIdentifier::DuplicateIdentifier(Expr_ptr duplicate)
    : f_duplicate(duplicate)
{}

const char* DuplicateIdentifier::what() const throw()
{
    std::ostringstream oss;
    oss
        << "Duplicate identifier: `"
        << f_duplicate << "`";

    return oss.str().c_str();
}

BadParamCount::BadParamCount(Expr_ptr instance, unsigned expected, unsigned got)
    : f_instance(instance)
    , f_expected(expected)
    , f_got(got)
{}

const char* BadParamCount::what() const throw()
{
    std::ostringstream oss;
    oss
        << "Wrong parameters count in `"
        << f_instance << "`, "
        << f_expected << " expected, "
        << " got " << f_got;

    return oss.str().c_str();
}

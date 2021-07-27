/**
 * @file exceptions.cc
 * @brief Model management subsystem, exception classes implementation.
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

#include <common/common.hh>
#include <expr/expr.hh>
#include <model/exceptions.hh>
#include <utils/misc.hh>

#include <sstream>
#include <string>

static std::string build_module_not_found_error_message(expr::Expr_ptr expr)
{
    std::ostringstream oss;

    oss
        << "Module not found: `"
        << expr
        << "`";

    return oss.str();
}

ModuleNotFound::ModuleNotFound(expr::Expr_ptr module_name)
    : ModelException("ModuleNotFound",
                     build_module_not_found_error_message(module_name))
{}

static std::string build_main_module_not_found_error_message()
{
    std::ostringstream oss;

    oss
        << "Main module not found";

    return oss.str();
}

MainModuleNotFound::MainModuleNotFound()
    : ModelException("MainModuleNotFound",
                     build_main_module_not_found_error_message())
{}

static std::string build_duplicate_identifier_error_message(expr::Expr_ptr expr)
{
    std::ostringstream oss;
    oss
        << "identifier: `"
        << expr
        << "`";

    return oss.str();
}

DuplicateIdentifier::DuplicateIdentifier(expr::Expr_ptr duplicate)
    : ModelException("DuplicateIdentifier",
                     build_duplicate_identifier_error_message(duplicate))
{}

static std::string build_unknown_identifier_error_message(expr::Expr_ptr expr)
{
    std::ostringstream oss;

    oss
        << "Unknown identifier: `"
        << expr
        << "`";

    return oss.str();
}

UnknownIdentifier::UnknownIdentifier(expr::Expr_ptr unknown)
    : ModelException("UnknownIdentifier",
                     build_unknown_identifier_error_message(unknown))
{}

static std::string build_bad_param_count_error_message(expr::Expr_ptr instance,
                                                       unsigned expected,
                                                       unsigned got)
{
    std::ostringstream oss;

    oss
        << "Wrong parameters count in `"
        << instance
        << "`, "
        << expected
        << " expected, "
        << " got "
        << got;

    return oss.str();
}

BadParamCount::BadParamCount(expr::Expr_ptr instance, unsigned expected, unsigned got)
    : ModelException("BadParamCount",
                     build_bad_param_count_error_message(instance, expected, got))
{}

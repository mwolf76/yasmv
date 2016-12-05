/**
 * @file expr/walker/exceptions.hh
 * @brief Expression walker pattern implementation, exception class declarations.
 *
 * This header file contains the declarations required by the Expression
 * Walker class.
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
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/

#ifndef EXPR_WALKER_EXCEPTIONS_H
#define EXPR_WALKER_EXCEPTIONS_H

#include <common/common.hh>
#include <expr/walker/typedefs.hh>
#include <utils/misc.hh>

class WalkerException : public Exception {
public:
    WalkerException(const std::string& subtype,
                    const std::string& message="(no message)")
        : Exception("WalkerException", subtype, message)
    {}
};

// raised when the walker has encountered an unsupported entry point
class UnsupportedEntryPoint : public WalkerException {
public:
    UnsupportedEntryPoint(entry_point ep)
        : WalkerException("UnsupportedEntryPoint",
                          "encountered " + ep)
    {}
};

// raised when the walker has encountered an unsupported operator
class UnsupportedOperator : public WalkerException {
public:
    UnsupportedOperator(ExprType et)
        : WalkerException("UnsupportedOperator",
                          "encountered " + et)
    {}
};

class UnsupportedLeaf : public WalkerException {
public:
    UnsupportedLeaf()
        : WalkerException("UnsupportedLeaf")
    {}
};

class InternalError : public WalkerException {
public:
    InternalError(const std::string& message)
        : WalkerException("InternalError", message)
    {}
};

#endif /* EXPR_WALKER_EXCEPTIONS_H */

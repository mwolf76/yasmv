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

class WalkerException : public Exception
{
public:
    virtual const char* what() const throw() =0;
};

// raised when the walker has encountered a null expression
class NullExpressionException : public WalkerException {
public:
    NullExpressionException()
    {}

    virtual const char* what() const throw() {
        std::ostringstream oss;
        oss
            << "null expression encountered"
            << std::endl;


        return oss2cstr(oss);
    }
};

// raised when the walker has encountered an unsupported entry point
class UnsupportedEntryPointException : public WalkerException {
public:
    UnsupportedEntryPointException(entry_point ep)
        : f_ep(ep)
    {}

    virtual const char* what() const throw() {
        std::ostringstream oss;
        oss
            << "Unsupported entry point (" << f_ep << ")";

        return oss2cstr(oss);
    }

private:
    entry_point f_ep;
};

// raised when the walker has encountered an unsupported operator
class UnsupportedOperatorException : public WalkerException {
public:
    UnsupportedOperatorException(ExprType et)
        : f_et(et)
    {}

    virtual const char* what() const throw() {
        std::ostringstream oss;
        oss
            << "Unsupported operator (" << f_et << ")"
            << std::endl;

        return oss2cstr(oss);
    }

private:
    ExprType f_et;
};

class UnsupportedLeaf : public WalkerException {
public:

    virtual const char* what() const throw() {
        std::ostringstream oss;
        oss
            << "Unsupported leaf encountered"
            << std::endl
            ;

        return oss2cstr(oss);
    }
};

class InternalError : public WalkerException {
public:
    InternalError(std::string message)
        : f_message(message)
    {}

    virtual const char* what() const throw() {
        std::ostringstream oss;

        oss
            << "Internal error: "
            << f_message
            << std::endl;

        return oss2cstr(oss);
    }

    virtual ~InternalError() throw() {}

private:
    std::string f_message;
};

#endif /* EXPR_WALKER_EXCEPTIONS_H */

/**
 * @file expr/exceptions.hh
 * @brief Expr system module header file, exception classes.
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

#ifndef EXPR_EXCEPTIONS_H
#define EXPR_EXCEPTIONS_H

namespace expr {

/** Exception classes */
class ExprException : public Exception {
public:
    ExprException(const std::string& subexpr,
                  const std::string& message="")
        : Exception("ExprException", subexpr, message)
    {}
};

};

#endif /* EXPR_EXCEPTIONS_H */

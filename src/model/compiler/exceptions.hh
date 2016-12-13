/**
 * @file exceptions.hh
 * @brief Propositional logic compiler
 *
 * This header file contains the declaration of exceptions required by
 * the compiler.
 *
 * Copyright (C) 2011-2015 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 2.1 of
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

#ifndef COMPILER_EXCEPTIONS_H
#define COMPILER_EXCEPTIONS_H

#include <common/common.hh>
#include <model/exceptions.hh>

/** Exception classes */
class CompilerException : public Exception {
public:
    CompilerException(const std::string& subtype,
                      const std::string& message="")
        : Exception("CompilerException", subtype, message)
    {}
};

/** Raised when a constant could not fit into a native word */
class ConstantTooLarge : public CompilerException {
public:
    ConstantTooLarge(Expr_ptr expr);
};

class UnexpectedExpression : public CompilerException {
public:
    UnexpectedExpression(Expr_ptr expr);
};

#endif /* COMPILER_EXCEPTIONS_H */

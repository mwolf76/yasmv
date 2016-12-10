/**
 * @file model/exceptions.hh
 * @brief Model module header file, exception classes declarations.
 *
 * This header file contains the declarations required by the Model
 * class and its dependencies.
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
#ifndef MODEL_EXCEPTIONS_H
#define MODEL_EXCEPTIONS_H

#include <common/common.hh>
#include <expr/expr.hh>

class ModelException : public Exception {
public:
    ModelException(const std::string& subtype,
                   const std::string& message="")
        : Exception("ModelException", subtype, message)
    {}
};

class SemanticError : public ModelException {
public:
    SemanticError(const std::string &message)
        : ModelException("SemanticError", message)
    {}
};

class ModuleNotFound : public ModelException {
public:
    ModuleNotFound(Expr_ptr expr);
};

class MainModuleNotFound : public ModelException {
public:
    MainModuleNotFound();
};

class DuplicateIdentifier : public ModelException {
public:
    DuplicateIdentifier(Expr_ptr expr);
};

class UnknownIdentifier : public ModelException {
public:
    UnknownIdentifier(Expr_ptr expr);
};

class BadParamCount : public ModelException {
public:
    BadParamCount(Expr_ptr instance, unsigned expected, unsigned got);
};

#endif /* MODEL_EXCEPTIONS_H */

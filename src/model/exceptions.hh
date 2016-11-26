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

class ModelException : public Exception {
public:
    virtual const char* what() const throw() =0;
};

class ModuleNotFound : public ModelException {
public:
    ModuleNotFound(Expr_ptr expr);
    const char* what() const throw();

private:
    Expr_ptr f_module_name;
};

class MainModuleNotFound : public ModelException {
public:
    MainModuleNotFound();
    const char* what() const throw();
};

class DuplicateIdentifier : public ModelException {
public:
    DuplicateIdentifier(Expr_ptr expr);
    const char* what() const throw();

private:
    Expr_ptr f_duplicate;
};

class UnknownIdentifier : public ModelException {
public:
    UnknownIdentifier(Expr_ptr expr);
    const char* what() const throw();

private:
    Expr_ptr f_unknown;
};

class BadParamCount : public ModelException {
public:
    BadParamCount(Expr_ptr instance, unsigned expected, unsigned got);
    const char* what() const throw();

private:
    Expr_ptr f_instance;
    unsigned f_expected;
    unsigned f_got;
};

#endif /* MODEL_EXCEPTIONS_H */

/**
 * @file symb/classes.hh
 * @brief Symbol interface, symbol classes
 *
 * This header file contains the declarations required by the symbol
 * resolver.
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

#ifndef SYMBOL_CLASSES_H
#define SYMBOL_CLASSES_H

#include <common/common.hh>

#include <expr/expr.hh>
#include <utils/pool.hh>

#include <type/typedefs.hh>

#include <parser/grammars/grammar.hh>

#include <vector>
#include <utility>

namespace symb {

class Typed {
public:
    virtual const Type_ptr type() const =0;
};

class Value {
public:
    virtual value_t value() const =0;
};

class Body {
public:
    virtual const expr::Expr_ptr body() const =0;
};

class Params {
public:
    virtual const expr::ExprVector& formals() const =0;
};

class Symbol {
public:
    Symbol()
        : f_format(FORMAT_DEFAULT)
        , f_hidden(false)
    {}

    virtual const expr::Expr_ptr module()  const =0;
    virtual const expr::Expr_ptr name() const =0;

    bool is_const() const;
    Constant& as_const() const;

    bool is_literal() const;
    Literal& as_literal() const;

    bool is_variable() const;
    Variable& as_variable() const;

    bool is_parameter() const;
    Parameter& as_parameter() const;

    bool is_define() const;
    Define& as_define() const;

    bool is_hidden() const;
    void set_hidden(bool value);

    value_format_t format() const
    { return f_format; }

    void set_format(value_format_t fmt)
    { f_format = fmt; }

protected:
    value_format_t f_format;

private:
    bool f_hidden;
};

class Constant
    : public Symbol
    , public Typed
    , public Value
{
    expr::Expr_ptr f_module;
    expr::Expr_ptr f_name;
    Type_ptr f_type;
    value_t f_value;

public:
    Constant(const expr::Expr_ptr module, const expr::Expr_ptr name, Type_ptr type, value_t value)
        : f_module(module)
        , f_name(name)
        , f_type(type)
        , f_value(value)
    {}

    const expr::Expr_ptr module() const
    { return f_module; }

    const expr::Expr_ptr name() const
    { return f_name; }

    const Type_ptr type() const
    { return f_type; }

    value_t value() const
    { return f_value; }
};

class Variable
    : public Symbol
    , public Typed
{
    expr::Expr_ptr f_module;
    expr::Expr_ptr f_name;
    Type_ptr f_type;
    bool     f_input;
    bool     f_temp;
    bool     f_frozen;
    bool     f_inertial;

public:
    Variable(expr::Expr_ptr module, expr::Expr_ptr name, Type_ptr type)
        : f_module(module)
        , f_name(name)
        , f_type(type)
        , f_input(false)
        , f_temp(false)
        , f_frozen(false)
        , f_inertial(false)
    {}

    const expr::Expr_ptr module() const
    { return f_module; }

    const expr::Expr_ptr name() const
    { return f_name; }

    const Type_ptr type() const
    { return f_type; }

    void set_input(bool value)
    { f_input = value; }

    inline bool is_input() const
    { return f_input; }

    void set_inertial(bool value)
    { f_inertial = value; }

    inline bool is_inertial() const
    { return f_inertial; }

    void set_frozen(bool value)
    { f_frozen = value; }

    inline bool is_frozen() const
    { return f_frozen; }

    void set_temp(bool value)
    { f_temp = value; }

    inline bool is_temp() const
    { return f_temp; }
};

class Parameter
    : public Symbol
    , public Typed
{
    expr::Expr_ptr f_module;
    expr::Expr_ptr f_name;
    Type_ptr f_type;

public:
    Parameter(expr::Expr_ptr module, expr::Expr_ptr name, Type_ptr type)
        : f_module(module)
        , f_name(name)
        , f_type(type)
    {}

    const expr::Expr_ptr module() const
    { return f_module; }

    const expr::Expr_ptr name() const
    { return f_name; }

    const Type_ptr type() const
    { return f_type; }

};

class Literal
    : public Symbol
    , public Typed
{
    const expr::Expr_ptr f_name;
    const Type_ptr f_type;
    const value_t f_value;

public:
    Literal(const expr::Expr_ptr name, const Type_ptr type, value_t value)
        : f_name(name)
        , f_type(type)
        , f_value(value)
    {}

    virtual const expr::Expr_ptr module() const
    { return NULL; }

    virtual const expr::Expr_ptr name() const
    { return f_name; }

    virtual const Type_ptr type() const
    { return f_type; }

    virtual const value_t value() const
    { return f_value; }
};

class Define
    : public Symbol
    , public Body
{
    const expr::Expr_ptr f_module;
    const expr::Expr_ptr f_name;
    const expr::Expr_ptr f_body;

public:
    Define(const expr::Expr_ptr module, const expr::Expr_ptr name, const expr::Expr_ptr body)
        : f_module(module)
        , f_name(name)
        , f_body(body)
    {}

    const expr::Expr_ptr module() const
    { return f_module; }

    const expr::Expr_ptr name() const
    { return f_name; }

    const expr::Expr_ptr body() const
    { return f_body; }
};

};

#endif /* SYMBOL_CLASSES_H */

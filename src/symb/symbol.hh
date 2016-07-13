/**
 *  @file symbol.hh
 *  @brief Symbol interface
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

#ifndef SYMBOL_H
#define SYMBOL_H

#include <common.hh>

#include <boost/unordered_map.hpp>

#include <expr/expr.hh>
#include <utils/pool.hh>

#include <type/type.hh>

#include <vector>
#include <utility>

class UnresolvedSymbol : public Exception {
    Expr_ptr f_expr;

public:
    UnresolvedSymbol(Expr_ptr expr);
    const char* what() const throw();
};

class Symbol;
typedef Symbol* Symbol_ptr;
typedef boost::unordered_map<Expr_ptr, Symbol_ptr, PtrHash, PtrEq> Symbols;

class Literal;
typedef Literal* Literal_ptr;
typedef boost::unordered_map<Expr_ptr, Literal_ptr, PtrHash, PtrEq> Literals;

class Constant;
typedef Constant* Constant_ptr;
typedef boost::unordered_map<Expr_ptr, Constant_ptr, PtrHash, PtrEq> Constants;

class Variable;
typedef Variable* Variable_ptr;
typedef boost::unordered_map<Expr_ptr, Variable_ptr, PtrHash, PtrEq> Variables;

class Parameter;
typedef Parameter* Parameter_ptr;
typedef std::vector< std::pair< Expr_ptr, Parameter_ptr > > Parameters;

class Define;
typedef Define* Define_ptr;
typedef boost::unordered_map<Expr_ptr, Define_ptr, PtrHash, PtrEq> Defines;

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
    virtual const Expr_ptr body() const =0;
};

class Params {
public:
    virtual const ExprVector& formals() const =0;
};

typedef enum {
    VALUE_MODIFIER_UNDEFINED,
    VALUE_MODIFIER_BINARY,
    VALUE_MODIFIER_OCTAL,
    VALUE_MODIFIER_DECIMAL,
    VALUE_MODIFIER_HEXADECIMAL
} value_modifier_t;

class Symbol {
public:
    Symbol()
        : f_binary(false)
        , f_octal(false)
        , f_decimal(false)
        , f_hexadecimal(false)
        , f_hidden(false)
    {}

    virtual const Expr_ptr module()  const =0;
    virtual const Expr_ptr name() const =0;

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

    /* format modifiers */
    bool is_hidden() const;
    void set_hidden(bool value);

    bool is_binary() const;
    void set_binary(bool value);

    bool is_octal() const;
    void set_octal(bool value);

    bool is_decimal() const;
    void set_decimal(bool value);

    bool is_hexadecimal() const;
    void set_hexadecimal(bool value);

protected:
    bool f_binary;
    bool f_octal;
    bool f_decimal;
    bool f_hexadecimal;

private:
    bool f_hidden;
};

class Constant
    : public Symbol
    , public Typed
    , public Value
{
    Expr_ptr f_module;
    Expr_ptr f_name;
    Type_ptr f_type;
    value_t f_value;

public:
    Constant(const Expr_ptr module, const Expr_ptr name, Type_ptr type, value_t value)
        : f_module(module)
        , f_name(name)
        , f_type(type)
        , f_value(value)
    {}

    const Expr_ptr module() const
    { return f_module; }

    const Expr_ptr name() const
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
    Expr_ptr f_module;
    Expr_ptr f_name;
    Type_ptr f_type;
    bool     f_input;
    bool     f_temp;
    bool     f_frozen;

public:
    Variable(Expr_ptr module, Expr_ptr name, Type_ptr type)
        : f_module(module)
        , f_name(name)
        , f_type(type)
        , f_input(false)
        , f_temp(false)
        , f_frozen(false)
    {}

    const Expr_ptr module() const
    { return f_module; }

    const Expr_ptr name() const
    { return f_name; }

    const Type_ptr type() const
    { return f_type; }

    void set_input(bool value)
    { f_input = value; }

    inline bool is_input() const
    { return f_input; }

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
    Expr_ptr f_module;
    Expr_ptr f_name;
    Type_ptr f_type;

public:
    Parameter(Expr_ptr module, Expr_ptr name, Type_ptr type)
        : f_module(module)
        , f_name(name)
        , f_type(type)
    {}

    const Expr_ptr module() const
    { return f_module; }

    const Expr_ptr name() const
    { return f_name; }

    const Type_ptr type() const
    { return f_type; }

};

class Literal
    : public Symbol
    , public Typed
{
    const Expr_ptr f_name;
    const Type_ptr f_type;
    const value_t f_value;

public:
    Literal(const Expr_ptr name, const Type_ptr type, value_t value)
        : f_name(name)
        , f_type(type)
        , f_value(value)
    {}

    virtual const Expr_ptr module() const
    { return NULL; }

    virtual const Expr_ptr name() const
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
    const Expr_ptr f_module;
    const Expr_ptr f_name;
    const Expr_ptr f_body;

public:
    Define(const Expr_ptr module, const Expr_ptr name, const Expr_ptr body)
        : f_module(module)
        , f_name(name)
        , f_body(body)
    {}

    const Expr_ptr module() const
    { return f_module; }

    const Expr_ptr name() const
    { return f_name; }

    const Expr_ptr body() const
    { return f_body; }
};


/**
 * Symbol iterator
 *
 * COI aware
 * Preserves ordering
 *
 */
class Model;
class SymbIter {
public:
    /* Calculates COI if formula is non-NULL */
    SymbIter(Model& model, Expr_ptr formula = NULL);

    ~SymbIter();

    /* true iff there are more symbols to be processed */
    inline bool has_next() const
    { return f_iter != f_symbols.end(); }

    inline std::pair <Expr_ptr, Symbol_ptr> next()
    {
        std::pair< Expr_ptr, Symbol_ptr> res = (* f_iter);
        ++ f_iter;

        return res;
    }

private:
    Model&  f_model;
    Expr_ptr f_formula; /* for COI */

    std::vector< std::pair< Expr_ptr, Symbol_ptr > >f_symbols;
    std::vector< std::pair< Expr_ptr, Symbol_ptr> >::const_iterator f_iter;
};

#endif

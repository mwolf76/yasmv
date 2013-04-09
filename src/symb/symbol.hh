/**
 *  @file symbol.hh
 *  @brief Symbol interface
 *
 *  This module contains definitions and services that implement an
 *  optimized storage for expressions. Expressions are stored in a
 *  Directed Acyclic Graph (DAG) for data sharing.
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
#include <expr.hh>
#include <pool.hh>
#include <type.hh>

typedef vector<FQExpr> FQExprVector;

class ISymbol;
typedef ISymbol* ISymbol_ptr;
typedef unordered_map<FQExpr, ISymbol_ptr, FQExprHash, FQExprEq> Symbols;

class ILiteral;
typedef ILiteral* ILiteral_ptr;
typedef unordered_map<FQExpr, ILiteral_ptr, FQExprHash, FQExprEq> Literals;

class IEnum;
typedef IEnum* IEnum_ptr;
typedef unordered_map<FQExpr, IEnum_ptr, FQExprHash, FQExprEq> Enums;

class IConstant;
typedef IConstant* IConstant_ptr;
typedef unordered_map<FQExpr, IConstant_ptr, FQExprHash, FQExprEq> Constants;

class IArray;
typedef IArray* IArray_ptr;

class IVariable;
typedef IVariable* IVariable_ptr;
typedef unordered_map<FQExpr, IVariable_ptr, FQExprHash, FQExprEq> Variables;

class ITemporary;
typedef ITemporary* ITemporary_ptr;
typedef unordered_map<FQExpr, ITemporary_ptr, FQExprHash, FQExprEq> Temporaries;

class IDefine;
typedef IDefine* IDefine_ptr;
typedef unordered_map<FQExpr, IDefine_ptr, FQExprHash, FQExprEq> Defines;

class ITyped : IObject {
public:
    virtual const Type_ptr type() const =0;
};

class IValue : IObject {
public:
    virtual value_t value() const =0;
};

class ISymbol : IObject {
public:
    virtual const Expr_ptr ctx()  const =0;
    virtual const Expr_ptr expr() const =0;

    bool is_const() const;
    IConstant& as_const() const;

    bool is_literal() const;
    ILiteral& as_literal() const;

    bool is_variable() const;
    IVariable& as_variable() const;

    bool is_temporary() const;
    ITemporary& as_temporary() const;

    bool is_define() const;
    IDefine& as_define() const;

    bool is_enum() const;
    IEnum& as_enum() const;

    bool is_array() const;
    IArray& as_array() const;
};

class IConstant
    : public ISymbol
    , public ITyped
    , public IValue
{};

class ITemporary
    : public ISymbol
    , public ITyped
{};

class IArray
    : public ISymbol
    , public ITyped
{};

class IVariable
    : public ISymbol
    , public ITyped
{};

class IEnum
    : public ISymbol
    , public ITyped
{};

class ILiteral
    : public ISymbol
    , public ITyped
    , public IValue
{};

class IDefine : public ISymbol {
public:
    // defines have no type, it has to be inferred.
    virtual const Expr_ptr body() const =0;
};

#endif

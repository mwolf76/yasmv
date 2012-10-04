/**
 *  @file expr.hh
 *  @brief Expression management
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
#ifndef EXPR_DATATYPES_H
#define EXPR_DATATYPES_H

#include <fqexpr.hh>

typedef vector<FQExpr> FQExprVector;

class ISymbol;
typedef ISymbol* ISymbol_ptr;
typedef unordered_map<FQExpr, ISymbol_ptr, fqexpr_hash, fqexpr_eq> Symbols;

class IConstant;
typedef IConstant* IConstant_ptr;
typedef unordered_map<FQExpr, IConstant_ptr, fqexpr_hash, fqexpr_eq> Constants;

class IVariable;
typedef IVariable* IVariable_ptr;
typedef unordered_map<FQExpr, IVariable_ptr, fqexpr_hash, fqexpr_eq> Variables;

class IDefine;
typedef IDefine* IDefine_ptr;
typedef unordered_map<FQExpr, IDefine_ptr, fqexpr_hash, fqexpr_eq> Defines;
typedef unordered_map<FQExpr, IDefine_ptr, fqexpr_hash, fqexpr_eq> Assigns;

class IModule;
typedef IModule* IModule_ptr;
typedef unordered_map<Expr_ptr, IModule_ptr, PtrHash, PtrEq> Modules;

#endif

/**
 * @file typedefs.hh
 * @brief Type system module header file, type definitions.
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

#ifndef TYPE_TYPEDEFS_H
#define TYPE_TYPEDEFS_H

#include <common/common.hh>
#include <expr/expr.hh>
#include <utils/pool.hh>

#include <vector>
#include <boost/unordered_map.hpp>

/* base classes pointer types */
typedef class Type* Type_ptr;
typedef class TypeMgr* TypeMgr_ptr;

/* aggregate types */
typedef std::vector<Type_ptr> TypeVector;
typedef boost::unordered_map<Expr_ptr, Type_ptr, PtrHash, PtrEq> TypeMap;

/* 1. scalars */
typedef class ScalarType* ScalarType_ptr;
typedef class StringType* StringType_ptr;

/* 1.1. monoliths */
typedef class MonolithicType* MonolithicType_ptr;
typedef class BooleanType* BooleanType_ptr;
typedef class EnumType* EnumType_ptr;

/* 1.2. algebraics */
typedef class ConstantType* ConstantType_ptr;
typedef class AlgebraicType* AlgebraicType_ptr;
typedef class SignedAlgebraicType* SignedAlgebraicType_ptr;
typedef class UnsignedAlgebraicType* UnsignedAlgebraicType_ptr;

/* 1.3. module instances */
typedef class InstanceType* InstanceType_ptr;

/* 2. arrays */
typedef class ArrayType* ArrayType_ptr;

#endif /* TYPE_TYPEDEFS_H */

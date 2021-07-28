/**
 * @file type/classes.cc
 * @brief Toplevel type class implementation, type classes.
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

#include <type/classes.hh>

namespace type {

Type::~Type()
{}

bool Type::is_scalar()
{ return NULL != dynamic_cast<ScalarType_ptr>( this ); }

ScalarType_ptr Type::as_scalar()
{ return dynamic_cast <const ScalarType_ptr> (this); }

bool Type::is_monolithic()
{ return NULL != dynamic_cast<MonolithicType_ptr>( this ); }

bool Type::is_boolean()
{ return NULL != dynamic_cast<BooleanType_ptr>( this ); }

BooleanType_ptr Type::as_boolean()
{ return dynamic_cast <const BooleanType_ptr> (this); }

bool Type::is_enum()
{ return NULL != dynamic_cast<EnumType_ptr>( this ); }

EnumType_ptr Type::as_enum()
{ return dynamic_cast<EnumType_ptr> (this); }

bool Type::is_instance()
{ return NULL != dynamic_cast<InstanceType_ptr> (this); }

InstanceType_ptr Type::as_instance()
{ return dynamic_cast<InstanceType_ptr> (this); }

bool Type::is_time()
{ return NULL != dynamic_cast<TimeType_ptr> (this); }

TimeType_ptr Type::as_time()
{ return dynamic_cast<TimeType_ptr> (this); }

bool Type::is_algebraic()
{ return NULL != dynamic_cast<AlgebraicType_ptr> (this); }

bool Type::is_constant()
{ return NULL != dynamic_cast<ConstantType_ptr> (this); }

AlgebraicType_ptr Type::as_algebraic()
{ return dynamic_cast <const AlgebraicType_ptr> (this); }

bool Type::is_signed_algebraic()
{ return NULL != dynamic_cast<SignedAlgebraicType_ptr> (this); }

SignedAlgebraicType_ptr Type::as_signed_algebraic()
{ return dynamic_cast <const SignedAlgebraicType_ptr> (this); }

bool Type::is_unsigned_algebraic()
{ return NULL != dynamic_cast<UnsignedAlgebraicType_ptr> (this); }

UnsignedAlgebraicType_ptr Type::as_unsigned_algebraic()
{ return dynamic_cast <const UnsignedAlgebraicType_ptr> (this); }

bool Type::is_array()
{ return NULL != dynamic_cast<ArrayType_ptr> (this); }

ArrayType_ptr Type::as_array()
{ return dynamic_cast<ArrayType_ptr> (this); }

bool Type::is_string()
{ return NULL != dynamic_cast<StringType_ptr> (this); }

StringType_ptr Type::as_string()
{ return dynamic_cast<const StringType_ptr> (this); }

};

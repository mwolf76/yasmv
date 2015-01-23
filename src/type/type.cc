/**
 *  @file type.cc
 *  @brief Type system classes
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
#include <type.hh>
#include <type_mgr.hh>

bool Type::is_scalar()
{ return NULL != dynamic_cast<ScalarType_ptr>( this ); }

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
{ return NULL != dynamic_cast<InstanceType_ptr>( this ); }

InstanceType_ptr Type::as_instance()
{ return dynamic_cast<InstanceType_ptr> (this); }

bool Type::is_algebraic()
{ return NULL != dynamic_cast<AlgebraicType_ptr>( this ); }

bool Type::is_constant()
{ return NULL != dynamic_cast<ConstantType_ptr> ( this ); }

AlgebraicType_ptr Type::as_algebraic()
{ return dynamic_cast <const AlgebraicType_ptr> (this); }

bool Type::is_signed_algebraic()
{ return NULL != dynamic_cast<SignedAlgebraicType_ptr>( this ); }

SignedAlgebraicType_ptr Type::as_signed_algebraic()
{ return dynamic_cast <const SignedAlgebraicType_ptr> (this); }

bool Type::is_unsigned_algebraic()
{ return NULL != dynamic_cast<UnsignedAlgebraicType_ptr>( this ); }

UnsignedAlgebraicType_ptr Type::as_unsigned_algebraic()
{ return dynamic_cast <const UnsignedAlgebraicType_ptr> (this); }

bool Type::is_array()
{ return NULL != dynamic_cast<ArrayType_ptr>( this ); }

ArrayType_ptr Type::as_array()
{ return dynamic_cast<ArrayType_ptr> (this); }

Type::~Type() {}

// ostream helper, uses FQExpr printer (see expr/expr.cc)
std::ostream& operator<<(std::ostream& os, Type_ptr type)
{ return os << type->repr(); }


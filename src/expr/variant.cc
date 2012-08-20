/**
 *  @file variant.cc
 *  @brief Variant type implementation
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

#include <variant.hh>

Variant NilValue;

bool Variant::is_nil() const
{ return f_type == BOTTOM; }

bool Variant::is_boolean() const
{ return f_type == BOOLEAN; }
bool Variant::as_boolean() const
{ return f_bool; }

bool Variant::is_integer() const
{ return f_type == INTEGER; }
int Variant::as_integer() const
{ return f_int; }

bool Variant::is_string() const
{ return f_type == STRING; }
string Variant::as_string() const
{ return f_str; }

ostream& operator<<(ostream& os, const Variant& variant)
{
  if (variant.is_boolean()) {
    return os << variant.as_boolean();
  }
  else assert(0);
}

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

// variant constructors
Variant::Variant()
    : f_type(BOTTOM)
{
    // DRIVEL << "Initialized BOTTOM Variant @" << this << endl;
}

Variant::Variant(bool value)
    : f_type(BOOLEAN)
    , f_bool(value)
{
    // DRIVEL << "Initialized BOOLEAN Variant @" << this << " (value = " << f_bool << ")" << endl;
}

Variant::Variant(int value)
    : f_type(INTEGER)
    , f_int(value)
{
    // DRIVEL << "Initialized INTEGER Variant @" << this << " (value = " << f_int << ")" << endl;
}

Variant::Variant(const std::string &value)
    : f_type(STRING)
    , f_str(value)
{
    // DRIVEL << "Initialized STRING Variant @" << this << " (value = " << f_str << ")" << endl;
}

Variant::Variant(const char *value)
    : f_type(STRING)
    , f_str(value)
{
    // DRIVEL << "Initialized STRING Variant @" << this << " (value = " << f_str << ")" << endl;
}

Variant::Variant(const Variant& v)
    : f_type(v.f_type)
{
    switch (f_type) {
    case BOTTOM: return;
    case BOOLEAN: f_bool = v.f_bool; return;
    case INTEGER: f_int = v.f_int; return;
    case STRING: f_str = v.f_str; return;
    default: assert(0);
    }

    void *tmp = (void *) &v;
    DRIVEL
        << "Initialized COPY Variant @" << this
        << " (from @" << tmp << ")"
        << std::endl;
}

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
std::string Variant::as_string() const
{ return f_str; }

std::ostream& operator<<(std::ostream& os, const Variant& variant)
{
    if (variant.is_nil()) {
        return os << "(null)";
    }
    else if (variant.is_boolean()) {
        return os << variant.as_boolean();
    }
    else if (variant.is_integer()) {
        return os << variant.as_integer();
    }
    else if (variant.is_string()) {
        return os << variant.as_string();
    }
    else assert(0);
}

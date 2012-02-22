/*
Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 2.1 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA

 */

/**
 * @file variant.hh
 *
 * @brief Variants management
 *
 */

#ifndef VARIANT_H
#define VARIANT_H
#include <common.hh>

typedef enum {
  BOOLEAN,
  INTEGER,
  STRING,
} VariantType;

// Variant iface
class IVariant {
public:
  virtual bool is_boolean() =0;
  virtual bool as_boolean() =0;

  virtual bool is_integer() =0;
  virtual int as_integer() =0;

  virtual bool is_string() =0;
  virtual string as_string() =0;
};


// Variant implementation
class Variant : public IVariant {
public:
  // variant constructors
  Variant(bool value)
    : f_type(BOOLEAN)
    , f_bool(value)
  {}

  Variant(int value)
    : f_type(INTEGER)
    , f_int(value)
  {}

  Variant(string value)
    : f_type(STRING)
    , f_str(value)
  {}

  bool is_boolean();
  bool as_boolean();

  bool is_integer();
  int as_integer();

  bool is_string();
  string as_string();

private:
  bool f_bool;
  int f_int;
  string f_str;
};

#endif

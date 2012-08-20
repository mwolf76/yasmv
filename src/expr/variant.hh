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
  BOTTOM,
  BOOLEAN,
  INTEGER,
  STRING,
} VariantType;

// Variant iface
class IVariant : public IObject {
public:
  virtual bool is_nil() const =0;

  virtual bool is_boolean() const =0;
  virtual bool as_boolean() const =0;

  virtual bool is_integer() const =0;
  virtual int as_integer() const =0;

  virtual bool is_string() const =0;
  virtual string as_string() const =0;
};


// Variant implementation
class Variant : public IVariant {
  friend ostream& operator<<(ostream& os, const Variant& variant);

public:
  // variant constructors
  Variant()
    : f_type(BOTTOM)
  {}

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

  bool is_nil() const;

  bool is_boolean() const;
  bool as_boolean() const;

  bool is_integer() const;
  int as_integer() const;

  bool is_string() const;
  string as_string() const;

private:
  VariantType f_type;

  bool f_bool;
  int f_int;
  string f_str;
};

extern Variant NilValue;

#endif

/**
 * @file variant.hh
 * @brief Variant type implementation
 *
 * This header file contains definitions and services that implement a
 * variant type, used mainly as a return type for commands.
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

#ifndef VARIANT_H
#define VARIANT_H

#include <common/common.hh>
#include <ctime>

typedef enum {
    BOTTOM,
    BOOLEAN,
    INTEGER,
    STRING,
} VariantType;

class Variant {
    friend std::ostream& operator<<(std::ostream& os, const Variant& variant);

public:
    // variant ctors
    Variant();

    Variant(const std::string &value);
    Variant(const char *value);

    Variant(bool value);
    Variant(int value);

    Variant(const Variant& v);

    // variant predicates & getters
    bool is_nil() const;

    bool is_boolean() const;
    bool as_boolean() const;

    bool is_integer() const;
    int as_integer() const;

    bool is_clock() const;
    clock_t as_clock() const;

    bool is_string() const;
    std::string as_string() const;

private:
    VariantType f_type;

    bool f_bool;
    int f_int;
    std::string f_str;
    clock_t f_clock;
};

extern Variant NilValue;

#endif /* VARIANT_H */

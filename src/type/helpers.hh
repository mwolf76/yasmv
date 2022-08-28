/**
 * @file type.hh
 * @brief Type system module header file, helpers.
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

#ifndef TYPE_HELPERS_H
#define TYPE_HELPERS_H

/** -- shortcurts to simplify the manipulation of the internal type stack -- */
#define TOP_TYPE(tp)                            \
    const auto tp { f_type_stack.back() }

#define DROP_TYPE()                             \
    f_type_stack.pop_back()

#define POP_TYPE(tp)                            \
    TOP_TYPE(tp); DROP_TYPE()

#define PUSH_TYPE(tp)                           \
    f_type_stack.push_back(tp)

namespace type {

typedef std::vector<Type_ptr> TypeVector;

};

#endif /* TYPE_HELPERS_H */

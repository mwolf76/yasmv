/**
 * @file utils/ctx.hh
 * @brief System-wide definitions.
 *
 * This header file contains common definitions used throughout the
 * whole program.
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

#ifndef UTILS_CTX_H
#define UTILS_CTX_H

#include <vector>

/* -- shortcurts to simplify the manipulation of the internal ctx stack -- */
#define TOP_CTX(ctx)                \
    assert(0 < f_ctx_stack.size()); \
    const expr::Expr_ptr ctx        \
    {                               \
        f_ctx_stack.back()          \
    }

#define DROP_CTX() \
    f_ctx_stack.pop_back()

#define POP_CTX(ctx) \
    TOP_CTX(ctx);    \
    DROP_CTX()

#define PUSH_CTX(ctx) \
    f_ctx_stack.push_back(ctx)

namespace utils {

};

#endif /* UTILS_CTX_H */

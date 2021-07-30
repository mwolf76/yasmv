/**
 * @file expr/walker/helpers.hh
 * @brief Expression walker pattern implementation, implementation helpers.
 *
 * This header file contains the declarations required by the Expression
 * Walker class.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/

#ifndef EXPR_WALKER_HELPERS_H
#define EXPR_WALKER_HELPERS_H

namespace expr {

/* helper macros to declare walker hooks */
#define UNARY_HOOK(op)                                             \
    bool walk_## op ## _preorder(const expr::Expr_ptr expr);       \
    void walk_## op ## _postorder(const expr::Expr_ptr expr)

#define BINARY_HOOK(op)                                            \
    bool walk_## op ## _preorder(const expr::Expr_ptr expr);       \
    bool walk_## op ## _inorder(const expr::Expr_ptr expr);        \
    void walk_## op ## _postorder(const expr::Expr_ptr expr)

#define OP_HOOKS                                   \
    BINARY_HOOK(at); BINARY_HOOK(interval);        \
    UNARY_HOOK(next);                              \
    UNARY_HOOK(neg); UNARY_HOOK(not);              \
    UNARY_HOOK(bw_not);                            \
                                                   \
    BINARY_HOOK(add); BINARY_HOOK(sub);            \
    BINARY_HOOK(div); BINARY_HOOK(mod);            \
    BINARY_HOOK(mul);                              \
                                                   \
    BINARY_HOOK(and); BINARY_HOOK(or);             \
    BINARY_HOOK(bw_and); BINARY_HOOK(bw_or);       \
    BINARY_HOOK(bw_xor); BINARY_HOOK(implies);     \
    BINARY_HOOK(guard);                            \
    BINARY_HOOK(bw_xnor); BINARY_HOOK(lshift);     \
    BINARY_HOOK(rshift);                           \
                                                   \
    BINARY_HOOK(type); BINARY_HOOK(cast);          \
                                                   \
    BINARY_HOOK(assignment);                       \
                                                   \
    BINARY_HOOK(eq); BINARY_HOOK(ne);              \
    BINARY_HOOK(le); BINARY_HOOK(lt);              \
    BINARY_HOOK(ge); BINARY_HOOK(gt);              \
    BINARY_HOOK(ite); BINARY_HOOK(cond);           \
                                                   \
    BINARY_HOOK(dot);                              \
    BINARY_HOOK(params);                           \
    BINARY_HOOK(params_comma);                     \
    BINARY_HOOK(subscript);                        \
    UNARY_HOOK(set);                               \
    BINARY_HOOK(set_comma);                        \
    UNARY_HOOK(array);                             \
    BINARY_HOOK(array_comma)

#define LTL_HOOKS                                       \
    UNARY_HOOK(F); UNARY_HOOK(G); UNARY_HOOK(X);        \
    BINARY_HOOK(R); BINARY_HOOK(U)

#define UNARY_STUB(op)                                             \
    bool walk_## op ## _preorder(const expr::Expr_ptr expr)        \
    { assert(false); return false; }                               \
    void walk_## op ## _postorder(const expr::Expr_ptr expr) {}

#define BINARY_STUB(op)                                            \
    bool walk_## op ## _preorder(const expr::Expr_ptr expr)        \
    { assert(false); return false; }                               \
    bool walk_## op ## _inorder(const expr::Expr_ptr expr)         \
    { assert(false); return false; }                               \
    void walk_## op ## _postorder(const expr::Expr_ptr expr) {}

#define LTL_STUBS                                       \
    UNARY_STUB(F); UNARY_STUB(G); UNARY_STUB(X);        \
    BINARY_STUB(R); BINARY_STUB(U)

};

#endif /* EXPR_WALKER_HELPERS_H */

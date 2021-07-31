/**
 * @file resolver.hh
 * @brief Expr time resolver
 *
 * This header file contains the declarations required by the
 * Expression resolver class.
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

#ifndef EXPR_TIME_RESOLVER_H
#define EXPR_TIME_RESOLVER_H

#include <string>
#include <expr/expr_mgr.hh>
#include <expr/walker/walker.hh>

#include <boost/unordered_map.hpp>

namespace expr::time {

class DoesNotApply : public ExprException {
public:
    DoesNotApply(Expr_ptr expr, step_t time);
};

/* TODO: rename this to Expander. This class rewrites @a..b{phi} into
 * @a{phi} ^ @a+1{phi} ^ ... ^ @b{phi} */

class Resolver : public ExprWalker {
public:
    Resolver(ExprMgr& em);
    ~Resolver();

    inline ExprMgr& em()
    { return f_em; }

    Expr_ptr process(Expr_ptr expr);

protected:
    void pre_hook();
    void post_hook();

    // support for LTL ops
    LTL_HOOKS;

    // support for basic ops
    OP_HOOKS;

    void walk_instant(const Expr_ptr expr);
    void walk_leaf(const Expr_ptr expr);

private:
    ExprMgr& f_em;

    ExprVector f_expr_stack;
    bool internal_error(const Expr_ptr expr);
};

} // namespace expr::time

#endif /* EXPR_TIME_RESOLVER_H */

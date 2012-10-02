/**
 *  @file full_expr_walker.hh
 *  @brief Expression algorithm-unaware walk pattern implementation (FULL variant)
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

#ifndef FULL_EXPR_WALKER_H
#define FULL_EXPR_WALKER_H

#include <common.hh>
#include <expr.hh>
#include <temporal_expr_walker.hh>

class FullWalker : public TemporalWalker {
protected:

    // extra-hooks
    virtual void pre_hook()
    {}
    virtual void post_hook()
    {}

    void walk();

public:
    FullWalker();
    virtual ~FullWalker();

    virtual bool walk_set_preorder(const Expr_ptr expr) =0;
    virtual void walk_set_postorder(const Expr_ptr expr) =0;

    virtual bool walk_params_preorder(const Expr_ptr expr) =0;
    virtual void walk_params_postorder(const Expr_ptr expr) =0;

    virtual bool walk_comma_preorder(const Expr_ptr expr) =0;
    virtual bool walk_comma_inorder(const Expr_ptr expr) =0;
    virtual void walk_comma_postorder(const Expr_ptr expr) =0;

    virtual bool walk_range_preorder(const Expr_ptr expr) =0;
    virtual bool walk_range_inorder(const Expr_ptr expr) =0;
    virtual void walk_range_postorder(const Expr_ptr expr) =0;
};

#endif

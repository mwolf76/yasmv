/**
 *  @file temporal_expr_walker.hh
 *  @brief Expression algorithm-unaware walk pattern implementation
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

#ifndef TEMP_EXPR_WALKER_H
#define TEMP_EXPR_WALKER_H

#include <common.hh>
#include <expr.hh>

typedef enum {
    F_1, G_1, X_1, U_1, U_2, R_1, R_2,
    AF_1, AG_1, AX_1, AU_1, AU_2, AR_1, AR_2,
    EF_1, EG_1, EX_1, EU_1, EU_2, ER_1, ER_2,
} expr_walker_entry_point;

struct activation_record {
    expr_walker_entry_point pc;
    Expr_ptr expr;

    activation_record(const Expr_ptr e)
    : pc(DEFAULT) , expr(e)
    {}

};

typedef stack<struct activation_record> walker_stack;

class TemporalWalker : public class SimpleWalker {
protected:
    virtual void walk();

public:
    TemporalWalker();
    virtual ~TemporalWalker();

    Walker& operator() (const Expr_ptr expr);

    // -- walker interface: for unary operator we define a pre- and a
    // -- post-order hook. The pre-hook returns a boolean that
    // -- determines if the subtree is to be visited. For each binary
    // -- operator we define a pre-, an in- and a post-order hook. Here,
    // -- both pre- and in- hooks return a boolean with the same
    // -- semantics as above. This can be used e.g. for lazy evaluation.

    // LTL ops
    virtual bool walk_F_preorder(const Expr_ptr expr) =0;
    virtual void walk_F_postorder(const Expr_ptr expr) =0;
    virtual bool walk_G_preorder(const Expr_ptr expr) =0;
    virtual void walk_G_postorder(const Expr_ptr expr) =0;
    virtual bool walk_X_preorder(const Expr_ptr expr) =0;
    virtual void walk_X_postorder(const Expr_ptr expr) =0;
    virtual bool walk_U_preorder(const Expr_ptr expr) =0;
    virtual bool walk_U_inorder(const Expr_ptr expr) =0;
    virtual void walk_U_postorder(const Expr_ptr expr) =0;
    virtual bool walk_R_preorder(const Expr_ptr expr) =0;
    virtual bool walk_R_inorder(const Expr_ptr expr) =0;
    virtual void walk_R_postorder(const Expr_ptr expr) =0;

    // CTL A ops
    virtual bool walk_AF_preorder(const Expr_ptr expr) =0;
    virtual void walk_AF_postorder(const Expr_ptr expr) =0;
    virtual bool walk_AG_preorder(const Expr_ptr expr) =0;
    virtual void walk_AG_postorder(const Expr_ptr expr) =0;

    virtual bool walk_AX_preorder(const Expr_ptr expr) =0;
    virtual void walk_AX_postorder(const Expr_ptr expr) =0;

    virtual bool walk_AU_preorder(const Expr_ptr expr) =0;
    virtual bool walk_AU_inorder(const Expr_ptr expr) =0;
    virtual void walk_AU_postorder(const Expr_ptr expr) =0;

    virtual bool walk_AR_preorder(const Expr_ptr expr) =0;
    virtual bool walk_AR_inorder(const Expr_ptr expr) =0;
    virtual void walk_AR_postorder(const Expr_ptr expr) =0;

    // CTL E ops
    virtual bool walk_EF_preorder(const Expr_ptr expr) =0;
    virtual void walk_EF_postorder(const Expr_ptr expr) =0;

    virtual bool walk_EG_preorder(const Expr_ptr expr) =0;
    virtual void walk_EG_postorder(const Expr_ptr expr) =0;

    virtual bool walk_EX_preorder(const Expr_ptr expr) =0;
    virtual void walk_EX_postorder(const Expr_ptr expr) =0;

    virtual bool walk_EU_preorder(const Expr_ptr expr) =0;
    virtual bool walk_EU_inorder(const Expr_ptr expr) =0;
    virtual void walk_EU_postorder(const Expr_ptr expr) =0;

    virtual bool walk_ER_preorder(const Expr_ptr expr) =0;
    virtual bool walk_ER_inorder(const Expr_ptr expr) =0;
    virtual void walk_ER_postorder(const Expr_ptr expr) =0;
};

#endif

/**
 *  @file ltl_expr_walker.hh
 *  @brief Expression algorithm-unaware walk pattern implementation (LTL variant)
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

#ifndef LTL_EXPR_WALKER_H
#define LTL_EXPR_WALKER_H

#include <temporal_expr_walker.hh>

// just a temporal walker with the CTL part
// filtered out
class LTLWalker : public TemporalWalker {
protected:

    // extra-hooks
    virtual void pre_hook()
    {}
    virtual void post_hook()
    {}

    void walk();

public:
    LTLWalker();
    virtual ~LTLWalker();

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
    virtual bool walk_AF_preorder(const Expr_ptr expr)
    { assert (false); return false; }
    virtual void walk_AF_postorder(const Expr_ptr expr)
    { assert (false); }
    virtual bool walk_AG_preorder(const Expr_ptr expr)
    { assert (false); return false; }
    virtual void walk_AG_postorder(const Expr_ptr expr)
    { assert (false); }

    virtual bool walk_AX_preorder(const Expr_ptr expr)
    { assert (false); return false; }
    virtual void walk_AX_postorder(const Expr_ptr expr)
    { assert (false); }

    virtual bool walk_AU_preorder(const Expr_ptr expr)
    { assert(false); return false; }
    virtual bool walk_AU_inorder(const Expr_ptr expr)
    { assert(false); return false; }
    virtual void walk_AU_postorder(const Expr_ptr expr)
    { assert(false); }

    virtual bool walk_AR_preorder(const Expr_ptr expr)
    { assert(false); return false; }
    virtual bool walk_AR_inorder(const Expr_ptr expr)
    { assert(false); return false; }
    virtual void walk_AR_postorder(const Expr_ptr expr)
    { assert(false); }

    // CTL E ops
    virtual bool walk_EF_preorder(const Expr_ptr expr)
    { assert(false); return false; }
    virtual void walk_EF_postorder(const Expr_ptr expr)
    { assert(false); }

    virtual bool walk_EG_preorder(const Expr_ptr expr)
    { assert(false); return false; }
    virtual void walk_EG_postorder(const Expr_ptr expr)
    { assert(false); }

    virtual bool walk_EX_preorder(const Expr_ptr expr)
    { assert(false); return false; }
    virtual void walk_EX_postorder(const Expr_ptr expr)
    { assert(false); }

    virtual bool walk_EU_preorder(const Expr_ptr expr)
    { assert(false); return false; }
    virtual bool walk_EU_inorder(const Expr_ptr expr)
    { assert(false); return false; }
    virtual void walk_EU_postorder(const Expr_ptr expr)
    { assert(false); }

    virtual bool walk_ER_preorder(const Expr_ptr expr)
    { assert(false); return false; }
    virtual bool walk_ER_inorder(const Expr_ptr expr)
    { assert(false); return false; }
    virtual void walk_ER_postorder(const Expr_ptr expr)
    { assert(false); }

};

#endif

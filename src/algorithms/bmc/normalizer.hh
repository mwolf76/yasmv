/**
 *  @file normalizer.hh
 *  @brief Formula normalizer header file
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

#ifndef NORMALIZER_H
#define NORMALIZER_H

#include <expr_mgr.hh>

#include <type.hh>
#include <type_mgr.hh>

#include <expr_walker.hh>

// NOTE: here we're using a vector in order to bypass STL stack
// interface limitations. (i.e. absence of clear())
typedef vector<Expr_ptr> ExprStack;

class ModelMgr;
class Normalizer : public ExprWalker {
public:
    Normalizer(ModelMgr& owner);
    ~Normalizer();

    // walker toplevel
    Expr_ptr process(Expr_ptr expr);

    inline bool is_invariant() const
    { return f_invariant; }

    inline Expr_ptr property() const
    {
        assert( 1 == f_result_stack.size());
        return f_result_stack.back();
    }

protected:
    void pre_hook();
    void post_hook();

    void pre_node_hook(Expr_ptr expr);
    void post_node_hook(Expr_ptr expr);

    // Full lang support
    LTL_HOOKS; OP_HOOKS;
    void walk_leaf(const Expr_ptr expr);

    bool f_polarity;
    bool f_invariant;

    ExprStack f_result_stack;

    // managers
    ModelMgr& f_owner;
    ExprMgr& f_em;
};

#endif

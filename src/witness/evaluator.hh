/**
 *  @file evaluator.hh
 *  @brief Const expr evaluator
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

#ifndef EVALUATOR_H
#define EVALUATOR_H

#include <expr_walker.hh>
#include <expr/pool.hh>

#include <witness.hh>

/* local typedefs */
typedef unordered_map<FQExpr, value_t, FQExprHash, FQExprEq> FQExprValueMap;
typedef pair<FQExprValueMap::iterator, bool> FQExprValueMapHit;

typedef vector<Expr_ptr> ExprStack;
typedef vector<step_t>   TimeStack;
typedef vector<value_t>  ValuesStack;

/* shortcuts to to simplify manipulation of the internal values stack */
#define POP_VALUE(op)                              \
    assert(0 < f_values_stack.size());             \
    const value_t op = f_values_stack.back();      \
    f_values_stack.pop_back()

#define PUSH_VALUE(op)                             \
    f_values_stack.push_back(op)

class WitnessMgr;// fwd decl
class Evaluator : public ExprWalker {

    // ExprStack f_expr_stack;
    ExprStack f_ctx_stack;
    TimeStack f_time_stack;
    ValuesStack f_values_stack;

    // environment for evaluation
    Witness_ptr f_witness;

    // cache
    FQExprValueMap f_map;

public:
    Evaluator(WitnessMgr& owner); // defaults to std::cout
    virtual ~Evaluator();

    value_t process(Witness& witness, Expr_ptr ctx, Expr_ptr body, step_t time);

protected:
    OP_HOOKS;
    void walk_leaf(const Expr_ptr expr);

private:

    // the owner
    WitnessMgr &f_owner;

    // services
    inline bool cache_miss(const Expr_ptr expr)
    {
        assert( 0 < f_ctx_stack.size());
        Expr_ptr ctx = f_ctx_stack.back();

        assert( 0 < f_time_stack.size());
        step_t step = f_time_stack.back();

        FQExpr key(ctx , expr, step);
        FQExprValueMap::iterator eye = f_map.find(key);

        if (eye != f_map.end()) {
            value_t res = (*eye).second;
            PUSH_VALUE(res);
            return false;
        }

        return true;
    }
};

#endif
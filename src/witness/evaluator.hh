/**
 * @file evaluator.hh
 * @brief Const expr evaluator
 *
 * This header file contains the declarations required to implement
 * the evaluation of defines.
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

#ifndef EVALUATOR_H
#define EVALUATOR_H

#include <expr/timed_expr.hh>
#include <expr/walker/walker.hh>

#include <witness/witness.hh>

#include <utils/time.hh>
#include <utils/values.hh>

#include <boost/unordered_map.hpp>
typedef boost::unordered_map<TimedExpr, value_t,
                             TimedExprHash, TimedExprEq> TimedExprValueMap;

class WitnessMgr;
class Evaluator : public ExprWalker {

    TypeVector f_type_stack;
    ExprVector f_ctx_stack;
    TimeVector f_time_stack;
    ValueVector f_values_stack;

    // environment for evaluation
    Witness_ptr f_witness;

    TimedExprValueMap f_te2v_map;

public:
    Evaluator(WitnessMgr& owner);
    virtual ~Evaluator();

    Expr_ptr process(Witness& witness, Expr_ptr ctx, Expr_ptr body, step_t time);

protected:
    inline WitnessMgr& owner() const
    { return f_owner; }

    OP_HOOKS;
    LTL_STUBS;
    void walk_leaf(const Expr_ptr expr);

private:
    WitnessMgr &f_owner;

    bool cache_miss(const Expr_ptr expr);
    void clear_internals();

    void push_value(const Expr_ptr expr);
};

#endif /* EVALUATOR_H */

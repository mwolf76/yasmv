/**
 *  @file witness.hh
 *  @brief Witness module
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

#ifndef WITNESS_H
#define WITNESS_H

#include <common.hh>

#include <expr.hh>
#include <expr_mgr.hh>

#include <type.hh>
#include <type_mgr.hh>

#include <model.hh>
#include <model_mgr.hh>

#include <variant.hh>
#include <sat.hh>

typedef unordered_map<FQExpr, Expr_ptr, FQExprHash, FQExprEq> FQExpr2ExprMap;

class Witness; // fwd decl

typedef class TimeFrame* TimeFrame_ptr;
class TimeFrame : public IObject {

public:
    TimeFrame(Witness& owner);
    ~TimeFrame();

    /* Retrieves value for expr, throws an exception if no value exists. */
    Expr_ptr value( FQExpr expr );

    /* Returns true iff expr has an assigned value within this time frame. */
    bool has_value( FQExpr expr );

    /* Sets value for expr */
    void set_value( FQExpr expr, Expr_ptr value );

private:
    FQExpr2ExprMap f_map;

    // forbid copy
    TimeFrame(const TimeFrame &other)
        : f_owner( other.f_owner)
    { assert (false); }

    Witness& f_owner;
};

typedef vector<TimeFrame_ptr> TimeFrames;
typedef vector<FQExpr> FQExprs;

typedef class Witness* Witness_ptr;
class Witness : public IObject {
public:
    Witness(string id = "<Noname>", step_t j = 0, step_t k = 0);

    /* data storage */
    inline TimeFrames& frames()
    { return f_frames; }

    inline TimeFrame& operator[](step_t i)
    { return * f_frames [i]; }

    inline const string& id() const
    { return f_id; }

    inline void set_id(string id)
    { f_id = id; }

    inline unsigned length()
    { return f_frames.size(); }

    inline FQExprs& lang()
    { return f_lang; }

    inline step_t j() const
    { return f_j; }

    inline step_t k() const
    { return f_k; }

    // extend trace by k appending the given one, yields last timeframe
    TimeFrame& extend(Witness& w);

    // extend trace by k steps, yields last one (default is 1 step)
    TimeFrame& extend(step_t k = 1);

    /* Retrieves value for expr, throws an exception if no value exists. */
    Expr_ptr value( FQExpr expr );

    /* Returns true iff expr has an assigned value within this time frame. */
    bool has_value( FQExpr expr );

protected:
    /* this witness' id */
    string f_id;

    /* distance (i.e. number of transitions) from time 0 of the first frame */
    step_t f_j;

    /* distance (i.e. number of transitions) from time 0 of the last frame */
    step_t f_k;

    /* Timeframes (list) */
    TimeFrames f_frames;

    /* Language (i.e. full list of symbols) */
    FQExprs f_lang;
};

class WitnessPrinter : public IObject {
public:
    virtual void operator() (const Witness& w, step_t j = 0, step_t k = -1) =0;
};

#endif

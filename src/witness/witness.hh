/**
 * @file witness.hh
 * @brief Witness module header file
 *
 * This module contains definitions and services that implement the
 * abstract interface for the witness subsystem.
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

#ifndef WITNESS_H
#define WITNESS_H

#include <common/common.hh>

#include <vector>

#include <boost/unordered_map.hpp>

#include <expr/expr.hh>
#include <expr/expr_mgr.hh>

#include <type/type.hh>
#include <type/type_mgr.hh>

#include <model/model.hh>
#include <model/model_mgr.hh>

#include <sat/sat.hh>

#include <symb/typedefs.hh>
#include <symb/classes.hh>
#include <symb/symb_iter.hh>

#include <utils/variant.hh>

#include <witness/exceptions.hh>

namespace witness {

typedef boost::unordered_map<expr::Expr_ptr, expr::Expr_ptr, utils::PtrHash, utils::PtrEq> Expr2ExprMap;
typedef Expr2ExprMap::iterator Expr2ExprMapIterator;

typedef boost::unordered_map<expr::Expr_ptr, value_format_t, utils::PtrHash, utils::PtrEq> Expr2FormatMap;
typedef Expr2FormatMap::iterator Expr2FormatMapIterator;

class Witness; // fwd decl

typedef class TimeFrame* TimeFrame_ptr;
class TimeFrame {

public:
    TimeFrame(Witness& owner);
    ~TimeFrame();

    /* Retrieves value for expr, throws an exception if no value exists. */
    expr::Expr_ptr value( expr::Expr_ptr expr );

    /* Returns true iff expr has an assigned value within this time frame. */
    bool has_value( expr::Expr_ptr expr );

    /* Sets value (and optionally also format) for expr */
    void set_value( expr::Expr_ptr expr, expr::Expr_ptr value,
                    value_format_t format = FORMAT_DECIMAL);

    /* Retrieves format for expr, throws an exception if no value exists. */
    // value_format_t format( expr::Expr_ptr expr );

    /* Full list of assignments for this Time Frame */
    expr::ExprVector assignments();

private:
    Expr2ExprMap f_map;
    Expr2FormatMap f_format_map;

    // forbid copy
    TimeFrame(const TimeFrame &other)
        : f_owner( other.f_owner)
    { assert (false); }

    Witness& f_owner;
};

typedef std::vector<TimeFrame_ptr> TimeFrames;

typedef class Witness* Witness_ptr;
class Witness {
public:
    Witness(sat::Engine_ptr pengine = NULL,
            expr::Atom id = "<Noname>",
            expr::Atom desc = "<No description>",
            step_t j = 0);

    /* data storage */
    inline TimeFrames& frames()
    { return f_frames; }

    TimeFrame& operator[](step_t i);

    inline const expr::Atom& id() const
    { return f_id; }

    inline void set_id(expr::Atom id)
    { f_id = id; }

    inline const expr::Atom& desc() const
    { return f_desc; }

    inline void set_desc(expr::Atom desc)
    { f_desc = desc; }

    inline step_t first_time()
    { return f_j; }

    inline TimeFrame& first()
    { return operator[](first_time()); }

    inline step_t last_time()
    { return f_j + f_frames.size() -1; }

    inline TimeFrame& last()
    { return operator[](last_time()); }

    inline step_t size()
    { return f_frames.size(); }

    inline expr::ExprVector& lang()
    { return f_lang; }

    /* Extends trace by k appending the given one, yields last timeframe */
    TimeFrame& extend(Witness& w);

    /* Extends trace by 1 steps, yields new step */
    TimeFrame& extend();

    /* Retrieves value for expr, throws an exception if no value exists. */
    expr::Expr_ptr value( expr::Expr_ptr expr, step_t time);

    /* Returns true iff expr has an assigned value within this time frame. */
    bool has_value( expr::Expr_ptr expr, step_t time);

protected:
    /* this witness' id */
    expr::Atom f_id;

    /* this witness' description */
    expr::Atom f_desc;

    /* distance (i.e. number of transitions) from time 0 of the first frame */
    step_t f_j;

    /* Timeframes (list) */
    TimeFrames f_frames;

    /* Language (i.e. full list of symbols) */
    expr::ExprVector f_lang;

    /* An engine that can be used to extend this witness. This is not
       necessarily the engine that created the trace. Ordinarily it
       should be a simulation engine. */
    sat::Engine_ptr p_engine;

    inline bool has_engine() const
    { return NULL != p_engine; }

    inline sat::Engine& engine()
    {
        assert (NULL != p_engine);
        return * p_engine;
    }

    void register_engine(sat::Engine& e);
};

class WitnessPrinter {
public:
    virtual void operator() (const Witness& w, step_t j = 0, step_t k = -1) =0;
};

};

#endif /* WITNESS_H */

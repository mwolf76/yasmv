/**
 *  @file witness.hh
 *  @brief Witness module
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

/** Exception classes */
class WitnessException : public Exception {
public:
    virtual const char* what() const throw() =0;
};

/** Raised when a given ID is registered more than once */
class DuplicateWitnessId : public WitnessException {
public:
    DuplicateWitnessId(Atom id)
        : f_id(id)
    {}

    ~DuplicateWitnessId() throw()
    {}

    const char* what() const throw();

private:
    Atom f_id;
};

/** Raised when a given ID is searched for and was not registered */
class UnknownWitnessId : public WitnessException {
public:
    UnknownWitnessId(Atom id)
        : f_id(id)
    {}

    ~UnknownWitnessId() throw()
    {}

    const char* what() const throw();

private:
    Atom f_id;
};

/** Raised when TimeFrame for requested time does not exist. */
class IllegalTime : public WitnessException {
public:
    IllegalTime(step_t time)
        : f_time(time)
    {}

    ~IllegalTime() throw()
    {}

    const char* what() const throw();

private:
    step_t f_time;
};

class NoValue : public WitnessException {
public:
    NoValue(Expr_ptr id)
        : f_id(id)
    {}

    ~NoValue() throw()
    {}

    const char* what() const throw();

private:
    Expr_ptr f_id;
};

typedef unordered_map<Expr_ptr, Expr_ptr, PtrHash, PtrEq> Expr2ExprMap;

class Witness; // fwd decl

typedef class TimeFrame* TimeFrame_ptr;
class TimeFrame {

public:
    TimeFrame(Witness& owner);
    ~TimeFrame();

    /* Retrieves value for expr, throws an exception if no value exists. */
    Expr_ptr value( Expr_ptr expr );

    /* Returns true iff expr has an assigned value within this time frame. */
    bool has_value( Expr_ptr expr );

    /* Sets value for expr */
    void set_value( Expr_ptr expr, Expr_ptr value );

private:
    Expr2ExprMap f_map;

    // forbid copy
    TimeFrame(const TimeFrame &other)
        : f_owner( other.f_owner)
    { assert (false); }

    Witness& f_owner;
};

typedef vector<TimeFrame_ptr> TimeFrames;
typedef vector<Expr_ptr> Exprs;

typedef class Witness* Witness_ptr;
class Witness {
public:
    Witness(Atom id = "<Noname>", Atom desc = "<No description>", step_t j = 0);

    /* data storage */
    inline TimeFrames& frames()
    { return f_frames; }

    inline TimeFrame& operator[](step_t i)
    {
        if (i < f_j) {
            throw IllegalTime(i);
        }
        i -= f_j;
        assert(0 <= i);

        if (f_frames.size() -1 < i) {
            throw IllegalTime(f_j + i);
        }
        return * f_frames [i];
    }

    inline const Atom& id() const
    { return f_id; }

    inline void set_id(Atom id)
    { f_id = id; }

    inline const Atom& desc() const
    { return f_desc; }

    inline void set_desc(Atom desc)
    { f_desc = desc; }

    inline step_t first_time()
    { return f_j; }

    inline step_t last_time()
    { return f_j + f_frames.size() -1; }

    inline step_t length()
    { return f_frames.size(); }

    inline Exprs& lang()
    { return f_lang; }

    /* Extends trace by k appending the given one, yields last timeframe */
    TimeFrame& extend(Witness& w);

    /* Extends trace by 1 steps, yields new step */
    TimeFrame& extend();

    /* Retrieves value for expr, throws an exception if no value exists. */
    Expr_ptr value( Expr_ptr expr, step_t time);

    /* Returns true iff expr has an assigned value within this time frame. */
    bool has_value( Expr_ptr expr, step_t time);

protected:
    /* this witness' id */
    Atom f_id;

    /* this witness' description */
    Atom f_desc;

    /* distance (i.e. number of transitions) from time 0 of the first frame */
    step_t f_j;

    /* Timeframes (list) */
    TimeFrames f_frames;

    /* Language (i.e. full list of symbols) */
    Exprs f_lang;
};

class WitnessPrinter {
public:
    virtual void operator() (const Witness& w, step_t j = 0, step_t k = -1) =0;
};

#endif

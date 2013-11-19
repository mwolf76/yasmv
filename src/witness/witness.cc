/**
 *  @file witness.cc
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
#include <witness.hh>

TimeFrame::TimeFrame(Witness& owner)
    : f_owner(owner)
{}

TimeFrame::~TimeFrame()
{}

/* Retrieves value for expr, throws an exception if no value exists. */
Expr_ptr TimeFrame::value( FQExpr expr )
{
    // symbol is defined in witness' language
    FQExprs& lang = f_owner.lang();
    assert( find( lang.begin(), lang.end(), expr) != lang.end());

    FQExpr2ExprMap::iterator eye;

    eye = f_map.find( expr );
    assert (f_map.end() != eye); // TODO

    return (*eye).second;
}

/* Returns true iff expr has an assigned value within this time frame. */
bool TimeFrame::has_value( FQExpr expr )
{
    // symbol is defined in witness' language
    FQExprs& lang = f_owner.lang();
    assert( find( lang.begin(), lang.end(), expr) != lang.end());

    FQExpr2ExprMap::iterator eye;

    eye = f_map.find( expr );
    return (f_map.end() != eye);
}

/* Sets value for expr */
void TimeFrame::set_value( FQExpr fqexpr, Expr_ptr value )
{
    // symbol is defined in witness' language
    FQExprs& lang = f_owner.lang();
    assert( find( lang.begin(), lang.end(), fqexpr) != lang.end());

    DRIVEL << fqexpr << " := " << value << endl;
    f_map.insert( make_pair< FQExpr, Expr_ptr > (fqexpr, value));
}

Witness::Witness(string name, step_t j, step_t k)
    : f_id(name)
    , f_j(j)
{
    DEBUG
        << "Created new witness: "
        << f_id << " (" << k << " steps)"
        << endl;

    if (k) {
        extend(k);
    }
}

TimeFrame& Witness::extend(Witness& w)
{
    assert(k() <= w.j()); // overlap not yet supported

   // there may be a gap, fill it with empty timeframes
    for (step_t i = k(); i < w.j(); ++ i) {
        TimeFrame_ptr tf = new TimeFrame(*this);
        f_frames.push_back(tf);

        step_t curr = length() -1 ;
        DEBUG << "Added empty TimeFrame " << curr
              << " to witness " << id()
              << " @" << tf
              << endl;
    }

    TimeFrame_ptr last = NULL;
    for (TimeFrames::iterator i = w.frames().begin(); i != w.frames().end(); ++ i) {
        f_frames.push_back(*i); // copy
        last = (*i);
    }

    assert( last);
    return * last;
}

TimeFrame& Witness::extend(step_t k)
{
    TimeFrame_ptr tf = NULL;
    while (f_j != k --) {
        tf = new TimeFrame(*this);
        f_frames.push_back(tf);

        step_t curr = length() -1 ;
        DEBUG << "Added empty TimeFrame " << curr
              << " to witness " << id()
              << " @" << tf
              << endl;
    }

    assert(tf);
    return *tf;
}

/* Retrieves value for expr, throws an exception if no value exists. */
Expr_ptr Witness::value( FQExpr fq )
{
    return f_frames[fq.time()]
        -> value( FQExpr(fq.ctx(), fq.expr()));
}

/* Returns true iff expr has an assigned value within this time frame. */
bool Witness::has_value( FQExpr fq )
{
    return f_frames[fq.time()]
        -> has_value( FQExpr(fq.ctx(), fq.expr()));
}


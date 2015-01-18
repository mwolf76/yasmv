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
#include <sstream>
#include <witness.hh>

const char* DuplicateWitnessId::what() const throw()
{
    std::ostringstream oss;
    oss << "Duplicate witness ID:  "
        << f_id << " is already registered."
        << std::endl
        ;

    return oss.str().c_str();
}

const char* UnknownWitnessId::what() const throw()
{
    std::ostringstream oss;
    oss << "Unknown witness ID:  "
        << f_id << " is not registered."
        << std::endl
        ;

    return oss.str().c_str();
}

const char* IllegalTime::what() const throw()
{
    std::ostringstream oss;
    oss << "Illegal time: "
        << f_time
        << std::endl
        ;

    return oss.str().c_str();
}

const char* NoValue::what() const throw()
{
    std::ostringstream oss;
    oss << "No value for `" << f_id << "`";

    return oss.str().c_str();
}

TimeFrame::TimeFrame(Witness& owner)
    : f_owner(owner)
{}

TimeFrame::~TimeFrame()
{}

/* Retrieves value for expr, throws an exception if no value exists. */
Expr_ptr TimeFrame::value( Expr_ptr expr )
{
    // symbol is defined in witness' language
    Exprs& lang = f_owner.lang();
    assert( find( lang.begin(), lang.end(), expr) != lang.end());

    Expr2ExprMap::iterator eye;

    eye = f_map.find( expr );
    if (f_map.end() == eye) {
        throw NoValue(expr);
    }

    return (*eye).second;
}

/* Returns true iff expr has an assigned value within this time frame. */
bool TimeFrame::has_value( Expr_ptr expr )
{
    // symbol is defined in witness' language
    Exprs& lang
        (f_owner.lang());
    if (lang.end() == std::find( lang.begin(), lang.end(), expr)) {
        std::cerr << expr << std::endl;
        assert(false);
    }

    Expr2ExprMap::iterator eye;

    eye = f_map.find( expr );
    return (f_map.end() != eye);
}

/* Sets value for expr */
void TimeFrame::set_value( Expr_ptr expr, Expr_ptr value )
{
    // symbol is defined in witness' language
    Exprs& lang = f_owner.lang();
    assert( find( lang.begin(), lang.end(), expr) != lang.end());

    DEBUG
        << expr
        << " := "
        << value
        << std::endl;

    f_map.insert( std::make_pair< Expr_ptr, Expr_ptr >
                  (expr, value));
}

Witness::Witness(Atom id, Atom desc, step_t j)
    : f_id(id)
    , f_desc(desc)
    , f_j(j)
{
    DEBUG
        << "Created new witness: "
        << f_id
        << ", starting at time "
        << f_j
        << std::endl;
}

TimeFrame& Witness::extend(Witness& w)
{
    // seizing ownership of the TimeFrames from w
    TimeFrame_ptr last = NULL;
    for (TimeFrames::iterator i = w.frames().begin(); i != w.frames().end(); ++ i) {
        f_frames.push_back(*i);
        last = (*i);
    }
    w.f_frames.clear();

    assert( last);
    return * last;
}

TimeFrame& Witness::extend()
{
    TimeFrame_ptr tf = new TimeFrame(*this);
    f_frames.push_back(tf);

    step_t last = 1 + last_time();
    DEBUG << "Added empty TimeFrame " << last
          << " to witness " << id()
          << " @" << tf
          << std::endl;

    assert(tf);
    return *tf;
}

/* Retrieves value for expr, throws an exception if no value exists. */
Expr_ptr Witness::value( Expr_ptr expr, step_t time)
{
    if (time < first_time() || time > last_time()) {
        throw IllegalTime(time);
    }
    return f_frames[ time ]
        -> value( expr );
}

/* Returns true iff expr has an assigned value within this time frame. */
bool Witness::has_value( Expr_ptr expr, step_t time)
{
    if (time < first_time() || time > last_time()) {
        return false;
    }
    return f_frames[ time ]
        -> has_value( expr );
}


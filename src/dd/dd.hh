/**
 *  @file dd.hh
 *  @brief Decision Diagram class
 *
 *  This module contains definitions and services that implement a
 *  lightweight decision diagram class or DD. DDs are used to store
 *  compilation result in a time-independent fashion, in order to make
 *  it easy to instantiate timed expressions and convert them to CNF.
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

#ifndef DECISION_DIAGRAMS_H
#define DECISION_DIAGRAMS_H

#include <climits>

#include <common.hh>
#include <cuddObj.hh>

typedef class YDD  {

public:
    YDD(bool value)
        : f_index( UINT_MAX ^ (value ? 1 : 0))
        , f_then(NULL)
        , f_else(NULL)
    {}

    YDD(int index, YDD *t, YDD *e)
        : f_index(index)
        , f_then(t)
        , f_else(e)
    {}

    inline bool is_true() const
    {
        assert(NULL == f_then &&
               NULL == f_else &&
               UINT_MAX -1 <= f_index);

        return f_index == UINT_MAX;
    }

    inline bool is_false() const
    {
        assert(NULL == f_then &&
               NULL == f_else &&
               UINT_MAX -1 <= f_index);

        return f_index != UINT_MAX;
    }

    inline bool is_const() const
    { return (UINT_MAX - 1) <= f_index; }

    inline int index() const
    { return f_index; }

    inline YDD* Then() const
    {
        assert (NULL != f_then);
        return f_then;
    }

    inline YDD* Else() const
    {
        assert (NULL != f_else);
        return f_else;
    }

private:
    unsigned f_index;

    YDD *f_then; /* left  */
    YDD *f_else; /* right */
} *YDD_ptr;

typedef vector <YDD_ptr> YDDVector;

#endif

/**
 * @file tcbi.hh
 * @brief Expression management
 *
 * This header file contains the declarations required by the Timed
 * Canonical Bit Identifier class.
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

#ifndef TCBI_H
#define TCBI_H

#include <enc/ucbi.hh>

namespace enc {

/* Timed Canonical Bit Identifiers */
class TCBI {
public:
    TCBI(const UCBI& ucbi, step_t timebase);
    TCBI(const TCBI& tcbi);

    inline Expr_ptr expr() const
    { return f_expr; }

    inline unsigned bitno() const
    { return f_bitno; }

    inline step_t absolute_time() const
    {
        /* reserved for frozen variables */
        if (f_time == FROZEN)
            return 0;

        /* always treat negative time as absolute */
        if (is_negative(f_time))
            return f_time;

        return f_time + f_base;
    }

    inline step_t time() const
    { return f_time; }

    inline step_t base() const
    { return f_base; }

private:

    // expression body
    Expr_ptr f_expr;

    // expression time (default is 0)
    step_t f_time;

    // bit number
    unsigned f_bitno;

    // time base (default is 0)
    step_t f_base;

};

std::ostream& operator<<(std::ostream& os, const TCBI& tcbi);

struct TCBIHash {
    long operator() (const TCBI& k) const;
};

struct TCBIEq {
    bool operator() (const TCBI& x, const TCBI& y) const;
};

};

#endif

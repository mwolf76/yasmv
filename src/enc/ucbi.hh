/**
 * @file ucbi.hh
 * @brief Expression management
 *
 * This header file contains the declarations required by the Untimed
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
#ifndef UCBI_H
#define UCBI_H

#include <expr/expr.hh>

/* Untimed Canonical Bit Identifiers */
class UCBI {
public:
    UCBI(Expr_ptr expr, step_t time_ofs, unsigned bitno);
    UCBI(const UCBI& ucbi);

    inline Expr_ptr expr() const
    { return f_expr; }

    inline step_t time() const
    { return f_time; }

    inline unsigned bitno() const
    { return f_bitno; }

private:
    // expression body
    Expr_ptr f_expr;

    // expression time (default is 0)
    step_t f_time;

    // bit number
    unsigned f_bitno;
};

std::ostream& operator<<(std::ostream& os, const UCBI& ucbi);

struct UCBIHash {
    long operator() (const UCBI& k) const;
};

struct UCBIEq {
    bool operator() (const UCBI& x, const UCBI& y) const;
};

#endif

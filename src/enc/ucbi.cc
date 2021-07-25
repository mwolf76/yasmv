/**
 * @file ucbi.cc
 * @brief Encoding subsystem, Untimed Canonical Boolean Identifier class implementation.
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

#include <enc/ucbi.hh>
#include <expr/printer/printer.hh>

namespace enc {

UCBI::UCBI(Expr_ptr expr, step_t time, unsigned bitno)
    : f_expr(expr)
    , f_time(time)
    , f_bitno(bitno)
{}

UCBI::UCBI(const UCBI& ucbi)
    : f_expr(ucbi.expr())
    , f_time(ucbi.time())
    , f_bitno(ucbi.bitno())
{}

std::ostream& operator<<(std::ostream& os, const UCBI& ucbi)
{
    Expr_ptr expr
        (ucbi.expr());
    step_t step
        (ucbi.time());
    unsigned bitno
        (ucbi.bitno());

    os << "+" << step
       << "{" ;

    Printer (os)
        << "::"
        << expr ;

    os << "}."
       << bitno ;

    return os;
}

long UCBIHash::operator() (const UCBI& k) const
{
    long x, res = 0;
    ExprHash eh;

    long v0 = eh(*k.expr());
    long v1 = k.time();
    long v2 = k.bitno();

    res = (res << 4) + v0;
    if ((x = res & 0xF0000000L) != 0) {
        res ^= (x >> 24);
    }
    res &= ~x;

    res = (res << 4) + v1;
    if ((x = res & 0xF0000000L) != 0) {
        res ^= (x >> 24);
    }
    res &= ~x;

    res = (res << 4) + v2;
    if ((x = res & 0xF0000000L) != 0) {
        res ^= (x >> 24);
    }
    res &= ~x;

    return res;
}

bool UCBIEq::operator() (const UCBI& x, const UCBI& y) const
{
    return x.expr() == y.expr() &&
        x.time() == y.time() &&
        x.bitno() == y.bitno() ;
}

};

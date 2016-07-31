/**
 * @file tcbi.cc
 * @brief Encoding subsystem, Timed Canonical Boolean Identifier class implementation.
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

#include <enc/tcbi.hh>
#include <expr/printer/printer.hh>

TCBI::TCBI(const UCBI& ucbi, step_t base)
    : f_expr(ucbi.expr())
    , f_time(ucbi.time())
    , f_bitno(ucbi.bitno())
    , f_base(base)
{}

TCBI::TCBI(const TCBI& tcbi)
    : f_expr(tcbi.expr())
    , f_time(tcbi.time())
    , f_bitno(tcbi.bitno())
    , f_base(tcbi.base())
{}

std::ostream& operator<<(std::ostream& os, const TCBI& tcbi)
{
    Expr_ptr expr
        (tcbi.expr());
    step_t step
        (tcbi.time());
    unsigned bitno
        (tcbi.bitno());
    step_t timebase
        (tcbi.base());

    os << "@" << timebase
       << "{"

       << "+" <<  step
       << "{" ;

    Printer (os)
        << "::"
        << expr ;

    os << "}."
       << bitno ;

    os << "}" ;

    return os;
}

long TCBIHash::operator() (const TCBI& k) const
{
    long x, res = 0;
    ExprHash eh;

    long v0 = eh(*k.expr());
    long v1 = k.absolute_time();
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

bool TCBIEq::operator() (const TCBI& x, const TCBI& y) const
{
    step_t abs_time_x
        (x.absolute_time());
    step_t abs_time_y
        (y.absolute_time());

    return
        x.expr() == y.expr() &&
        x.bitno() == y.bitno() &&
        abs_time_x == abs_time_y;
}

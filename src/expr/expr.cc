/**
 * @file expr.cc
 * @brief Expression management
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

#include <expr/expr.hh>
#include <expr/expr_mgr.hh>
#include <expr/printer/printer.hh>

#include <enc/enc_mgr.hh>

#include <iomanip>

namespace expr {

value_t Expr_TAG::value() const
{
    ExprMgr& em
        (ExprMgr::INSTANCE());

    if (em.is_false(const_cast<Expr_ptr> (this)))
        return 0;

    if (em.is_true(const_cast<Expr_ptr> (this)))
        return 1;

    assert (ICONST == f_symb ||
            HCONST == f_symb ||
            OCONST == f_symb ||
            BCONST == f_symb ||
            QSTRING == f_symb ||
            INSTANT == f_symb );

    return u.f_value;
}

std::ostream& operator<<(std::ostream& os, const Expr_ptr expr)
{
    Printer (os)
        << expr;

    return os;
}

int LexicographicOrdering::operator() (const Expr_ptr x,
                                       const Expr_ptr y) const
{
    ExprMgr& em
        (ExprMgr::INSTANCE());

    if (em.is_constant(x) && em.is_identifier(y))
        return 1;

    if (em.is_constant(x) && em.is_constant(y))
        return x -> value() < y -> value();

    if (em.is_identifier(x) && em.is_identifier(y))
        return x -> atom() < y -> atom();

    assert(false);
}

long ExprHash::operator() (const Expr& k) const
{
    if (k.f_symb == IDENT)
        return (long)(k.u.f_atom);

    long v0, v1, x, res = (long)(k.f_symb);

    if (k.f_symb == ICONST
        || k.f_symb == HCONST
        || k.f_symb == BCONST
        || k.f_symb == OCONST
        || k.f_symb == INSTANT) {
        v0 = (long)(k.u.f_value);
        v1 = (long)(k.u.f_value >> sizeof(long));
    }
    else {
        v0 = (long)(k.u.f_lhs);
        v1 = (long)(k.u.f_rhs);
    }

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

    return res;
}

bool ExprEq::operator() (const Expr& x, const Expr& y) const
{
    return
        // both exprs must be the same type and...
        x.f_symb == y.f_symb
        && (
            /* ...either have the same identifier */
            (x.f_symb == IDENT  && *x.u.f_atom == *y.u.f_atom) ||

            /* ...or have the same constant value */
            (x.f_symb >= ICONST && x.f_symb <= INSTANT
             && x.u.f_value == y.u.f_value) ||

            /* ...or share the same subtrees */
            (x.u.f_lhs == y.u.f_lhs &&
             x.u.f_rhs == y.u.f_rhs));
}

};

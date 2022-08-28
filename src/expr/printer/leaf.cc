/**
 * @file leaf.cc
 * @brief Expression printer implementation, leaf services.
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
#include <expr/walker/walker.hh>

#include <enc/enc_mgr.hh>

#include <iomanip>

namespace expr {

    static void print_dec_leaf(const Expr_ptr expr, std::ostream& os)
    {
        value_t value(expr->value());

        os
            << std::dec
            << value;
    }

    static void print_hex_leaf(const Expr_ptr expr, std::ostream& os)
    {
        value_t value(expr->value());

        os
            << std::hex
            << "0x"
            << value;
    }

    // duplicated
    static inline value_t pow2(unsigned exp)
    {
        value_t res = 1;

        if (!exp)
            return res;

        ++res;

        while (--exp)
            res <<= 1;

        return res;
    }

    static void print_bin_leaf(const Expr_ptr expr, std::ostream& os)
    {
        enc::EncodingMgr& bm(enc::EncodingMgr::INSTANCE());

        std::vector<bool> booleanization;

        const unsigned base(2);

        const unsigned width(bm.word_width());

        value_t value(expr->value());

        if (value < 0)
            value += pow2(width); // 2's complement

        for (unsigned i = 0; i < width; ++i) {
            bool digit(value % base);

            booleanization.push_back(digit);

            value /= base;
        }

        assert(!value); /* TODO: turn this into an exception */

        for (std::vector<bool>::reverse_iterator ri = booleanization.rbegin();
             ri != booleanization.rend(); ++ri) {

            bool d(*ri);

            os
                << (d ? "1" : "0");
        }
    }

    static void print_oct_leaf(const Expr_ptr expr, std::ostream& os)
    {
        value_t value(expr->value());

        os
            << std::oct
            << "0"
            << value;
    }

    static void print_atom_leaf(const Expr_ptr expr, std::ostream& os)
    {
        Atom& atom(expr->atom());

        os
            << atom;
    }

    void Printer::print_leaf(const Expr_ptr expr)
    {
        switch (expr->f_symb) {
            case ICONST:
            case INSTANT:
                print_dec_leaf(expr, f_os);
                break;

            case HCONST:
                print_hex_leaf(expr, f_os);
                break;

            case BCONST:
                print_bin_leaf(expr, f_os);
                break;

            case OCONST:
                print_oct_leaf(expr, f_os);
                break;

            case IDENT:
            case QSTRING:
                print_atom_leaf(expr, f_os);
                break;

            case UNDEF:
                f_os
                    << "UNDEFINED";
                break;

            default:
                throw UnsupportedLeaf();
        } /* switch() */
    }

}; // namespace expr

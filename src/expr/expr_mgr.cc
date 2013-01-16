/**
 *  @file expr_mgr.cc
 *  @brief Expression management. ExprMgr class
 *
 *  This module contains definitions and services that implement an
 *  optimized storage for expressions. Expressions are stored in a
 *  Directed Acyclic Graph (DAG) for data sharing.
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
#include <common.hh>
#include <expr_mgr.hh>

// singleton instance initialization
ExprMgr_ptr ExprMgr::f_instance = NULL;

ExprMgr::ExprMgr()
{
    // boolean type identifier, false and true identifiers
    bool_expr = make_identifier(BOOL_TOKEN);
    false_expr = make_identifier(FALSE_TOKEN);
    true_expr = make_identifier(TRUE_TOKEN);

    // integer types identifiers
    {
        ostringstream oss; oss << UNSIGNED_TOKEN << " " << INT_TOKEN;
        unsigned_int_expr = make_identifier(oss.str());
    }
    {
        ostringstream oss; oss << SIGNED_TOKEN << " " << INT_TOKEN;
        signed_int_expr = make_identifier(oss.str());
    }
    int_expr = make_identifier(INT_TOKEN);

    // fixed-point real types identifiers
    {
        ostringstream oss; oss << UNSIGNED_TOKEN << " " << FXD_TOKEN;
        unsigned_fxd_expr = make_identifier(oss.str());
    }
    {
        ostringstream oss; oss << SIGNED_TOKEN  << " "  << FXD_TOKEN;
        signed_fxd_expr = make_identifier(oss.str());
    }
    fxd_expr = make_identifier(FXD_TOKEN);

    main_expr = make_identifier(MAIN_TOKEN);
    enum_expr = make_identifier(ENUM_TOKEN);
    inst_expr = make_identifier(INST_TOKEN);
    array_expr = make_identifier (ARRAY_TOKEN);

    DEBUG << "ExprMgr @" << this << " initialized" << endl;
}

ExprMgr::~ExprMgr()
{
    DEBUG << "ExprMgr @" << this << " deinitialized" << endl;
}

Expr_ptr ExprMgr::make_enum_type(ExprSet& literals)
{
    Expr_ptr res = NULL;

    /* reverse iteration */
    for (ExprSet::reverse_iterator eye = literals.rbegin();
         eye != literals.rend(); eye ++) {
        if (!res) res = (*eye);
        else res = make_expr(COMMA, (*eye), res);
    }

    return make_expr(SET, res, NULL);
}

// Expr_ptr ExprMgr::make_wconst(Atom atom)
// {
//     regex wconst_rx("0(u|s)(b|d|o|h|)(/d+)_(.+)");
//     cmatch match;

//     regex_match(atom.c_str(), match, wconst_rx);
//     assert (match.size() == 4);

//     string sign_flag(match[0]);
//     string type_flag(match[1]);
//     string size_field(match[2]);
//     string wliteral(match[3]);
//     bool is_signed = (sign_flag == "s");
//     unsigned short wsize = atoi(size_field.c_str());

//     value_t value = 0ULL;

//     if (match[1] == "b") {
//         if (wsize != wliteral.size())
//             throw BadWordConstException("Boolean word constants must match the word size.");

//         int i;
//         for (i = wliteral.size() -1;
//              i >= (is_signed) ? 1 : 0; -- i) {
//             value = 2 * value + wliteral[i];
//         }

//         // MSB is -2^(wsize)
//         if ((is_signed) && (wliteral[0] == '1')) {
//             value -= pow2(i);
//         }

//     }

//     // NEG not supported here
//     else if (match[1] == "d") {
//         value = strtoll(wliteral.c_str(), NULL, 10);
//     }
//     else if (match[1] == "o") {
//         value = strtoll(wliteral.c_str(), NULL, 8);
//     }
//     else if (match[1] == "h") {
//         value = strtoll(wliteral.c_str(), NULL, 16);
//     }
//     else assert(0);

//     // range check
//     if (value >= pow2(wsize - (is_signed ? 1 : 0))) {
//         throw BadWordConstException("Decimal value not representable with this word size.");
//     }

//     return is_signed
//         ? make_swconst(wsize, value)
//         : make_uwconst(wsize, value);
// }

value_t ExprMgr::pow2(unsigned exp)
{
    value_t res = 1;
    for (unsigned i = exp; i; -- i) {
        res *= 2;
    }
    return res;
}

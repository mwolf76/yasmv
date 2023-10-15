/**
 * @file expr_mgr.cc
 * @brief Expression Manager class implementation.
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

#include <cmath>
#include <common/common.hh>
#include <expr_mgr.hh>

#include <stack>
#include <vector>

#include <utils/logging.hh>

namespace expr {

    // singleton instance initialization
    ExprMgr_ptr ExprMgr::f_instance = NULL;

    ExprMgr::ExprMgr()
    {
        const void* instance { this };

        /* generate internal symbol definitions */
        time_expr = make_identifier(TIME_TOKEN);
        bool_expr = make_identifier(BOOL_TOKEN);
        string_expr = make_identifier(STRING_TOKEN);
        false_expr = make_identifier(FALSE_TOKEN);
        true_expr = make_identifier(TRUE_TOKEN);

        {
            std::ostringstream oss;
            oss
                << CONST_TOKEN << " "
                << INT_TOKEN;

            const_int_expr = make_identifier(oss.str());
        }

        {
            std::ostringstream oss;
            oss
                << UNSIGNED_TOKEN
                << INT_TOKEN;

            unsigned_int_expr = make_identifier(oss.str());
        }

        {
            std::ostringstream oss;
            oss
                << SIGNED_TOKEN
                << INT_TOKEN;

            signed_int_expr = make_identifier(oss.str());
        }

        array_expr = make_identifier(ARRAY_TOKEN);
        empty_expr = make_identifier(EMPTY_TOKEN);

        DEBUG
            << "ExprMgr @"
            << instance
            << " initialized"
            << std::endl;
    }

    ExprMgr::~ExprMgr()
    {
        const void* instance { this };
        DEBUG
            << "Destroyed ExprMgr @"
            << instance
            << std::endl;
    }

    Expr_ptr ExprMgr::make_enum_type(ExprSet& literals)
    {
        Expr_ptr res { NULL };

        for (ExprSet::reverse_iterator eye = literals.rbegin();
             eye != literals.rend(); eye++) {

            res = (!res)
                      ? *eye
                      : make_expr(SET_COMMA, *eye, res);
        }

        return make_set(res);
    }

    const Atom& ExprMgr::internalize(Atom atom)
    {
        boost::mutex::scoped_lock lock { f_atom_mutex };

        AtomPoolHit ah { f_atom_pool.insert(atom) };
        const Atom& pooled_atom { *ah.first };

        return pooled_atom;
    }

    Expr_ptr ExprMgr::make_identifier(Atom atom)
    {
        boost::mutex::scoped_lock lock { f_atom_mutex };

        AtomPoolHit ah { f_atom_pool.insert(atom) };
        const Atom& pooled_atom { *ah.first };

        return make_expr(IDENT, pooled_atom);
    }

    Expr_ptr ExprMgr::make_qstring(Atom atom)
    {
        boost::mutex::scoped_lock lock { f_atom_mutex };

        AtomPoolHit ah { f_atom_pool.insert(atom) };
        const Atom& pooled_atom { *ah.first };

        return make_expr(QSTRING, pooled_atom);
    }

    Expr_ptr ExprMgr::__make_expr(Expr_ptr expr)
    {
        boost::mutex::scoped_lock lock { f_expr_mutex };

        ExprPoolHit eh { f_expr_pool.insert(*expr) };
        Expr_ptr pooled_expr { const_cast<Expr_ptr>(&(*eh.first)) };

        return pooled_expr;
    }

    Expr_ptr ExprMgr::left_associate_dot(const Expr_ptr expr)
    {
        Expr_ptr res { NULL };
        std::vector<Expr_ptr> fragments;

        // 1. in-order visit, build fwd expr stack
        std::stack<Expr_ptr> stack;
        stack.push(expr);

        while (0 < stack.size()) {
            Expr_ptr top { stack.top() };
            stack.pop();

            if (is_dot(top)) {
                stack.push(top->rhs());
                stack.push(top->lhs());
                continue;
            }

            fragments.push_back(top);
        }

        // 2. good, now build canonical AST
        for (std::vector<Expr_ptr>::const_iterator i = fragments.begin();
             fragments.end() != i; ++i)

            res = res
                      ? make_expr(DOT, res, *i)
                      : *i;

        return res;
    }

    static inline value_t pow2(unsigned exp)
    {
        value_t res = 1;
        if (!exp) {
            return res;
        }
        ++res;

        while (--exp) {
            res <<= 1;
        }

        return res;
    }

    value_t ExprMgr::decimal_lookup(const char* decimal_repr)
    {
        opts::OptsMgr& om { opts::OptsMgr::INSTANCE() };

        double val { strtod(decimal_repr, NULL) };
        unsigned precision { om.precision() };

        value_t j, m, k;
        double fm, dj, dm, dk, pp { pow(2.0, precision) };

        j = 0;
        k = pow2(precision) - 1;

        while (k - j > 1) {
            m = j + (k - j) / 2;
            fm = (double) m / pp;

            if (fm <= val) {
                j = m;
            }

            else if (val <= fm) {
                k = m;
            }
        }

        dj = fabs(val - ((double) j / pp));
        dm = fabs(val - ((double) m / pp));
        dk = fabs(val - ((double) k / pp));

        if (dj <= dm && dj <= dk) {
            return j;
        }

        else if (dk <= dj && dk <= dm) {
            return k;
        }

        else if (dm <= dj && dm <= dk) {
            return m;
        }

        // unreachable
        assert(false);
    }

    ExprVector ExprMgr::array_literals(const Expr_ptr expr) const
    {
        assert(is_array(expr));

        ExprVector res;
        Expr_ptr eye;
        for (eye = expr->lhs(); is_array_comma(eye); eye = eye->rhs()) {
            res.push_back(eye->lhs());
        }
        res.push_back(eye);

        return res;
    }

}; // namespace expr

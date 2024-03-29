/**
 * @file monolithical.cc
 * @brief Monolithical type classes implementation
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

#include <type.hh>
#include <type_mgr.hh>

namespace type {

    BooleanType::BooleanType(TypeMgr& owner)
        : MonolithicType(owner)
    {
	TypeMgr& tm { f_owner };
	expr::ExprMgr& em { tm.em() };

        f_repr = em.make_boolean_type();
    }

    unsigned BooleanType::width() const
    {
        return 1;
    }

    EnumType::EnumType(TypeMgr& owner, expr::ExprSet& literals)
        : MonolithicType(owner)
        , f_literals(literals)
    {
	TypeMgr& tm { f_owner };
	expr::ExprMgr& em { tm.em() };

        const symb::Literals& lits { tm.literals() };

        for (expr::ExprSet::const_iterator i = literals.begin(); i != literals.end(); ++i) {
            const expr::Expr_ptr& lit { *i };

            if (!em.is_identifier(lit)) {
                throw IdentifierExpected(lit);
            }

            if (lits.end() != lits.find(lit)) {
                throw DuplicateLiteral(lit);
            }
        }

        f_repr = em.make_enum_type(f_literals);
    }

    unsigned EnumType::width() const
    {
        return 1;
    }

    value_t EnumType::value(expr::Expr_ptr lit) const
    {
        value_t res { 0 };
        for (expr::ExprSet::iterator eye = f_literals.begin();
             eye != f_literals.end(); ++eye, ++res) {

            if (*eye == lit) {
                return res;
            }
        }

        assert(false); // not found
    }

}; // namespace type

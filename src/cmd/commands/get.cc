/*
 * @file get.cc
 * @brief Command `get` class implementation.
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

#include <cstdlib>
#include <cstring>

#include <cmd/commands/commands.hh>
#include <cmd/commands/get.hh>

#include <expr/expr.hh>
#include <expr/expr_mgr.hh>

#include <witness/witness.hh>
#include <witness/witness_mgr.hh>

namespace cmd {

    Get::Get(Interpreter& owner)
        : Command(owner)
        , f_identifier(NULL)
    {}

    Get::~Get()
    {}

    void Get::set_identifier(expr::Expr_ptr id)
    {
        f_identifier = id;
    }

    void Get::print_assignment(std::ostream& os, expr::Expr_ptr id)
    {
        env::Environment& env { env::Environment::INSTANCE() };

        /* raises an exception on failures */
        expr::Expr_ptr value { env.get(id) };

        os
            << outPrefix
            << id
            << " := "
            << value
            << std::endl;
    }

    void Get::print_all_assignments(std::ostream& os)
    {
        env::Environment& env { env::Environment::INSTANCE() };
        const expr::ExprSet& identifiers { env.identifiers() };

        for (expr::ExprSet::const_iterator i = identifiers.begin();
             i != identifiers.end(); ++i) {

            expr::Expr_ptr id { *i };
            print_assignment(os, id);
        }
    }

    utils::Variant Get::print_one_assignment(std::ostream& os, expr::Expr_ptr id)
    {
        utils::Variant res { errMessage };

        try {
            print_assignment(os, id);
            res = utils::Variant(okMessage);
        } catch (env::NoSuchIdentifier& nsi) {
            const char* what { nsi.what() };

            os
                << wrnPrefix
                << what
                << std::endl;
        }

        return res;
    }

    utils::Variant Get::operator()()
    {
        /* FIXME: implement stream redirection for std{out,err} */
        std::ostream& out { std::cout };

        if (NULL == f_identifier) {
            print_all_assignments(out);
            return utils::Variant(okMessage);
        } else {
            return print_one_assignment(out, f_identifier);
        }
    }

    GetTopic::GetTopic(Interpreter& owner)
        : CommandTopic(owner)
    {}

    GetTopic::~GetTopic()
    {
        TRACE
            << "Destroyed get topic"
            << std::endl;
    }

    void GetTopic::usage()
    {
        display_manpage("get");
    }

}; // namespace cmd

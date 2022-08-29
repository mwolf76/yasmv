/**
 * @file last.cc
 * @brief Command `last` class implementation.
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

#include <cmd/interpreter.hh>

#include <cmd/commands/commands.hh>
#include <cmd/commands/last.hh>

#include <iomanip>

namespace cmd {

    Last::Last(Interpreter& owner)
        : Command(owner)
        , f_message(NULL)
    {}

    Last::~Last()
    {
    }

    utils::Variant Last::operator()()
    {
        opts::OptsMgr& om { opts::OptsMgr::INSTANCE() };
        Interpreter& interpreter { Interpreter::INSTANCE() };

        std::ostream& out { std::cout };

        utils::Variant& last { interpreter.last_result() };

        if (last.is_string()) {
            if (!om.quiet()) {
                out << outPrefix;
            }

            std::string value { last.as_string() };
            if (value == okMessage) {
                out
                    << "Last command was SUCCESSFUL"
                    << std::endl;
            }

            else if (value == errMessage) {
                out
                    << "Last command was UNSUCCESSFUL"
                    << std::endl;
            }

            else {
                assert(false); /* unexpected */
            }

            return last;
        }

        else {
            if (!om.quiet()) {
                out << outPrefix;
            }

            out
                << "No status available"
                << std::endl;

            return utils::Variant(errMessage);
        }
    }

    LastTopic::LastTopic(Interpreter& owner)
        : CommandTopic(owner)
    {}

    LastTopic::~LastTopic()
    {
        TRACE
            << "Destroyed last topic"
            << std::endl;
    }

    void LastTopic::usage()
    {
        display_manpage("last");
    }

}; // namespace cmd

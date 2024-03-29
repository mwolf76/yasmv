/**
 * @file list_traces.cc
 * @brief Command `list-traces` class implementation.
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

#include <cmd/commands/commands.hh>
#include <cmd/commands/list_traces.hh>

#include <witness/witness_mgr.hh>

namespace cmd {

    ListTraces::ListTraces(Interpreter& owner)
        : Command(owner)
    {}

    ListTraces::~ListTraces()
    {}

    utils::Variant ListTraces::operator()()
    {
        witness::WitnessMgr& wm { witness::WitnessMgr::INSTANCE() };
        witness::Witness& current(wm.current());

        witness::WitnessList::const_iterator eye;
        std::ostream& os { std::cout };

        const witness::WitnessList& witnesses { wm.witnesses() };
        if (!witnesses.empty()) {
            for (eye = witnesses.begin(); eye != witnesses.end(); ++eye) {
                witness::Witness& w { **eye };

                const char* tmp {
                    w.id() == current.id()
                        ? "[*] "
                        : "    "
                };

                os
                    << tmp
                    << w.id()
                    << "\t\t"
                    << w.desc()
                    << "\t\t"
                    << w.size()
                    << std::endl;
            }

            os << std::endl;
            return utils::Variant(okMessage);
        }

        else {
            os
                << "No traces to list."
                << std::endl
                << std::endl;

            return utils::Variant(errMessage);
        }
    }

    ListTracesTopic::ListTracesTopic(Interpreter& owner)
        : CommandTopic(owner)
    {}

    ListTracesTopic::~ListTracesTopic()
    {
        TRACE
            << "Destroyed list-traces topic"
            << std::endl;
    }

    void ListTracesTopic::usage()
    {
        display_manpage("list-traces");
    }

}; // namespace cmd

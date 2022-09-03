/**
 * @file commands.cc
 * @brief Command interpreter subsystem implementation.
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

#include <common/common.hh>
#include <expr.hh>

#include <iostream>
#include <sstream>

#include <ctime>

#include <commands.hh>

/* algorithms */
#include <check/check.hh>
#include <reach/reach.hh>
#include <sim/simulation.hh>

namespace cmd {
    const std::string outPrefix { "-- " };
    const std::string wrnPrefix { "!! " };

    const std::string okMessage { "Ok" };
    const std::string errMessage { "ERROR" };
    const std::string byeMessage { "Bye" };

    Command::Command(Interpreter& owner)
        : f_owner(owner)
    {
        const void* instance { this };
        DRIVEL
            << "Initialized command @"
            << instance
            << std::endl;
    }

    Command::~Command()
    {
        const void* instance { this };
        DRIVEL << "Destroyed command @"
               << instance
               << std::endl;
    }

    CommandTopic::CommandTopic(Interpreter& owner)
        : f_owner(owner)
    {
        const void* instance { this };
        DRIVEL
            << "Initialized command topic @"
            << instance
            << std::endl;
    }

    CommandTopic::~CommandTopic()
    {
        const void* instance { this };
        DRIVEL << "Destroyed command topic @"
               << instance
               << std::endl;
    }

} // namespace cmd

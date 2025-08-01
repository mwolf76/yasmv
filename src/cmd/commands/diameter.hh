/**
 * @file diameter.hh
 * @brief Command-interpreter subsystem related classes and definitions.
 *
 * This header file contains the handler interface for the `diameter`
 * command.
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

#ifndef DIAMETER_CMD_H
#define DIAMETER_CMD_H

#include <cmd/command.hh>

namespace cmd {

    class Diameter: public Command {
    public:
        Diameter(Interpreter& owner);
        virtual ~Diameter();

        /* run() */
        utils::Variant virtual operator()();

    private:
        std::ostream& f_out;

        // -- helpers -------------------------------------------------------------
        bool check_requirements() const;
    };

    typedef Diameter* Diameter_ptr;

    class DiameterTopic: public CommandTopic {
    public:
        DiameterTopic(Interpreter& owner);
        virtual ~DiameterTopic();

        void virtual usage();
    };

}; // namespace cmd

#endif /* DIAMETER_CMD_H */

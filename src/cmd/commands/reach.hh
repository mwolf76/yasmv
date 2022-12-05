/**
 * @file reach.hh
 * @brief Command-interpreter subsystem related classes and definitions.
 *
 * This header file contains the handler interface for the `reach`
 * command.
 *
 * Copyright (C) 2012-2018 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/

#ifndef REACH_CMD_H
#define REACH_CMD_H

#include <algorithms/reach/reach.hh>
#include <cmd/command.hh>

namespace cmd {

    class Reach: public Command {
    public:
        Reach(Interpreter& owner);
        virtual ~Reach();

        /** cmd params */
        void set_target(expr::Expr_ptr target);

        /* guided reachability support: forward, backward and global guides */
        void add_constraint(expr::Expr_ptr constraint);

	/* quiet mode */
	void go_quiet();

        /* run() */
        utils::Variant virtual operator()();

    private:
        std::ostream& f_out;

        /* the negation of invariant property to be verified */
        expr::Expr_ptr f_target;

	/* if true and a witness is found, it is immediately displayed */
	bool f_quiet;

        /* constraints for guided reachability */
        expr::ExprVector f_constraints;

        // -- helpers -------------------------------------------------------------
        bool check_requirements();
    };
    using Reach_ptr = Reach*;

    class ReachTopic: public CommandTopic {
    public:
        ReachTopic(Interpreter& owner);
        virtual ~ReachTopic();

        void virtual usage();
    };

} // namespace cmd

#endif /* REACH_CMD_H */

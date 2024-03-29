/**
 *  @file dd_walker.hh
 *  @brief DD algorithm-unaware walk pattern implementation
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

#ifndef DD_WALKER_H
#define DD_WALKER_H

#include <common/common.hh>
#include <stack>

#include <cuddInt.h>
#include <dd/dd.hh>

namespace dd {

    typedef enum {
        DD_WALK_LHS,
        DD_WALK_RHS,
        DD_WALK_NODE,
    } dd_entry_point;

    // reserved for ADD walkers
    struct add_activation_record {
        dd_entry_point pc;
        const DdNode* node;

        add_activation_record(const DdNode* dd)
            : pc(DD_WALK_LHS)
            , node(dd)
        {}
    };
    typedef std::stack<struct add_activation_record> add_walker_stack;

    class DDWalkerException: public Exception {
    public:
        virtual const char* what() const throw() = 0;
    };

    class ADDWalker {
    public:
        ADDWalker();
        virtual ~ADDWalker();

        virtual ADDWalker& operator()(ADD dd);

    protected:
        virtual void walk();

        virtual bool condition(const DdNode* node) = 0;
        virtual void action(const DdNode* node) = 0;

        virtual void pre_hook() = 0;
        virtual void post_hook() = 0;

        /* explicit recursion stack */
        add_walker_stack f_recursion_stack;
    };

}; // namespace dd

#endif

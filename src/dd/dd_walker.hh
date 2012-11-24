/**
 *  @file dd_walker.hh
 *  @brief DD algorithm-unaware walk pattern implementation
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

#ifndef DD_WALKER_H
#define DD_WALKER_H

#include <common.hh>
#include <cudd_mgr.hh>
#include <cuddInt.h>

// enums in C++ are non-extensible, thus we have to keep all possible
// values together in one place. (for DDs things are simpler)
typedef enum {
    DD_DEFAULT,
    DD_RETURN,
    DD_ELSE,
} dd_entry_point;

// reserved for walkers
struct dd_activation_record {
    dd_entry_point pc;
    const DdNode *node;

    dd_activation_record(const DdNode *n)
        : pc(DD_DEFAULT)
        , node(n)
    {}
};

typedef stack<struct dd_activation_record> dd_walker_stack;

class DDWalkerException : public Exception
{
public:
    virtual const char* what() const throw() =0;
};

/* Two kinds of DD walkers are defined: leaf and node walkers,
   designed to process leaf nodes and internal nodes of given DD
   respectively. */

// base class (generic walker)
class DDWalker {
public:
    DDWalker(CuddMgr& owner);
    virtual ~DDWalker();

    virtual DDWalker& operator() (ADD dd);

protected:
    virtual void walk() =0;
    virtual void pre_hook() =0;
    virtual void post_hook() =0;

    virtual bool condition(const DdNode *node) =0;
    virtual void action   (const DdNode *node) =0;

    /* explicit recursion stack */
    dd_walker_stack f_recursion_stack;

    /* the CUDD instance */
    CuddMgr& f_owner;
};

class DDLeafWalker : public DDWalker {
public:
    DDLeafWalker(CuddMgr& owner);
    virtual ~DDLeafWalker();

protected:
    virtual void walk();
    virtual void pre_hook();
    virtual void post_hook();

    /* Holds the value for relevant literals when action is called */
    char *f_data; /* try to limit memory waste for caching */
};

class DDNodeWalker : public DDWalker {
public:
    DDNodeWalker(CuddMgr& owner);
    virtual ~DDNodeWalker();

protected:
    virtual void walk();
    virtual void pre_hook();
    virtual void post_hook();
};


#endif

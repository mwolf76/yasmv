/**
 * @file analyzer.hh
 * @brief Expr analyzer
 *
 * This header file contains the declarations required by the
 * Expression analyzer class.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/

#ifndef EXPR_ANALYZER_H
#define EXPR_ANALYZER_H

#include <string>
#include <expr/walker/walker.hh>

#include <boost/unordered_map.hpp>

namespace expr {

class Analyzer : public ExprWalker {
public:
    Analyzer();
    ~Analyzer();

    void process(Expr_ptr expr);

    inline bool has_forward_time() const
    { return f_has_forward_time; }

    inline bool has_backward_time() const
    { return f_has_backward_time; }

protected:
    void pre_hook();
    void post_hook();

    // support for LTL ops
    LTL_HOOKS;

    // support for basic ops
    OP_HOOKS;

    void walk_instant(const Expr_ptr expr);
    void walk_leaf(const Expr_ptr expr);

private:
    bool f_has_forward_time;
    bool f_has_backward_time;
};

};

#endif /* EXPR_ANALYZER_H */

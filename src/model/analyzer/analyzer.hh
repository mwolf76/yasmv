/**
 * @file analyzer.hh
 * @brief Semantic analyzer
 *
 * This header file contains the declarations required to implement
 * the type checking of temporal logic expressions.
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

#ifndef ANALYZER_H
#define ANALYZER_H

#include <expr/walker/walker.hh>

#include <type/type.hh>
#include <type/type_mgr.hh>

#include <boost/unordered_map.hpp>

namespace model {

/* guard -> identifier map (first pass) */
typedef boost::unordered_map<expr::Expr_ptr, expr::Expr_ptr, utils::PtrHash, utils::PtrEq> DependencyTrackingMap;

/* identifier -> framing condition clause */
typedef boost::unordered_map<expr::Expr_ptr, expr::Expr_ptr, utils::PtrHash, utils::PtrEq> FramingConditionMap;

class ModelMgr;
typedef enum {
    ANALYZE_INIT,
    ANALYZE_INVAR,
    ANALYZE_TRANS,
    ANALYZE_DEFINE
} analyze_section_t ;

class Analyzer : public expr::ExprWalker {
public:
    Analyzer(ModelMgr& owner);
    ~Analyzer();

    // walker toplevel
    void process(expr::Expr_ptr expr, expr::Expr_ptr ctx, analyze_section_t section);

    inline ModelMgr& owner()
    { return f_owner; }

    // generates framing conditions, adds them in the module
    void generate_framing_conditions();

protected:
    void pre_hook();
    void post_hook();

    void pre_node_hook(expr::Expr_ptr expr);
    void post_node_hook(expr::Expr_ptr expr);

    LTL_HOOKS; OP_HOOKS;

    void walk_instant(const expr::Expr_ptr expr);
    void walk_leaf(const expr::Expr_ptr expr);

private:
    expr::ExprVector f_expr_stack;
    expr::ExprVector f_ctx_stack;

    // managers
    ModelMgr& f_owner;

    // the type of expr we're analyzing
    analyze_section_t f_section;

    DependencyTrackingMap f_dependency_tracking_map;

    // helpers
    bool mutually_exclusive(expr::Expr_ptr p, expr::Expr_ptr q);
};

};

#endif /* ANALYZER_H */

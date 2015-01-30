/*
 * @file dup_trace.cc
 * @brief Command-interpreter subsystem related classes and definitions.
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
 *  Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/
#include <cmd/commands/dup_trace.hh>

#include <expr/expr.hh>
#include <expr/expr_mgr.hh>

#include <witness/witness.hh>
#include <witness/witness_mgr.hh>

DupTrace::DupTrace(Interpreter& owner, Expr_ptr trace_id, Expr_ptr duplicate_id)
    : Command(owner)
    , f_trace_id(trace_id)
    , f_duplicate_id(duplicate_id)
{}

Variant DupTrace::operator()()
{
    assert(false); // tODO
#if 0
    ExprMgr& em
        (ExprMgr::INSTANCE());

    std::ostream &os
        (std::cout);

    Witness& w
        (WitnessMgr::INSTANCE().witness(f_trace_id->atom()));

    for (step_t time = w.first_time(); time <= w.last_time(); ++ time) {
        os << "-- @ " << 1 + time << std::endl;
        TimeFrame& tf = w[ time ];

        SymbIter symbs( ModelMgr::INSTANCE().model(), NULL );
        while (symbs.has_next()) {

            std::pair< Expr_ptr, Symbol_ptr > pair
                (symbs.next());
            Expr_ptr ctx
                (pair.first);
            Symbol_ptr symb
                (pair.second);
            Expr_ptr name
                (symb->name());
            Expr_ptr value
                (NULL);
            Expr_ptr full
                (em.make_dot( ctx, name));

            if (name -> atom()[0] == '@')
                continue;

            if (symb->is_variable())  {
                try {
                    value = tf.value(full);
                    os
                        << full << " = "
                        << value << std::endl;
                }
                catch (NoValue nv) {
                    // value = ExprMgr::INSTANCE().make_undef();
                }
            }
            else if (symb->is_define()) {
                Expr_ptr expr(symb->name());

                try {
                    value = WitnessMgr::INSTANCE().eval( w, ctx, expr, time);
                    os
                        << full  << " = "
                        << value << std::endl;
                }
                catch (NoValue nv) {
                    // value = ExprMgr::INSTANCE().make_undef();
                }
            }
            else
                continue;
        }

        os << std::endl;
    }

#endif
    return Variant("Ok");

}

DupTrace::~DupTrace()
{}


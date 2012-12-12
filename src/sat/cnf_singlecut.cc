/**
 *  @file sat.cc
 *  @brief SAT interface implementation
 *
 *  This module contains the interface for services that implement an
 *  CNF clauses generation in a form that is suitable for direct
 *  injection into the SAT solver.
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
#include <pool.hh>
#include <sat.hh>
#include <dd_walker.hh>

namespace Minisat {

    /* used only for CNF-ization */
    class TimedDD {
    public:
        TimedDD(YDD_ptr node, step_t time)
            : f_node(node)
            , f_time(time)
        {}

        TimedDD(const TimedDD& other)
            : f_node(other.node())
            , f_time(other.time())
        {}

        inline YDD_ptr node() const
        { return f_node; }

        inline step_t time() const
        { return f_time; }

    private:
        // The YDD node
        YDD_ptr f_node;

        // expression time (default is 0)
        step_t f_time;
    };

    struct TimedDDHash {
        inline long operator() (const TimedDD& k) const
        { return 0; } // TODO: hash function
    };

    struct TimedDDEq {
        inline bool operator() (const TimedDD& x, const TimedDD& y) const
        {
            return (x.node() == y.node() &&
                    x.time() == y.time());
        }
    };



    class CNFBuilderSingleCut : public YDDWalker {
    public:
        CNFBuilderSingleCut(SAT& sat, step_t time)
            : f_sat(sat)
            , f_time(time)
            , f_toplevel(NULL)
        {}

        ~CNFBuilderSingleCut()
        {}

        void pre_hook()
        {
            assert( 1 == f_recursion_stack.size());

            ydd_activation_record curr = f_recursion_stack.top();
            f_toplevel = const_cast<YDD_ptr>(curr.node);

            /* this has to be preallocated */
            group_t group = MAINGROUP;
            f_gl = f_sat.cnf_find_group_lit(group);
        }

        void post_hook()
        {
            // FIXME...
            group_t group = MAINGROUP;
            color_t color = BACKGROUND;

            /* build and push clause toplevel */
            vec<Lit> ps; ps.push(f_gl);

            assert (NULL != f_toplevel);

            /* assert toplevel fun */
            push1( color, find_cnf_var(f_toplevel), false);
        }

        bool condition(const YDD_ptr node)
        {
            assert(NULL != node);

            /* is a non constant, not visited node. */
            return ( !node->is_const() &&
                     f_seen.find(node) == f_seen.end());
        }

        /* push 1 var clause */
        inline void push1( color_t color, Var x, bool px )
        {
            vec<Lit> ps;

            group_t group = MAINGROUP;
            ps.push(f_sat.cnf_find_group_lit(group));

            ps.push( mkLit( x, px ));

            // DRIVEL << ps << endl;
            f_sat.f_solver.addClause_(ps, color);
        }

        /* push 2 vars clause */
        inline void push2( color_t color, Var x, bool px, Var y, bool py )
        {
            vec<Lit> ps;
            group_t group = MAINGROUP;
            ps.push(f_sat.cnf_find_group_lit(group));

            ps.push( mkLit( x, px ));
            ps.push( mkLit( y, py ));

            // DRIVEL << ps << endl;
            f_sat.f_solver.addClause_(ps, color);
        }

        /* push 3 vars clause */
        inline void push3( color_t color, Var x, bool px, Var y, bool py, Var w, bool pw )
        {
            vec<Lit> ps;

            group_t group = MAINGROUP;
            ps.push(f_sat.cnf_find_group_lit(group));

            ps.push( mkLit( x, px ));
            ps.push( mkLit( y, py ));
            ps.push( mkLit( w, pw ));

            // DRIVEL << ps << endl;
            f_sat.f_solver.addClause_(ps, color);
        }

        void action(YDD_ptr node)
        {
            /* don't process leaves */
            assert (NULL != node && ! node->is_const());
            f_seen.insert(node); /* mark as visited */

            // FIXME...
            group_t group = MAINGROUP;
            color_t color = BACKGROUND;

            // Lit gl = f_sat.cnf_find_group_lit(group);

            Var f = find_cnf_var(node);
            Var v = find_dd_var(node);

            /* both T, E are consts */
            if (node->Then()->is_const() &&
                node->Else()->is_const()) {

                if (node->Then()->is_true() &&
                    node->Else()->is_false()) {

                    /* v <-> f */
                    push2( color, f, false, v, true );
                    push2( color, f, true, v, false );
                }

                else if (node->Then()->is_false() &&
                         node->Else()->is_true()) {
                    /* !( v <-> f ) */
                    push2( color, f, false, v, false );
                    push2( color, f, true, v, true );
                }

                else assert (false); /* unreachable */
            }

            /* T is const, E is not */
            else if (node->Then()->is_const() &&
                     ! node->Else()->is_const()) {

                Var e = find_cnf_var(node->Else());
                if (node->Then()->is_true()) {

                    /* ( f | !v ) ; */
                    push2( color, f, false, v, true);

                    /* ( f | !e ) */
                    push2( color, f, false, e, true);

                    /* (!f |  v |  e) */
                    push3( color, f, true , v, false, e, false);
                }

                else {
                    /* ( !f | !v ) ; */
                    push2( color, f, true, v, true);

                    /* ( !f | e ) */
                    push2( color, f, true, e, false);

                    /* (f |  v |  !e) */
                    push3( color, f, false , v, false, e, true);
                }
            }

            /* E is const, T is not */
            else if (node->Else()->is_const() &&
                     ! node->Then()->is_const()) {

                Var t = find_cnf_var(node->Then());

                if (node->Else()->is_true()) {

                    /* ( f | v ) ; */
                    push2( color, f, false, v, false);

                    /* ( f | !t ) */
                    push2( color, f, false, t, true);

                    /* (!f |  !v |  t) */
                    push3( color, f, true , v, true, t, false);
                }

                else {
                    /* ( !f | v ) ; */
                    push2( color, f, true, v, false);

                    /* ( !f | t ) */
                    push2( color, f, true, t, false);

                    /* (f |  !v |  !t) */
                    push3( color, f, false , v, true, t, true);
                }
            }

            /* both T, E non consts */
            else {
                assert (! node->Then()->is_const());
                Var t = find_cnf_var(node->Then());

                assert (! node->Else()->is_const());
                Var e = find_cnf_var(node->Else());

                /* !f, v, e */
                push3( color, f, true, v, false, e, false);

                /* !f, !v, t  */
                push3( color, f, true, v, true, t, false );

                /* f, v, !e */
                push3( color, f, false, v, false, e, true );

                /* f, !v, !t */
                push3( color, f, false, v, true, t, true );
            }
        }

    private:
        SAT& f_sat;
        unordered_set<YDD_ptr> f_seen;

        Lit f_gl;
        typedef unordered_map<TimedDD, Var, TimedDDHash, TimedDDEq> ActivationMap;
        ActivationMap f_activation_map;

        Var find_dd_var(const YDD_ptr node)
        {
            assert (NULL != node);

            UCBI ucbi = f_sat.find_ucbi(node->index());
            TCBI tcbi (ucbi.ctx(), ucbi.expr(), ucbi.time(), ucbi.bitno(), f_time);
            return f_sat.f_mapper.var(tcbi);
        }

        Var find_cnf_var(const YDD_ptr node)
        {
            Var res;

            assert (NULL != node);
            TimedDD timed_node (const_cast<YDD_ptr> (node), f_time);

            const ActivationMap::iterator eye = \
                f_activation_map.find( timed_node );

            if (f_activation_map.end() == eye) {
                res = f_sat.new_sat_var();

                /* Insert into activation map */
                f_activation_map [ timed_node ] = res;
            }

            else {
                res = (*eye).second;
            }

            return res;
        }

        YDD_ptr f_toplevel;
        step_t f_time;
    };

    void SAT::cnf_push_single_cut(Term phi, step_t time, const group_t group, const color_t color)
    {
        CNFBuilderSingleCut builder(*this, time);
        builder(phi);
    }

};

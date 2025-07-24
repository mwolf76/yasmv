/**
 * @file sat/cnf.cc
 * @brief Engine interface implementation, CNFization algorithm
 * implementation.
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
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA
 *
 **/

#include <dd/dd_walker.hh>
#include <sat/sat.hh>

// #define DEBUG_CNF_LITERALS

namespace sat {

    class CNFBuilder: public dd::ADDWalker {
    public:
        CNFBuilder(Engine& sat, step_t time,
                   group_t group = MAINGROUP)
            : f_sat(sat)
            , f_toplevel(NULL)
            , f_time(time)
            , f_group(group)
        {}

        ~CNFBuilder()
        {}

        void pre_hook()
        {
            assert(1 == f_recursion_stack.size());

            dd::add_activation_record curr { f_recursion_stack.top() };
            f_toplevel = const_cast<DdNode*>(curr.node);
        }

        void post_hook()
        {
            /* build and push clause toplevel */
            assert(NULL != f_toplevel);

            /* assert toplevel fun */
            push1(f_sat.find_cnf_var(f_toplevel, f_time), false);
        }

        inline bool is_toplevel() const
        {
            return 1 == f_recursion_stack.size();
        }

        inline bool is_unseen(const DdNode* node) const
        {
            return f_seen.end() == f_seen.find(const_cast<DdNode*>(node));
        }

        inline void mark(const DdNode* node)
        {
            f_seen.insert(const_cast<DdNode*>(node));
        }

        bool condition(const DdNode* node)
        {
            assert(NULL != node);
            return cuddIsConstant(node)

                       /* toplevel leaf or ... */
                       ? is_toplevel()

                       /* is a non-constant, yet unseen node. */
                       : is_unseen(node);
        }

        void action(const DdNode* node)
        {
            if (cuddIsConstant(node)) {
                assert(is_toplevel());

                if (!Cudd_V(node)) {
                    push1(0, true); /* make formula unsatisfiable */
                }
            } else {
                mark(node);

                Var f { f_sat.find_cnf_var(node, f_time) };
                Var v { f_sat.find_dd_var(node, f_time) };

                /* both T, E are consts */
                if (cuddIsConstant(cuddT(node)) &&
                    cuddIsConstant(cuddE(node))) {

                    /* positive polarity (T ^ !E) */
                    if (0 != cuddV(cuddT(node)) &&
                        0 == cuddV(cuddE(node))) {

                        /* v <-> f */
                        push2(f, false, v, true);
                        push2(f, true, v, false);
                    }

                    /* negative polarity (!T ^ E) */
                    else if (0 == cuddV(cuddT(node)) &&
                             0 != cuddV(cuddE(node))) {

                        /* !( v <-> f ) */
                        push2(f, false, v, false);
                        push2(f, true, v, true);
                    }

                    else {
                        assert(false); /* unreachable */
                    }
                }

                /* T is const, E is not */
                else if (cuddIsConstant(cuddT(node)) &&
                         !cuddIsConstant(cuddE(node))) {

                    Var e { f_sat.find_cnf_var(cuddE(node), f_time) };

                    /* Positive polarity (T) */
                    if (0 != cuddV(cuddT(node))) {

                        /* ( f | !v ) */
                        push2(f, false, v, true);

                        /* ( f | !e ) */
                        push2(f, false, e, true);

                        /* (!f |  v |  e) */
                        push3(f, true, v, false, e, false);
                    }

                    /* Negative polarity (!T) */
                    else {
                        /* ( !f | !v ) ; */
                        push2(f, true, v, true);

                        /* ( !f | e ) */
                        push2(f, true, e, false);

                        /* (f |  v |  !e) */
                        push3(f, false, v, false, e, true);
                    }
                }

                /* E is const, T is not */
                else if (cuddIsConstant(cuddE(node)) &&
                         !cuddIsConstant(cuddT(node))) {

                    Var t { f_sat.find_cnf_var(cuddT(node), f_time) };

                    /* Positive polarity (E) */
                    if (0 != cuddV(cuddE(node))) {

                        /* ( f | v ) */
                        push2(f, false, v, false);

                        /* ( f | !t ) */
                        push2(f, false, t, true);

                        /* (!f |  !v |  t) */
                        push3(f, true, v, true, t, false);
                    }

                    /* Negative polarity */
                    else {
                        /* ( !f | v ) */
                        push2(f, true, v, false);

                        /* ( !f | t ) */
                        push2(f, true, t, false);

                        /* (f |  !v |  !t) */
                        push3(f, false, v, true, t, true);
                    }
                }

                /* General case: both T, E non const */
                else {
                    assert(!cuddIsConstant(cuddT(node)));
                    Var t { f_sat.find_cnf_var(cuddT(node), f_time) };

                    assert(!cuddIsConstant(cuddE(node)));
                    Var e { f_sat.find_cnf_var(cuddE(node), f_time) };

                    /* !f, v, e */
                    push3(f, true, v, false, e, false);

                    /* !f, !v, t  */
                    push3(f, true, v, true, t, false);

                    /* f, v, !e */
                    push3(f, false, v, false, e, true);

                    /* f, !v, !t */
                    push3(f, false, v, true, t, true);
                }
            }
        } /* action() */

    private:
        Engine& f_sat;
        boost::unordered_set<DdNode*> f_seen;

        DdNode* f_toplevel;

        step_t f_time;
        group_t f_group;

        /* push 1 var clause */
        inline void push1(Var x, bool px)
        {
            vec<Lit> ps;

            if (MAINGROUP != f_group) {
                ps.push(mkLit(f_group, true));
            }

            ps.push(mkLit(x, px));

#ifdef DEBUG_CNF_LITERALS
            DRIVEL
                << ps
                << std::endl;
#endif

            f_sat.add_clause(ps);
        }

        /* push 2 vars clause */
        inline void push2(Var x, bool px, Var y, bool py)
        {
            vec<Lit> ps;

            if (MAINGROUP != f_group) {
                ps.push(mkLit(f_group, true));
            }

            ps.push(mkLit(x, px));
            ps.push(mkLit(y, py));

#ifdef DEBUG_CNF_LITERALS
            DRIVEL
                << ps
                << std::endl;
#endif

            f_sat.add_clause(ps);
        }

        /* push 3 vars clause */
        inline void push3(Var x, bool px, Var y, bool py, Var w, bool pw)
        {
            vec<Lit> ps;

            if (MAINGROUP != f_group) {
                ps.push(mkLit(f_group, true));
            }

            ps.push(mkLit(x, px));
            ps.push(mkLit(y, py));
            ps.push(mkLit(w, pw));

#ifdef DEBUG_CNF_LITERALS
            DRIVEL
                << ps
                << std::endl;
#endif

            f_sat.add_clause(ps);
        }
    };

    void Engine::cnf_push(ADD add, step_t time, const group_t group)
    {
        CNFBuilder worker { *this, time, group };

        worker(add);

#ifdef DEBUG_CNF_LITERALS
        DRIVEL
            << "------------------------------------------------------------"
            << std::endl;
#endif
    }

}; // namespace sat

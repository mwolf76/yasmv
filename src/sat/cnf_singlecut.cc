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

    class CNFBuilderSingleCut : public DDNodeWalker {
    public:
        CNFBuilderSingleCut(CuddMgr& mgr, SAT& sat)
            : DDNodeWalker(mgr)
            , f_sat(sat)
            , f_toplevel(NULL)
        {}

        ~CNFBuilderSingleCut()
        {}


        bool condition(const DdNode *node)
        {
            /* is a non constant, not visited node. */
            return ( !cuddIsConstant(node) &&
                     f_seen.find(node) == f_seen.end());
        }

        void pre_hook()
        {
            assert( 1 == f_recursion_stack.size());

            dd_activation_record curr = f_recursion_stack.top();
            f_toplevel = const_cast<DdNode *>(curr.node);

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

        void action(const DdNode *node)
        {
            /* don't process leaves */
            assert (!Cudd_IsConstant(node));
            f_seen.insert(node); /* mark as visited */

            // FIXME...
            group_t group = MAINGROUP;
            color_t color = BACKGROUND;

            // Lit gl = f_sat.cnf_find_group_lit(group);

            Var f = find_cnf_var(node);
            Var v = find_dd_var(node);

            /* both T, E are consts */
            if (cuddIsConstant( cuddT(node)) &&
                cuddIsConstant( cuddE(node))) {

                if (0 != cuddV(cuddT(node)) &&
                    0 == cuddV(cuddE(node))) {

                    /* v <-> f */
                    push2( color, f, false, v, true );
                    push2( color, f, true, v, false );
                }

                else if (0 == cuddV(cuddT(node)) &&
                         0 != cuddV(cuddE(node))) {
                    /* !( v <-> f ) */
                    push2( color, f, false, v, false );
                    push2( color, f, true, v, true );
                }

                else assert (false); /* unreachable */
            }

            /* T is const, E is not */
            else if (cuddIsConstant( cuddT(node)) &&
                     !cuddIsConstant( cuddE(node))) {

                Var e = find_cnf_var(cuddE(node));

                if (0 != cuddV(cuddT(node))) {

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
            else if (cuddIsConstant( cuddE(node)) &&
                     !cuddIsConstant( cuddT(node))) {

                Var t = find_cnf_var(cuddT(node));

                if (0 != cuddV(cuddE(node))) {

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
                assert (! Cudd_IsConstant(cuddT(node)));
                Var t = find_cnf_var(cuddT(node));

                assert (! Cudd_IsConstant(cuddE(node)));
                Var e = find_cnf_var(cuddE(node));

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
        unordered_set<const DdNode *> f_seen;

        Lit f_gl;

        typedef unordered_map<DdNode *, Var, PtrHash, PtrEq> ActivationMap;
        ActivationMap f_activation_map;

        Var find_dd_var(const DdNode *node)
        {
            assert (! Cudd_IsComplement(node));
            return f_sat.cnf_find_index_var(node->index);
        }

        Var find_cnf_var(const DdNode *node)
        {
            Var res;

            assert (! Cudd_IsComplement(node));
            DdNode *node_ = const_cast<DdNode *>(node);

            const ActivationMap::iterator eye = \
                f_activation_map.find( node_ );

            if (f_activation_map.end() == eye) {
                res = f_sat.f_solver.newVar();
                // DRIVEL << "Adding VAR " << res
                //        << " for CNF of DD (index = " << node->index << ")"
                //        << endl;

                /* insert into activation map */
                f_activation_map [ node_ ] = res;
            }

            else {
                res = (*eye).second;
            }

            return res;
        }

        DdNode* f_toplevel;
    };

    void SAT::cnf_push_single_cut(Term phi, const group_t group, const color_t color)
    { CNFBuilderSingleCut builder(CuddMgr::INSTANCE(), *this); builder(phi); }

};

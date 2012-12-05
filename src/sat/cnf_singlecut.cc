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
        {}

        ~CNFBuilderSingleCut()
        {}


        bool condition(const DdNode *node)
        {
            /* not visited */
            return (f_seen.find(node) == f_seen.end());
        }

        void pre_hook()
        {
            assert( 1 == f_recursion_stack.size());

            dd_activation_record curr = f_recursion_stack.top();
            f_recursion_stack.pop();

            ADD tmp(f_owner.dd(), const_cast<DdNode *>(curr.node));
            tmp.PrintMinterm();

            /* TODO: Benchmark this... (!) */

            /* (preprocessing) convert 0-1 ADD to BDD */
            BDD aux = tmp.BddPattern();
            aux.PrintMinterm();

            f_toplevel = aux.getNode();
            f_recursion_stack.push(f_toplevel);

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

            // TODO : messy...
            ps.push( mkLit( find_cnf_var( Cudd_Regular(f_toplevel)),
                            false));

            DRIVEL << ps << endl;
            f_sat.f_solver.addClause_(ps, color);
        }

        /* push 1 var clause */
        inline void push1( color_t color, Var x, bool px )
        {
            vec<Lit> ps;

            group_t group = MAINGROUP;
            ps.push(f_sat.cnf_find_group_lit(group));

            ps.push( mkLit( x, px ));

            DRIVEL << ps << endl;
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

            DRIVEL << ps << endl;
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

            DRIVEL << ps << endl;
            f_sat.f_solver.addClause_(ps, color);
        }

        void action(const DdNode *node)
        {
            DdNode *N = Cudd_Regular(node);
            bool Ncmpl = Cudd_IsComplement(node);

            /* mark as visited (REVIEW: regular node?) */
            f_seen.insert(N);

            // FIXME...
            group_t group = MAINGROUP;
            color_t color = BACKGROUND;

            Lit gl = f_sat.cnf_find_group_lit(group);

            DdNode *T = Ncmpl
                ? Cudd_Complement( cuddT(N))
                : cuddT(N)
                ;
            DdNode *Treg = Cudd_Regular(T);

            DdNode *E = Ncmpl
                ? Cudd_Complement( cuddE(N))
                : cuddE(N)
                ;
            DdNode *Ereg = Cudd_Regular(E);

            /* 0. Both children are const, do nothing. */
            if (cuddIsConstant(Treg) &&
                cuddIsConstant(Ereg))
                return;

            Var f = find_dd_var(const_cast<DdNode *>(N));
            Var v = find_cnf_var(const_cast<DdNode *>(N));

            /* 1. Only T is const */
            if (cuddIsConstant(Treg) &&
                !cuddIsConstant(Ereg)) {

                Var e =
                    cuddIsConstant(Cudd_Regular(cuddT(Ereg))) &&
                    cuddIsConstant(Cudd_Regular(cuddE(Ereg)))

                    ? find_dd_var(Ereg)
                    : find_cnf_var(Ereg)
                    ;

                bool e_cmpl = Cudd_IsComplement(E);

                if (Cudd_IsComplement(T)) {
                    /* ( f | !v ) ; */
                    push2( color, f, false, v,  true);

                    /* ( f | !e ) */
                    push2( color, f, false, e, ! e_cmpl);

                    /* (!f |  v |  e) */
                    push3( color, f, true , v, false, e, e_cmpl);
                }

                else {
                    /* (!f | !v ) ; */
                    push2( color, f,  true, v,  true );

                    /* (!f |  e)  */
                    push2( color, f,  true, e, e_cmpl);

                    /* ( f |  v | !e) */
                    push3( color, f, false, v, false, e, ! e_cmpl);
                }

                return;
            }

            /* 2. Only E is const */
            else if (!cuddIsConstant(Treg) &&
                     cuddIsConstant(Ereg)) {

                Var t =
                    cuddIsConstant(Cudd_Regular(cuddT(Treg))) &&
                    cuddIsConstant(Cudd_Regular(cuddE(Treg)))

                    ? find_dd_var(T)
                    : find_cnf_var(T);

                bool t_cmpl = Cudd_IsComplement(T);

                if (Cudd_IsComplement(E)) {
                    /* ( f |  v ) */
                    push2( color, f,  false, v, false);

                    /* ( f | !t ) */
                    push2( color, f,  false, t, ! t_cmpl);

                    /* (!f | !v |  t) */
                    push3( color, f, true, v, true, t, t_cmpl);
                }

                else {
                    /* (!f |  v ) */
                    push2( color, f, true,  v,  false);

                    /* (!f |  t ) ; */
                    push2( color, f, true,  t,  t_cmpl);

                    /* ( f | !v | !t) */
                    push3( color, f, false, v,  true, t, ! t_cmpl );
                }

                return;
            }

            // else
            {
                /* obviously */
                assert (! cuddIsConstant(Treg));
                assert (! cuddIsConstant(Ereg));

                Var t =
                    cuddIsConstant(Cudd_Regular(cuddT(Treg))) &&
                    cuddIsConstant(Cudd_Regular(cuddE(Treg)))

                    ? find_dd_var(T)
                    : find_cnf_var(T);

                bool t_cmpl = Cudd_IsComplement(T);

                Var e =
                    cuddIsConstant(Cudd_Regular(cuddT(Ereg))) &&
                    cuddIsConstant(Cudd_Regular(cuddE(Ereg)))

                    ? find_dd_var(E)
                    : find_cnf_var(E);

                bool e_cmpl = Cudd_IsComplement(E);

                /* v, !f,  e */
                push3( color, v, false, f,  true, e, e_cmpl );

                /* v,  f, !e  */
                push3( color, v, false, f, false, e, ! e_cmpl );

                /* !v, !f, t */
                push3( color, v,  true, f,  true, t, t_cmpl );

                /* !v, f, !t */
                push3( color, v,  true, f, false, t, ! t_cmpl );

                return;
            }

            assert ( false ); /* unreachable */
        }

    private:
        SAT& f_sat;
        unordered_set<const DdNode *> f_seen;

        Lit f_gl;

        typedef unordered_map<DdNode *, Var, PtrHash, PtrEq> ActivationMap;
        ActivationMap f_activation_map;

        Var find_dd_var(DdNode *node)
        {
            assert (! Cudd_IsComplement(node));
            return f_sat.cnf_find_index_var(node->index);
        }

        Var find_cnf_var(DdNode *node)
        {
            assert (! Cudd_IsComplement(node));

            Var res;
            const ActivationMap::iterator eye = f_activation_map.find( node );

            if (f_activation_map.end() == eye) {
                res = f_sat.f_solver.newVar();
                DRIVEL << "Adding VAR " << res
                       << " for CNF of DD (index = " << node->index << ")"
                       << endl;

                /* insert into activation map */
                f_activation_map [ node ] = res;
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

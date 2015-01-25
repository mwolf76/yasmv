/**
 *  @file cnf_inject.cc
 *  @brief SAT implementation - CNF injection module
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
#include <expr/pool.hh>
#include <sat/sat.hh>

#include <dd/dd_walker.hh>

#include <micro/micro_mgr.hh>

class CNFMicrocodeInjector {
public:
    CNFMicrocodeInjector(Engine& sat, step_t time, group_t group = MAINGROUP)
        : f_sat(sat)
        , f_time(time)
        , f_group(group)
    {}

    ~CNFMicrocodeInjector()
    {}

    inline void operator() (const MicroDescriptor& md)
    {
        MicroMgr& mm
            (MicroMgr::INSTANCE());

        OpTriple triple
            (md.triple());
        MicroLoader& loader
            (mm.require(triple));

        inject(md, loader.microcode());
    }

private:
    void inject(const MicroDescriptor& md,
                const LitsVector& microcode);

    Engine& f_sat;
    step_t f_time;
    group_t f_group;
};

void CNFMicrocodeInjector::inject(const MicroDescriptor& md,
                                  const LitsVector& microcode)
{
    DEBUG
        << const_cast<MicroDescriptor&> (md)
        << std::endl;

    /* true */
    const Var alpha
        (0);

    /* local refs */
    const DDVector& z
        (md.z());
    const DDVector& x
        (md.x());
    const DDVector& y
        (md.y());

    int width
        (triple_width(md.triple()));

    // keep each injection in a separate cnf space
    f_sat.clear_cnf_map();

    // foreach clause in microcode data...
    LitsVector::const_iterator i;
    for (i = microcode.begin(); microcode.end() != i; ++ i) {

        const Lits& clause
            (*i);

        Minisat::vec<Lit> ps;
        ps.push( mkLit( f_group, true));

        // for each literal in clause, determine whether associated
        // var belongs to z, x, y or is a cnf var. For each group in
        // (z, x, y) fetch appropriate dd var from the registry. CNF
        // vars are kept distinct among distinct injections.
        Lits::const_iterator j;
        for (j = clause.begin(); clause.end() != j; ++ j)  {
            Lit lit
                (*j);

            Var lit_var
                (Minisat::var(lit));
            int lit_sign
                (Minisat::sign(lit));

            Var tgt_var;

            /* z? */
            if (lit_var < width) {
                int ndx
                    (lit_var);
                assert(0 <= ndx && ndx < width);

                const DdNode* node(NULL);
                if (md.is_relational()) {
                    assert(!ndx);
                    node = z[0].getNode();
                }
                else
                    node = z[ width - ndx - 1].getNode();

                if (! Cudd_IsConstant(node)) {
                    tgt_var = f_sat.find_dd_var(node, f_time);
                    ps.push( mkLit( tgt_var, lit_sign));
                }
                // const DD support
                else {
                    value_t value
                        (cuddV(node));
                    assert( value < 2); // 0 or 1
                    ps.push( mkLit( alpha, value ? lit_sign : ! lit_sign));
                }
            }
            /* x? */
            else if (width <= lit_var && lit_var < 2 * width) {
                int ndx
                    (lit_var - width);
                assert(0 <= ndx && ndx < width);

                const DdNode* node
                    (x[ width - ndx - 1].getNode());

                if (! Cudd_IsConstant(node)) {
                    tgt_var = f_sat.find_dd_var(node, f_time);
                    ps.push( mkLit( tgt_var, lit_sign));
                }
                // const DD support
                else {
                    value_t value
                        (cuddV(node));
                    assert( value < 2); // 0 or 1

                    ps.push( mkLit( alpha, value ? lit_sign : ! lit_sign));
                }
            }
            /* y? */
            else if (2 * width <= lit_var && lit_var < 3 * width) {
                int ndx
                    (lit_var - 2 * width);
                assert(0 <= ndx && ndx < width);

                const DdNode* node
                    (y[ width - ndx - 1].getNode());
                if (! Cudd_IsConstant(node)) {
                    tgt_var = f_sat.find_dd_var(node, f_time);
                    ps.push( mkLit( tgt_var, lit_sign));
                }
                // const DD support
                else {
                    value_t value
                        (cuddV(node));
                    assert( value < 2); // 0 or 1
                    ps.push( mkLit( alpha, value
                                    ? lit_sign :
                                    ! lit_sign));
                }
            }
            /* nope, it's a cnf var */
            else {
                int ndx
                    (lit_var - 3 * width);
                assert(0 <= ndx /* && ndx < width */);

                tgt_var = f_sat.rewrite_cnf_var(ndx, f_time);
                ps.push( mkLit( tgt_var, lit_sign));
            }

        } /* for (j = clause...) */

        f_sat.add_clause(ps);
    }
}

class CNFMuxcodeInjector {
public:
    CNFMuxcodeInjector(Engine& sat, step_t time, group_t group = MAINGROUP)
        : f_sat(sat)
        , f_time(time)
        , f_group(group)
    {}

    ~CNFMuxcodeInjector()
    {}

    inline void operator() (const MuxDescriptor& md)
    { inject(md); }

private:
    void inject(const MuxDescriptor& md);

    Engine& f_sat;
    step_t f_time;
    group_t f_group;
};

void CNFMuxcodeInjector::inject(const MuxDescriptor& md)
{
    DEBUG
        << const_cast<MuxDescriptor&> (md)
        << std::endl;

    /* true */
    const Var alpha
        (0);

    /* local refs */
    const DDVector& z
        (md.z());
    const ADD& aux
        (md.aux());
    const DDVector& x
        (md.x());
    const DDVector& y
        (md.y());

    /* allocate a fresh variable for ITE condition */
    Var act
        (f_sat.find_dd_var( aux.getNode(), f_time));

    /* ! a, Zi <-> Xi for all i */
    for (unsigned pol = 0; pol < 2; ++ pol) {

        for (unsigned i = 0; i < md.width(); ++ i) {
            Minisat::vec<Lit> ps;
            ps.push( mkLit( f_group, true));
            ps.push( mkLit( act, true));
            ps.push( mkLit( f_sat.find_dd_var( z[i].getNode(),
                                               f_time), !pol ));
            DdNode* xnode
                (x[i].getNode());

            ps.push( Cudd_IsConstant(xnode)
                     ? mkLit( alpha, Cudd_V(xnode) ? pol : ! pol)
                     : mkLit( f_sat.find_dd_var( x[i].getNode(), f_time), pol));

            f_sat.add_clause( ps );
        }
    }

    /* a, Zi <-> Yi for all i */
    for (unsigned pol = 0; pol < 2; ++ pol) {

        for (unsigned i = 0; i < md.width(); ++ i) {
            Minisat::vec<Lit> ps;
            ps.push( mkLit( f_group, true));
            ps.push( mkLit( act, false));
            ps.push( mkLit( f_sat.find_dd_var( z[i].getNode(),
                                               f_time), !pol ));
            DdNode* ynode
                (y[i].getNode());

            ps.push(Cudd_IsConstant(ynode)
                    ? mkLit( alpha, Cudd_V(ynode) ? pol : ! pol )
                    : mkLit( f_sat.find_dd_var( y[i].getNode(), f_time), pol));

            f_sat.add_clause( ps );
        }
    }
}

class CNFArrayMuxcodeInjector {
public:
    CNFArrayMuxcodeInjector(Engine& sat, step_t time, group_t group = MAINGROUP)
        : f_sat(sat)
        , f_time(time)
        , f_group(group)
    {}

    ~CNFArrayMuxcodeInjector()
    {}

    inline void operator() (const ArrayMuxDescriptor& md)
    { inject(md); }

private:
    void inject(const ArrayMuxDescriptor& md);

    Engine& f_sat;
    step_t f_time;
    group_t f_group;
};

void CNFArrayMuxcodeInjector::inject(const ArrayMuxDescriptor& md)
{
    DEBUG
        << const_cast<ArrayMuxDescriptor&> (md)
        << std::endl;

    /* true */
    const Var alpha
        (0);

    /* local refs */
    const DDVector& z
        (md.z());
    const DDVector& acts
        (md.acts());
    const DDVector& x
        (md.x());

    unsigned j
        (0);
    DDVector::const_iterator ai
        (acts.begin());
    while (j < md.elem_count()) {

        /* allocate a fresh variable for ITE condition */
        Var act
            (f_sat.find_dd_var((*ai).getNode(), f_time));

        /* ! a, Zi <-> Xi for all i */
        for (unsigned pol = 0; pol < 2; ++ pol) {

            for (unsigned i = 0; i < md.elem_width(); ++ i) {

                unsigned ndx
                    (i + j * md.elem_width());

                Minisat::vec<Lit> ps;
                ps.push( mkLit( f_group, true));
                ps.push( mkLit( act, true));
                ps.push( mkLit( f_sat.find_dd_var( z[ i ].getNode(),
                                                   f_time), !pol ));
                ps.push( mkLit( f_sat.find_dd_var( x[ ndx ].getNode(),
                                                   f_time), pol));

                f_sat.add_clause( ps );
            }
        }

        ++ j;
        ++ ai;
    }
}


// proxies
void Engine::cnf_inject_microcode(const MicroDescriptor& md, step_t time, const group_t group)
{
    CNFMicrocodeInjector worker
        (*this, time, group);

    worker(md);
}

void Engine::cnf_inject_muxcode(const MuxDescriptor& md, step_t time, const group_t group)
{
    CNFMuxcodeInjector worker
        (*this, time, group);

    worker(md);
}

void Engine::cnf_inject_amuxcode(const ArrayMuxDescriptor& md, step_t time, const group_t group)
{
    CNFArrayMuxcodeInjector worker
        (*this, time, group);

    worker(md);
}




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
#include <pool.hh>
#include <sat.hh>

#include <dd_walker.hh>
#include <micro_mgr.hh>

// comment following to disable insanely verbose CNF debug logging
#define DEBUG_CNF

class CNFMicrocodeInjector {
public:
    CNFMicrocodeInjector(SAT& sat, step_t time, group_t group = MAINGROUP)
        : f_sat(sat)
        , f_time(time)
        , f_group(group)
    {}

    ~CNFMicrocodeInjector()
    {}

    inline void operator() (const MicroDescriptor& md)
    {
        MicroMgr& mm(MicroMgr::INSTANCE());

        OpTriple triple (md.triple());
        MicroLoader& loader = mm.require(triple);
        inject(md, loader.microcode());
    }

private:
    void inject(const MicroDescriptor& md,
                const LitsVector& microcode);

    SAT& f_sat;
    step_t f_time;
    group_t f_group;
};

void CNFMicrocodeInjector::inject(const MicroDescriptor& md,
                                  const LitsVector& microcode)
{
    DEBUG
        << const_cast<MicroDescriptor&> (md)
        << endl;

    // local refs
    const DDVector& z(md.z());
    const DDVector& x(md.x());
    const DDVector& y(md.y());

    int width( triple_width(md.triple()));
    const Var alpha(0); // true

    // keep each injection in a separate cnf space
    f_sat.clear_cnf_map();

    // foreach clause in microcode...
    LitsVector::const_iterator i;
    for (i = microcode.begin(); microcode.end() != i; ++ i) {
        const Lits& clause (*i);

        Minisat::vec<Lit> ps;
        ps.push( mkLit( f_group, true));

        // for each literal in clause, determine whether associated
        // var belongs to z, x, y or is a cnf var. For each group in
        // (z, x, y) fetch appropriate dd var from the registry. CNF
        // vars are kept distinct among distinct injections.
        Lits::const_iterator j;
        for (j = clause.begin(); clause.end() != j; ++ j)  {
            Lit lit (*j);

            Var lit_var (Minisat::var(lit));
            int lit_sign(Minisat::sign(lit));
            Var tgt_var;

            /* z? */
            if (lit_var < width) {
                int ndx = lit_var;
                assert(0 <= ndx && ndx < width);

                const DdNode* node(NULL);
                if (md.is_relational()) {
                    assert(!ndx);
                    node = z[0].getNode();
                }
                else if (md.is_binary()) {
                    node = z[ width - ndx - 1].getNode();
                }
                else if (md.is_unary()) {
                    assert(false); // not supported
                }

                if (! Cudd_IsConstant(node)) {
                    tgt_var = f_sat.find_dd_var(node, f_time);
                    ps.push( mkLit( tgt_var, lit_sign));
                }
                // const DD support
                else {
                    value_t value = cuddV(node);
                    assert( value < 2); // 0 or 1
                    ps.push( mkLit( alpha, value ? lit_sign : ! lit_sign));
                }
            }
            /* x? */
            else if (width <= lit_var && lit_var < 2 * width) {
                int ndx = lit_var - width;
                assert(0 <= ndx && ndx < width);

                const DdNode* node(x[ width - ndx - 1].getNode());
                if (! Cudd_IsConstant(node)) {
                    tgt_var = f_sat.find_dd_var(node, f_time);
                    ps.push( mkLit( tgt_var, lit_sign));
                }
                // const DD support
                else {
                    value_t value = cuddV(node);
                    assert( value < 2); // 0 or 1
                    ps.push( mkLit( alpha, value ? lit_sign : ! lit_sign));
                }
            }
            /* y? */
            else if (2 * width <= lit_var && lit_var < 3 * width) {
                int ndx = lit_var - 2 * width;
                assert(0 <= ndx && ndx < width);

                const DdNode* node(y[ width - ndx - 1].getNode());
                if (! Cudd_IsConstant(node)) {
                    tgt_var = f_sat.find_dd_var(node, f_time);
                    ps.push( mkLit( tgt_var, lit_sign));
                }
                // const DD support
                else {
                    value_t value = cuddV(node);
                    assert( value < 2); // 0 or 1
                    ps.push( mkLit( alpha, value ? lit_sign : ! lit_sign));
                }
            }
            /* cnf var */
            else {
                int ndx = lit_var - 3 * width;
                assert(0 <= ndx /* && ndx < width */);

                tgt_var = f_sat.rewrite_cnf_var(ndx, f_time);
                ps.push( mkLit( tgt_var, lit_sign));
            }

        } /* for (j = clause...) */

#ifdef DEBUG_CNF
        DRIVEL << ps << endl;
#endif
        f_sat.add_clause(ps);
    }
}

class CNFMuxcodeInjector {
public:
    CNFMuxcodeInjector(SAT& sat, step_t time, group_t group = MAINGROUP)
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

    SAT& f_sat;
    step_t f_time;
    group_t f_group;
};

void CNFMuxcodeInjector::inject(const MuxDescriptor& md)
{
    DEBUG
        << const_cast<MuxDescriptor&> (md)
        << endl;

    // local refs
    const DDVector& z(md.z());
    const ADD& cnd(md.cnd());
    const DDVector& x(md.x());
    const DDVector& y(md.y());

    { /* !a ( Zi <-> Xi for all i ) */

        for (unsigned pol = 0; pol < 2; ++ pol) {

            for (unsigned i = 0; i < md.width(); ++ i) {
                Minisat::vec<Lit> ps;
                ps.push( mkLit( f_group, true));

                const DdNode* node(cnd.getNode());
                if (! Cudd_IsConstant(node)) {
                    Var tgt_var = f_sat.find_dd_var(node, f_time);
                    ps.push( mkLit( tgt_var, true));
                }
                else assert(false);
                ps.push( mkLit( f_sat.find_dd_var( z[i].getNode(), ! pol ? true : false )));
                ps.push( mkLit( f_sat.find_dd_var( x[i].getNode(),   pol ? true : false)));
            }
        }
    }

    { /* a ( Zi <-> Yi for all i */
        for (unsigned pol = 0; pol < 2; ++ pol) {

            for (unsigned i = 0; i < md.width(); ++ i) {
                Minisat::vec<Lit> ps;
                ps.push( mkLit( f_group, true));

                const DdNode* node(cnd.getNode());
                if (! Cudd_IsConstant(node)) {
                    Var tgt_var = f_sat.find_dd_var(node, f_time);
                    ps.push( mkLit( tgt_var, false));
                }
                else assert(false);
                ps.push( mkLit( f_sat.find_dd_var( z[i].getNode(), ! pol ? true : false )));
                ps.push( mkLit( f_sat.find_dd_var( y[i].getNode(),   pol ? true : false)));
            }
        }
    }
}

// proxy
void SAT::cnf_inject_microcode(const MicroDescriptor& md, step_t time, const group_t group)
{
    CNFMicrocodeInjector worker(*this, time, group);
    worker(md);
}

// proxy
void SAT::cnf_inject_muxcode(const MuxDescriptor& md, step_t time, const group_t group)
{
    CNFMuxcodeInjector worker(*this, time, group);
    worker(md);
}


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
    // local refs
    const DDVector& z(md.z());
    const DDVector& x(md.x());
    const DDVector& y(md.y());
    int width(md.width());

    // foreach clause in microcode...
    LitsVector::const_iterator i;
    for (i = microcode.begin(); microcode.end() != i; ++ i) {
        const Lits& clause (*i);
        Lits ps;

        // for each literal in clause, determine whether associated
        // var belongs to z, x, y or is a cnf var. For each group in
        // (z, x, y) fetch appropriate dd var from the registry. CNF
        // vars are kept distinct among distinc injections.
        Lits::const_iterator j;
        for (j = clause.begin(); clause.end() != j; ++ j)  {
            Lit lit (*j);

            Var lit_var (Minisat::var(lit));
            int lit_sign(Minisat::sign(lit));
            Var tgt_var;

            /* z? */
            if (lit_var < (Var) width) {
                const DdNode* node(z[ lit_var ].getNode());
                tgt_var = f_sat.find_dd_var(node, f_time);
            }
            /* x? */
            else if (width <= lit_var && lit_var < 2 * width) {
                const DdNode* node(x[ lit_var - md.width() ].getNode());
                tgt_var = f_sat.find_dd_var(node, f_time);
            }
            /* y? */
            else if (2 * width <= lit_var && lit_var < 3 * width) {
                const DdNode* node(y[ lit_var - 2 * md.width() ].getNode());
                tgt_var = f_sat.find_dd_var(node, f_time);
            }
            /* cnf var */
            else {
                tgt_var = f_sat.find_cnf_var( lit_var - 3 * md.width(), f_time);
            }
            ps.push_back( mkLit( tgt_var, lit_sign));
        }
    }
}

// proxy
void SAT::cnf_inject_microcode(const MicroDescriptor& md, step_t time, const group_t group)
{
    CNFMicrocodeInjector worker(*this, time, group);
    worker(md);
}

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

    inline void operator() (MicroDescriptor& md)
    { inject( MicroMgr::INSTANCE().require(md.triple()).microcode()); }

private:
    void inject(const LitsVector& microcode);

    SAT& f_sat;
    step_t f_time;
    group_t f_group;
};


void CNFMicrocodeInjector::inject(const LitsVector& microcode)
{
    assert(false); // to be implemented
}

void SAT::cnf_inject_microcode(MicroDescriptor md, step_t time, const group_t group)
{
    CNFMicrocodeInjector worker(*this, time, group);
    worker(md);
}

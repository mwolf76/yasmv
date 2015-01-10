/**
 *  @file micro_mgr.hh
 *  @brief Microcode library - microcode manager module
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
#ifndef MICRO_MGR_H
#define MICRO_MGR_H

// the Minisat SAT solver
#include <minisat/core/Solver.h>
#include <minisat/core/SolverTypes.h>

#include <micro/micro.hh>
#include <micro/micro_loader.hh>

typedef class MicroMgr *MicroMgr_ptr;
class MicroMgr  {

public:
    static MicroMgr& INSTANCE() {
        if (! f_instance) {
            f_instance = new MicroMgr();
        }
        return (*f_instance);
    }

    MicroLoader& require(const OpTriple& triple);

    inline const MicroLoaderMap& loaders() const
    { return f_loaders; }

protected:
    MicroMgr();
    ~MicroMgr();

private:
    static MicroMgr_ptr f_instance;
    MicroLoaderMap f_loaders;
};

#endif

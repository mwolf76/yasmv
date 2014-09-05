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

#include <micro.hh>

typedef class MicroMgr *MicroMgr_ptr;

ostream& operator<<(ostream& os, OpTriple triple);

class MicroLoaderException : public Exception {
public:
    MicroLoaderException(const OpTriple& f_triple);
    ~MicroLoaderException() throw();

    const char* what() const throw();

private:
    OpTriple f_triple;
};

typedef class MicroLoader* MicroLoader_ptr;
class MicroLoader {
public:
    MicroLoader(const path& filepath);
    ~MicroLoader();

    inline const OpTriple& triple() const
    { return f_triple; }

    inline bool ready() const
    { return f_ready; }

    inline const LitsVector& microcode()
    {
        if (! f_ready) {
            fetch_microcode();
        }
        return f_microcode;
    }

private:
    const path& f_fullpath;
    OpTriple f_triple;

    bool f_ready;
    LitsVector f_microcode;

    void fetch_microcode();
};

typedef unordered_map<OpTriple, MicroLoader_ptr, OpTripleHash, OpTripleEq> MicroLoaderMap;

class MicroMgr  {

public:
    static MicroMgr& INSTANCE() {
        if (! f_instance) {
            f_instance = new MicroMgr();
        }
        return (*f_instance);
    }

    void show_info(ostream& os);

    MicroLoader& require(const OpTriple& triple);

protected:
    MicroMgr();
    ~MicroMgr();

private:
    static MicroMgr_ptr f_instance;

    MicroLoaderMap f_loaders;
};

#endif

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

#include <micro.hh>

typedef class MicroMgr *MicroMgr_ptr;

// <symb, is_signed?, width>
typedef tuple<bool, ExprType, int> OpTriple;
inline const OpTriple make_op_triple (bool is_signed, ExprType exprType, int width) {
    return make_tuple <bool, ExprType, int> (is_signed, exprType, width);
}

struct OpTripleHash {
    long operator() (const OpTriple& k) const
    {
        const long prime = 31;

        long res = 1;
        res = prime * res + (k.get<0>() ? 1231 : 1237);
        res = prime * res + k.get<1>();
        res = prime * res + k.get<2>();
        return res;
    }
};

struct OpTripleEq {
    bool operator() (const OpTriple& x, const OpTriple& y) const
    {
        return
            x.get<0>() == y.get<0>() &&
            x.get<1>() == y.get<1>() &&
            x.get<2>() == y.get<2>()  ;
    }
};

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

    void load();

private:
    const path& f_fullpath;
    OpTriple f_triple;

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

protected:
    MicroMgr();
    ~MicroMgr();

private:
    static MicroMgr_ptr f_instance;

    // load microcode from data files
    void initialize();

    MicroLoaderMap f_loaders;
};

#endif

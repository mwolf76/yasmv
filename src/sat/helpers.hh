/**
 *  @file helpers.hh
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
#ifndef SAT_HELPERS
#define SAT_HELPERS

#include <expr/pool.hh>
#include <sat/sat.hh>

#include <boost/filesystem.hpp>

#include <dd/dd_walker.hh>

class InlinedOperatorLoaderException : public Exception {
public:
    InlinedOperatorLoaderException(const InlinedOperatorSignature& f_triple);
    ~InlinedOperatorLoaderException() throw();

    const char* what() const throw();

private:
    InlinedOperatorSignature f_triple;
};

typedef class InlinedOperatorLoader* InlinedOperatorLoader_ptr;
typedef boost::unordered_map<InlinedOperatorSignature, InlinedOperatorLoader_ptr,
                             InlinedOperatorSignatureHash,
                             InlinedOperatorSignatureEq> InlinedOperatorLoaderMap;


class InlinedOperatorLoader {
public:
    InlinedOperatorLoader(const boost::filesystem::path& filepath);
    ~InlinedOperatorLoader();

    inline const InlinedOperatorSignature& triple() const
    { return f_triple; }

    // synchronized
    const LitsVector& clauses();

private:
    boost::mutex f_loading_mutex;
    LitsVector f_clauses;

    boost::filesystem::path f_fullpath;
    InlinedOperatorSignature f_triple;
};

typedef class InlinedOperatorMgr *InlinedOperatorMgr_ptr;
class InlinedOperatorMgr  {

public:
    static InlinedOperatorMgr& INSTANCE() {
        if (! f_instance) {
            f_instance = new InlinedOperatorMgr();
        }
        return (*f_instance);
    }

    InlinedOperatorLoader& require(const InlinedOperatorSignature& triple);

    inline const InlinedOperatorLoaderMap& loaders() const
    { return f_loaders; }

protected:
    InlinedOperatorMgr();
    ~InlinedOperatorMgr();

private:
    static InlinedOperatorMgr_ptr f_instance;
    InlinedOperatorLoaderMap f_loaders;
};


class CNFOperatorInliner {
public:
    CNFOperatorInliner(Engine& sat, step_t time, group_t group = MAINGROUP)
        : f_sat(sat)
        , f_time(time)
        , f_group(group)
    {}

    ~CNFOperatorInliner()
    {}

    inline void operator() (const InlinedOperatorDescriptor& md)
    {
        InlinedOperatorMgr& mm
            (InlinedOperatorMgr::INSTANCE());

        InlinedOperatorSignature triple
            (md.triple());
        InlinedOperatorLoader& loader
            (mm.require(triple));

        inject(md, loader.clauses());
    }

private:
    void inject(const InlinedOperatorDescriptor& md,
                const LitsVector& clauses);

    Engine& f_sat;
    step_t f_time;
    group_t f_group;
};

class CNFBinarySelectionInliner {
public:
    CNFBinarySelectionInliner(Engine& sat, step_t time, group_t group = MAINGROUP)
        : f_sat(sat)
        , f_time(time)
        , f_group(group)
    {}

    ~CNFBinarySelectionInliner()
    {}

    inline void operator() (const BinarySelectionDescriptor& md)
    { inject(md); }

private:
    void inject(const BinarySelectionDescriptor& md);

    Engine& f_sat;
    step_t f_time;
    group_t f_group;
};

class CNFMultiwaySelectionInliner {
public:
    CNFMultiwaySelectionInliner(Engine& sat, step_t time, group_t group = MAINGROUP)
        : f_sat(sat)
        , f_time(time)
        , f_group(group)
    {}

    ~CNFMultiwaySelectionInliner()
    {}

    inline void operator() (const MultiwaySelectionDescriptor& md)
    { inject(md); }

private:
    void inject(const MultiwaySelectionDescriptor& md);

    Engine& f_sat;
    step_t f_time;
    group_t f_group;
};

#endif

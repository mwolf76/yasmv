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

class MicroLoaderException : public Exception {
public:
    MicroLoaderException(const InlinedOperatorSignature& f_triple);
    ~MicroLoaderException() throw();

    const char* what() const throw();

private:
    InlinedOperatorSignature f_triple;
};

typedef class MicroLoader* MicroLoader_ptr;
typedef boost::unordered_map<InlinedOperatorSignature, MicroLoader_ptr,
                             InlinedOperatorSignatureHash,
                             InlinedOperatorSignatureEq> MicroLoaderMap;


class MicroLoader {
public:
    MicroLoader(const boost::filesystem::path& filepath);
    ~MicroLoader();

    inline const InlinedOperatorSignature& triple() const
    { return f_triple; }

    // synchronized
    const LitsVector& microcode();

private:
    boost::mutex f_loading_mutex;
    LitsVector f_microcode;

    boost::filesystem::path f_fullpath;
    InlinedOperatorSignature f_triple;
};

typedef class MicroMgr *MicroMgr_ptr;
class MicroMgr  {

public:
    static MicroMgr& INSTANCE() {
        if (! f_instance) {
            f_instance = new MicroMgr();
        }
        return (*f_instance);
    }

    MicroLoader& require(const InlinedOperatorSignature& triple);

    inline const MicroLoaderMap& loaders() const
    { return f_loaders; }

protected:
    MicroMgr();
    ~MicroMgr();

private:
    static MicroMgr_ptr f_instance;
    MicroLoaderMap f_loaders;
};


class CNFMicrocodeInjector {
public:
    CNFMicrocodeInjector(Engine& sat, step_t time, group_t group = MAINGROUP)
        : f_sat(sat)
        , f_time(time)
        , f_group(group)
    {}

    ~CNFMicrocodeInjector()
    {}

    inline void operator() (const InlinedOperatorDescriptor& md)
    {
        MicroMgr& mm
            (MicroMgr::INSTANCE());

        InlinedOperatorSignature triple
            (md.triple());
        MicroLoader& loader
            (mm.require(triple));

        inject(md, loader.microcode());
    }

private:
    void inject(const InlinedOperatorDescriptor& md,
                const LitsVector& microcode);

    Engine& f_sat;
    step_t f_time;
    group_t f_group;
};

class CNFMuxcodeInjector {
public:
    CNFMuxcodeInjector(Engine& sat, step_t time, group_t group = MAINGROUP)
        : f_sat(sat)
        , f_time(time)
        , f_group(group)
    {}

    ~CNFMuxcodeInjector()
    {}

    inline void operator() (const BinarySelectionDescriptor& md)
    { inject(md); }

private:
    void inject(const BinarySelectionDescriptor& md);

    Engine& f_sat;
    step_t f_time;
    group_t f_group;
};

class CNFArrayMuxcodeInjector {
public:
    CNFArrayMuxcodeInjector(Engine& sat, step_t time, group_t group = MAINGROUP)
        : f_sat(sat)
        , f_time(time)
        , f_group(group)
    {}

    ~CNFArrayMuxcodeInjector()
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

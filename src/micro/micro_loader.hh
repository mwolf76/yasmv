/**
 *  @file micro_loader.hh
 *  @brief Microcode library - microcode loader module
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
#ifndef MICRO_LOADER_H
#define MICRO_LOADER_H

#include <boost/thread/mutex.hpp>
#include <boost/filesystem.hpp>

#include <micro.hh>

class MicroLoaderException : public Exception {
public:
    MicroLoaderException(const OpTriple& f_triple);
    ~MicroLoaderException() throw();

    const char* what() const throw();

private:
    OpTriple f_triple;
};

typedef class MicroLoader* MicroLoader_ptr;
typedef boost::unordered_map<OpTriple, MicroLoader_ptr,
                             OpTripleHash, OpTripleEq> MicroLoaderMap;

class MicroLoader {
public:
MicroLoader(const boost::filesystem::path& filepath);
    ~MicroLoader();

    inline const OpTriple& triple() const
    { return f_triple; }

    // synchronized
    const LitsVector& microcode();

private:
    boost::mutex f_loading_mutex;
    LitsVector f_microcode;

    boost::filesystem::path f_fullpath;
    OpTriple f_triple;
};

#endif

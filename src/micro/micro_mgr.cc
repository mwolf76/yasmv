/**
 *  @file micro.cc
 *  @brief Micro module
 *
 *  This module contains definitions and services that implement an
 *  optimized storage for microcode (i.e. pre-calculated CNFs for
 *  algebraic operators with unsigned/signed semantics and different
 *  operand widths in [1..64].
 *
 *  Loading this entire data set at startup-time would require a long
 *  time, therefore the manager uses a lazy approach consisting in two
 *  phases: 1. at startup time, the microcode storage directory is
 *  scanned to determine which microcodes are present. Accordingly,
 *  microcode loader instances are created. 2. at compile time, when
 *  the compiler determines it needs a certain microcode to perform
 *  its task the appropriate microcode loader fetches data from disk.
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

#include <common.hh>

#include <expr.hh>

#include <type.hh>
#include <micro.hh>
#include <micro_mgr.hh>

#include <3rdparty/jsoncpp/json.hh>

// static initialization
MicroMgr_ptr MicroMgr::f_instance = NULL;

MicroMgr::MicroMgr()
{
    char *basepath = getenv( YASMV_HOME );
    if (NULL == basepath) {
        ERR << YASMV_HOME << " is not set. Exiting..." << endl;
        exit(1);
    }
    path micropath = basepath / path ( MICROCODE_PATH );
    DEBUG << micropath;

    try {
        if (exists(micropath) && is_directory(micropath)) {
            for (directory_iterator di = directory_iterator(micropath);
                 di != directory_iterator(); ++ di) {

                path entry (di->path());
                if (strcmp(entry.extension().c_str(), ".json")) {
                    continue;
                }

                // lazy microcode-loaders registration
                try {
                    MicroLoader* loader = new MicroLoader(entry);
                    assert(NULL != loader);

                    DRIVEL << "Registering microcode loader for "
                           << loader->triple()
                           << "..."
                           << endl;

                    f_loaders.insert( make_pair< OpTriple, MicroLoader_ptr >
                                      (loader->triple(), loader));
                }
                catch (MicroLoaderException mle) {
                    string tmp(mle.what());
                    WARN << tmp << endl;
                }
            }
        }
        else {
            ERR << "Path " << micropath
                << " does not exist or is not a readable directory.";
            exit(1);
        }
    }
    catch (const filesystem_error& ex) {
        string tmp(ex.what());
        ERR << tmp;
        exit(1);
    }
 }

 MicroMgr::~MicroMgr()
 {
 }

MicroLoader& MicroMgr::require(const OpTriple& triple)
{
    MicroLoaderMap::const_iterator i = f_loaders.find( triple );
    if (i == f_loaders.end()) {
        throw MicroLoaderException(triple);
    }

    return * i->second;
}

ostream& operator<<(ostream& os, OpTriple triple)
{
    bool is_signed (triple.get<0>());
    os << (is_signed ? "s" : "u");
    switch (triple.get<1>()) {
    case NEG: os << "neg"; break;
    case NOT: os << "not"; break;

    case PLUS: os << "add"; break;
    case SUB:  os << "sub"; break;
    case MUL:  os << "mul"; break;
    case DIV:  os << "div"; break;
    case MOD:  os << "mod"; break;

    case BW_AND: os << "and"; break;
    case BW_OR:  os << "or";  break;
    case BW_XOR: os << "xor"; break;
    case BW_XNOR:os << "xnor";break;
    case IMPLIES: os << "implies"; break;

    case EQ: os << "eq"; break;
    case NE: os << "ne"; break;
    case LT: os << "lt"; break;
    case LE: os << "le"; break;
    case GT: os << "gt"; break;
    case GE: os << "ge"; break;

    default: assert(false);
    }
    os << triple.get<2>();
    return os;
}


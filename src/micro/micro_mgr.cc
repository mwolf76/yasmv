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

static const char* JSON_GENERATED = "generated";
static const char* JSON_CNF       = "cnf";

ostream& operator<<(ostream& os, OpTriple triple)
{
    bool is_signed (triple.get<0>());
    os << (is_signed ? "s" : "u");
    switch (triple.get<1>())   {
    case PLUS: os << "add"; break;
    case SUB:  os << "sub"; break;
    case MUL:  os << "mul"; break;
    case DIV:  os << "div"; break;
    case MOD:  os << "mod"; break;
    default: assert(false);
    }
    os << triple.get<2>();
    return os;
}

MicroLoaderException::MicroLoaderException(const OpTriple& triple)
    : f_triple(triple)
{}

const char* MicroLoaderException::what() const throw()
{
    ostringstream oss;
    oss << "MicroLoaderException: can not instantiate loader for" << f_triple;

    return oss.str().c_str();
}

MicroLoaderException::~MicroLoaderException() throw()
{}

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

void MicroMgr::show_info(ostream &os)
{
    os << f_loaders.size()
       << " microcode loaders registered." << endl
       << "known operators: "
    ;

    for (MicroLoaderMap::const_iterator i = f_loaders.begin();
         i != f_loaders.end(); ++ i) {
        os << i->first << " " ;
    }
    os << endl << endl;
}

MicroLoader& MicroMgr::require(const OpTriple& triple)
{
    MicroLoaderMap::const_iterator i = f_loaders.find( triple );
    if (i == f_loaders.end()) {
        throw MicroLoaderException(triple);
    }

    return * i->second;
}


MicroLoader::MicroLoader(const path& filepath)
    : f_fullpath(filepath)
    , f_ready(false)
    , f_microcode()
{
    const string native (filepath.filename().replace_extension().native());

    std::vector<std::string> fragments;
    split(fragments, native, boost::is_any_of("-"));

    // FIXME: better validation for microcode fragment filenames
    assert(fragments.size() == 3 && (fragments[0] == "s" || fragments[0] == "u"));

    bool op_signed (fragments[0] == "s");
    ExprType op_type (ExprMgr::INSTANCE().exprTypeFromString(fragments[1]));
    int op_width (strtol(fragments[2].c_str(), NULL, 10));

    f_triple = make_op_triple( op_signed, op_type, op_width );
}

MicroLoader::~MicroLoader()
{}

void MicroLoader::fetch_microcode()
{
    unsigned count(0);
    clock_t t0 = clock(), t1;
    double secs;

    // this shall be executed only once
    assert( ! f_ready );

    Lits newClause;
    ifstream json_file(f_fullpath.c_str());

    Json::Value obj;
    json_file >> obj;
    assert(obj.type() == Json::objectValue);

    const Json::Value generated (obj[ JSON_GENERATED ]);
    DEBUG
        << "Loading microcode for "
        << f_triple
        << ", generated " << generated
        << endl;

    const Json::Value cnf (obj[ JSON_CNF ]);
    assert( cnf.type() == Json::arrayValue);

    for (Json::Value::const_iterator i = cnf.begin(); cnf.end() != i; ++ i) {
        const Json::Value clause (*i);

        assert( clause.type() == Json::arrayValue);
        newClause.clear();
        for (Json::Value::const_iterator j = clause.begin(); clause.end() != j; ++ j) {
            const Json::Value literal (*j);
            assert( literal.type() == Json::intValue );
            newClause.push_back( Minisat::toLit(literal.asInt()));
        }
        f_microcode.push_back( newClause ); ++ count;
    }
    t1 = clock(); secs = 1000 * (double) (t1 - t0) / (double) CLOCKS_PER_SEC;
    DEBUG << count
          << " clauses fetched, took " << secs
          << " ms"
          << endl;

    f_ready = true;
}

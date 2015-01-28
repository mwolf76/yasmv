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

#include <sstream>
#include <common.hh>

#include <boost/algorithm/string.hpp>

#include <3rdparty/jsoncpp/json.hh>

#include <expr/expr.hh>

#include <type/type.hh>

#include <micro/micro.hh>
#include <micro/micro_loader.hh>

static const char* JSON_GENERATED = "generated";
static const char* JSON_CNF       = "cnf";

MicroLoaderException::MicroLoaderException(const InlinedOperatorSignature& triple)
    : f_triple(triple)
{}

const char* MicroLoaderException::what() const throw()
{
    std::ostringstream oss;
    oss
        << "MicroLoaderException: can not instantiate loader for" << f_triple;

    return oss.str().c_str();
}

MicroLoaderException::~MicroLoaderException() throw()
{}

MicroLoader::MicroLoader(const boost::filesystem::path& filepath)
    : f_fullpath(filepath)
{
    const std::string native (filepath.filename().replace_extension().native());

    std::vector<std::string> fragments;
    split(fragments, native, boost::is_any_of("-"));

    assert(3 == fragments.size());

    const char* signedness(fragments[0].c_str());
    assert( *signedness == 's' || *signedness == 'u');

    const char* op (fragments[1].c_str());
    ExprType op_type;
    if      (!strcmp( "neg", op)) op_type = NEG;
    else if (!strcmp( "add", op)) op_type = PLUS;
    else if (!strcmp( "sub", op)) op_type = SUB;
    else if (!strcmp( "div", op)) op_type = DIV;
    else if (!strcmp( "mod", op)) op_type = MOD;
    else if (!strcmp( "mul", op)) op_type = MUL;
    else if (!strcmp( "not", op)) op_type = BW_NOT;
    else if (!strcmp( "or",  op)) op_type = BW_OR;
    else if (!strcmp( "and", op)) op_type = BW_AND;
    else if (!strcmp( "xor", op)) op_type = BW_XOR;
    else if (!strcmp( "xnor",op)) op_type = BW_XNOR;
    else if (!strcmp( "eq",  op)) op_type = EQ;
    else if (!strcmp( "ne",  op)) op_type = NE;
    else if (!strcmp( "gt",  op)) op_type = GT;
    else if (!strcmp( "ge",  op)) op_type = GE;
    else if (!strcmp( "lt",  op)) op_type = LT;
    else if (!strcmp( "le",  op)) op_type = LE;
    else assert (false);

    const char* width(fragments[2].c_str());
    for (const char *p = width; *p; ++ p)
        assert( isdigit(*p));

    f_triple = make_ios( 's' == *signedness, op_type, atoi(width));
}

MicroLoader::~MicroLoader()
{}

const LitsVector& MicroLoader::microcode()
{
    boost::mutex::scoped_lock lock(f_loading_mutex);

    if (0 == f_microcode.size()) {

        unsigned count(0);
        clock_t t0 = clock(), t1;
        double secs;

        Lits newClause;
        std::ifstream json_file(f_fullpath.c_str());

        Json::Value obj;
        json_file >> obj;
        assert(obj.type() == Json::objectValue);

        const Json::Value generated (obj[ JSON_GENERATED ]);
        DEBUG
            << "Loading microcode for " << f_triple
            << ", generated " << generated
            << std::endl;

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

        DRIVEL
            << count
            << " clauses fetched, took " << secs
            << " ms"
            << std::endl;
    }

    return f_microcode;
}


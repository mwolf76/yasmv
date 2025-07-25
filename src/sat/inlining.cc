/**
 * @file helpers.cc
 * @brief SAT implementation, misc helpers implementation.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA
 *
 **/

#include <cstring>
#include <sstream>

#include <boost/algorithm/string.hpp>
#include <jsoncpp/json/json.h>

#include <compiler/streamers.hh>
#include <compiler/typedefs.hh>

#include <sat/engine.hh>
#include <sat/exceptions.hh>
#include <sat/inlining.hh>
#include <sat/typedefs.hh>

#include <dd/dd_walker.hh>

#include <utils/misc.hh>
#include <utils/pool.hh>

namespace sat {

    static const char* JSON_GENERATED { "generated" };
    static const char* JSON_CNF { "cnf" };

    InlinedOperatorLoader::InlinedOperatorLoader(const boost::filesystem::path& filepath)
        : f_fullpath(filepath)
    {
        const std::string native { filepath.filename().replace_extension().native() };

        std::vector<std::string> fragments;
        split(fragments, native, boost::is_any_of("-"));

        assert(3 == fragments.size());

        const char* signedness { fragments[0].c_str() };
        assert(*signedness == 's' || *signedness == 'u');

        const char* op { fragments[1].c_str() };
        expr::ExprType op_type;
        if (!strcmp("neg", op)) {
            op_type = expr::ExprType::NEG;
        } else if (!strcmp("add", op)) {
            op_type = expr::ExprType::PLUS;
        } else if (!strcmp("sub", op)) {
            op_type = expr::ExprType::SUB;
        } else if (!strcmp("div", op)) {
            op_type = expr::ExprType::DIV;
        } else if (!strcmp("mod", op)) {
            op_type = expr::ExprType::MOD;
        } else if (!strcmp("mul", op)) {
            op_type = expr::ExprType::MUL;
        } else if (!strcmp("not", op)) {
            op_type = expr::ExprType::BW_NOT;
        } else if (!strcmp("or", op)) {
            op_type = expr::ExprType::BW_OR;
        } else if (!strcmp("and", op)) {
            op_type = expr::ExprType::BW_AND;
        } else if (!strcmp("xor", op)) {
            op_type = expr::ExprType::BW_XOR;
        } else if (!strcmp("xnor", op)) {
            op_type = expr::ExprType::BW_XNOR;
        } else if (!strcmp("impl", op)) {
            op_type = expr::ExprType::IMPLIES;
        } else if (!strcmp("eq", op)) {
            op_type = expr::ExprType::EQ;
        } else if (!strcmp("ne", op)) {
            op_type = expr::ExprType::NE;
        } else if (!strcmp("gt", op)) {
            op_type = expr::ExprType::GT;
        } else if (!strcmp("ge", op)) {
            op_type = expr::ExprType::GE;
        } else if (!strcmp("lt", op)) {
            op_type = expr::ExprType::LT;
        } else if (!strcmp("le", op)) {
            op_type = expr::ExprType::LE;
        } else if (!strcmp("lsh", op)) {
            op_type = expr::ExprType::LSHIFT;
        } else if (!strcmp("rsh", op)) {
            op_type = expr::ExprType::RSHIFT;
        } else {
            ERR
                << "Unsupported mnemonic: "
                << op
                << std::endl;
            assert(false);
        }

        char buf[20];
        strncpy(buf, fragments[2].c_str(), 19);
        buf[19] = '\0';

        char* width { buf };
        f_ios = compiler::make_ios('s' == *signedness, op_type, atoi(width));
    }

    InlinedOperatorLoader::~InlinedOperatorLoader()
    {}

    const LitsVector& InlinedOperatorLoader::clauses()
    {
        boost::mutex::scoped_lock lock { f_loading_mutex };

        if (0 == f_clauses.size()) {
            unsigned count { 0 };
            clock_t t0 { clock() };
            double secs;

            Lits newClause;
            std::ifstream json_file { f_fullpath.c_str() };

            Json::Value obj;
            json_file >> obj;
            assert(obj.type() == Json::objectValue);

            const Json::Value generated { obj[JSON_GENERATED] };

            DEBUG
                << "Loading clauses for "
                << f_ios
                << ", generated "
                << generated;

            const Json::Value cnf { obj[JSON_CNF] };
            assert(cnf.type() == Json::arrayValue);

            for (auto clause : cnf) {
                assert(clause.type() == Json::arrayValue);

                newClause.clear();
                for (auto literal : clause) {
                    assert(literal.type() == Json::intValue);
                    newClause.push_back(Minisat::toLit(literal.asInt()));
                }

                f_clauses.push_back(newClause);
                ++count;
            }

            clock_t t1 { clock() };
            secs = 1000 * (double) (t1 - t0) / (double) CLOCKS_PER_SEC;

            DRIVEL
                << count
                << " clauses fetched, took " << secs
                << " ms"
                << std::endl;
        }

        return f_clauses;
    }

    // static initialization
    InlinedOperatorMgr_ptr InlinedOperatorMgr::f_instance { NULL };

    InlinedOperatorMgr::InlinedOperatorMgr()
        : f_builtin_microcode_path(STRING(YASMV_HOME))
    {
        using boost::filesystem::directory_iterator;
        using boost::filesystem::filesystem_error;
        using boost::filesystem::path;

        char* env_microcode_path { getenv(YASMV_HOME_PATH) };
        if (NULL == env_microcode_path) {
            ERR
                << "YASMV_HOME must be set to a valid directory."
                << std::endl;
            exit(1);
        }

        path micropath { env_microcode_path
                             ? env_microcode_path
                             : f_builtin_microcode_path.c_str() };

        micropath += "/microcode/";
        try {
            if (exists(micropath) && is_directory(micropath)) {
                for (directory_iterator di = directory_iterator(micropath);
                     di != directory_iterator(); ++di) {

                    path entry { di->path() };
                    if (strcmp(entry.extension().c_str(), ".json")) {
                        continue;
                    }

                    // lazy clauses-loaders registration
                    try {
                        InlinedOperatorLoader* loader { new InlinedOperatorLoader(entry) };
                        assert(NULL != loader);

                        f_loaders.insert(
                            std::pair<compiler::InlinedOperatorSignature, InlinedOperatorLoader_ptr>(loader->ios(), loader));
                    } catch (InlinedOperatorLoaderException& iole) {
                        pconst_char what { iole.what() };
                        WARN
                            << what
                            << std::endl;
                    }
                }
            } else {
                ERR
                    << "Path "
                    << micropath
                    << " does not exist or is not a readable directory."
                    << std::endl;

                /* leave immediately */
                exit(1);
            }
        } catch (const filesystem_error& fse) {
            pconst_char what { fse.what() };

            ERR
                << what
                << std::endl;

            /* leave immediately */
            exit(1);
        }
    }

    InlinedOperatorMgr::~InlinedOperatorMgr()
    {
    }

    InlinedOperatorLoader& InlinedOperatorMgr::require(const compiler::InlinedOperatorSignature& ios)
    {
        InlinedOperatorLoaderMap::const_iterator i { f_loaders.find(ios) };

        if (i == f_loaders.end()) {
            DRIVEL
                << ios
                << " not found, falling back..."
                << std::endl;

            compiler::InlinedOperatorSignature fallback {
                compiler::make_ios(compiler::ios_issigned(ios), compiler::ios_optype(ios), compiler::ios_width(ios))
            };
            i = f_loaders.find(fallback);
        }

        if (i == f_loaders.end()) {
            throw InlinedOperatorLoaderException(ios);
        }

        return *i->second;
    }

    void CNFOperatorInliner::inject(const compiler::InlinedOperatorDescriptor& md,
                                    const LitsVector& clauses)
    {
        DRIVEL
            << const_cast<compiler::InlinedOperatorDescriptor&>(md)
            << std::endl;

        /* true */
        const Var alpha { 0 };

        /* local refs */
        const dd::DDVector& z { md.z() };
        const dd::DDVector& x { md.x() };
        const dd::DDVector& y { md.y() };
        int width { static_cast<int>(compiler::ios_width(md.ios())) };

        /* keep each injection in a separate cnf space */
        f_sat.clear_cnf_map();

        for (const auto& clause : clauses) {
            Minisat::vec<Lit> ps;
            if (MAINGROUP != f_group) {
                ps.push(mkLit(f_group, true));
            }

            /* for each literal in clause, determine whether
               associated var belongs to z, x, y or is a cnf var. For
               each group in (z, x, y) fetch appropriate DD var from
               the registry; cnf vars gets rewritten into new sat
               vars. Remark: rewritten cnf vars must be kept distinct
               among distinct injections. */
            for (auto lit : clause) {
                Var lit_var { Minisat::var(lit) };
                int lit_sign { Minisat::sign(lit) };

                Var tgt_var;

                /* z? */
                if (lit_var < width) {
                    int ndx { lit_var };
                    assert(0 <= ndx && ndx < width);

                    const DdNode* node { NULL };
                    if (md.is_relational()) {
                        assert(!ndx);
                        node = z[0].getNode();
                    } else {
                        node = z[width - ndx - 1].getNode();
                    }

                    if (!Cudd_IsConstant(node)) {
                        tgt_var = f_sat.find_dd_var(node, f_time);
                        ps.push(mkLit(tgt_var, lit_sign));
                    } else {
                        value_t value { cuddV(node) };

                        assert(value < 2); // 0 or 1
                        ps.push(mkLit(alpha, value ? lit_sign : !lit_sign));
                    }
                }

                /* x? */
                else if (width <= lit_var && lit_var < 2 * width) {
                    int ndx { lit_var - width };

                    assert(0 <= ndx && ndx < width);
                    const DdNode* node { x[width - ndx - 1].getNode() };

                    if (!Cudd_IsConstant(node)) {
                        tgt_var = f_sat.find_dd_var(node, f_time);
                        ps.push(mkLit(tgt_var, lit_sign));
                    } else {
                        value_t value { cuddV(node) };

                        assert(value < 2); // 0 or 1
                        ps.push(mkLit(alpha, value ? lit_sign : !lit_sign));
                    }
                }

                /* y? */
                else if (2 * width <= lit_var && lit_var < 3 * width) {
                    int ndx { lit_var - 2 * width };

                    assert(0 <= ndx && ndx < width);
                    const DdNode* node { y[width - ndx - 1].getNode() };

                    if (!Cudd_IsConstant(node)) {
                        tgt_var = f_sat.find_dd_var(node, f_time);
                        ps.push(mkLit(tgt_var, lit_sign));
                    } else {
                        value_t value { cuddV(node) };

                        assert(value < 2); // 0 or 1
                        ps.push(mkLit(alpha, value ? lit_sign : !lit_sign));
                    }
                }

                /* none of the above, it's a cnf var. */
                else {
                    int ndx { lit_var - 3 * width };

                    assert(0 <= ndx /* && ndx < width */);
                    tgt_var = f_sat.rewrite_cnf_var(ndx, f_time);
                    ps.push(mkLit(tgt_var, lit_sign));
                }

            } /* for (j = clause...) */

            f_sat.add_clause(ps);
        } /* foreach clause ... */

    } /* CNFOperatorInliner::inject */

    void CNFBinarySelectionInliner::inject(const compiler::BinarySelectionDescriptor& md)
    {
        DRIVEL
            << const_cast<compiler::BinarySelectionDescriptor&>(md)
            << std::endl;

        /* true */
        const Var alpha { 0 };

        /* local refs */
        const dd::DDVector& z { md.z() };
        const ADD& aux { md.aux() };
        const dd::DDVector& x { md.x() };
        const dd::DDVector& y { md.y() };

        /* allocate a fresh variable for ITE condition */
        Var act { f_sat.find_dd_var(aux.getNode(), f_time) };

        /* ! a, Zi <-> Xi for all i */
        for (unsigned pol = 0; pol < 2; ++pol) {
            for (unsigned i = 0; i < md.width(); ++i) {
                Minisat::vec<Lit> ps;

                if (MAINGROUP != f_group) {
                    ps.push(mkLit(f_group, true));
                }

                ps.push(mkLit(act, true));
                ps.push(mkLit(f_sat.find_dd_var(z[i].getNode(), f_time), !pol));
                DdNode* xnode { x[i].getNode() };

                ps.push(
                    Cudd_IsConstant(xnode)
                        ? mkLit(alpha, Cudd_V(xnode) ? pol : !pol)
                        : mkLit(f_sat.find_dd_var(x[i].getNode(), f_time), pol));

                f_sat.add_clause(ps);
            }
        }

        /* a, Zi <-> Yi for all i */
        for (unsigned pol = 0; pol < 2; ++pol) {
            for (unsigned i = 0; i < md.width(); ++i) {
                Minisat::vec<Lit> ps;

                if (MAINGROUP != f_group) {
                    ps.push(mkLit(f_group, true));
                }

                ps.push(mkLit(act, false));
                ps.push(mkLit(f_sat.find_dd_var(z[i].getNode(), f_time), !pol));
                DdNode* ynode { y[i].getNode() };

                ps.push(
                    Cudd_IsConstant(ynode)
                        ? mkLit(alpha, Cudd_V(ynode) ? pol : !pol)
                        : mkLit(f_sat.find_dd_var(y[i].getNode(), f_time), pol));

                f_sat.add_clause(ps);
            }
        }
    }

    void CNFMultiwaySelectionInliner::inject(const compiler::MultiwaySelectionDescriptor& md)
    {
        DEBUG
            << const_cast<compiler::MultiwaySelectionDescriptor&>(md)
            << std::endl;

        /* true */
        const Var alpha(0);

        /* local refs */
        const dd::DDVector& z { md.z() };
        const dd::DDVector& acts { md.acts() };
        const dd::DDVector& x { md.x() };

        unsigned j { 0 };
        dd::DDVector::const_iterator ai { acts.begin() };
        while (j < md.elem_count()) {

            /* allocate a fresh variable for ITE condition */
            Var act { f_sat.find_dd_var((*ai).getNode(), f_time) };

            /* ! a, Zi <-> Xi for all i */
            for (unsigned pol = 0; pol < 2; ++pol) {
                for (unsigned i = 0; i < md.elem_width(); ++i) {
                    unsigned ndx { i + j * md.elem_width() };

                    Minisat::vec<Lit> ps;

                    if (MAINGROUP != f_group) {
                        ps.push(mkLit(f_group, true));
                    }

                    ps.push(mkLit(act, true));
                    ps.push(mkLit(f_sat.find_dd_var(z[i].getNode(), f_time), !pol));
                    ps.push(mkLit(f_sat.find_dd_var(x[ndx].getNode(), f_time), pol));
                    f_sat.add_clause(ps);
                }
            }

            ++j;
            ++ai;
        }
    }

} // namespace sat

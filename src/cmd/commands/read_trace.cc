/**
 * @file read_trace.cc
 * @brief Command `read-trace` class implementation.
 *
 * Copyright (C) 2012-2018 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
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

#include <cstdlib>
#include <cstring>
#include <iostream>

#include <boost/algorithm/string.hpp>
#include <boost/algorithm/string/predicate.hpp>
#include <boost/filesystem.hpp>

#include <cmd/commands/commands.hh>
#include <cmd/commands/read_trace.hh>

#include <model/model_mgr.hh>

#include <parse.hh>

#include <witness/witness.hh>
#include <witness/witness_mgr.hh>

namespace cmd {

    ReadTraceWitness::ReadTraceWitness(expr::Atom id, expr::Atom desc)
        : witness::Witness(NULL, id, desc)
    {
        model::ModelMgr& mm { model::ModelMgr::INSTANCE() };
        expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };

        symb::SymbIter si { mm.model() };
        while (si.has_next()) {
            std::pair<expr::Expr_ptr, symb::Symbol_ptr> pair { si.next() };
            expr::Expr_ptr ctx { pair.first };
            symb::Symbol_ptr symbol { pair.second };

            expr::Expr_ptr identifier { em.make_dot(ctx, symbol->name()) };
            f_lang.push_back(identifier);

            DEBUG
                << "Added symbol `"
                << identifier
                << "`"
                << std::endl;
        }

        TRACE
            << "Created new witness for reading, "
            << "id: "
            << id << ", "
            << "description: "
            << desc
            << std::endl;
    }

    ReadTrace::ReadTrace(Interpreter& owner)
        : Command(owner)
        , f_out(std::cout)
        , f_input(NULL)
    {}

    ReadTrace::~ReadTrace()
    {
        free(f_input);
        f_input = NULL;
    }

    void ReadTrace::set_input(pconst_char input)
    {
        if (input) {
            free(f_input);
            f_input = strdup(input);
        }
    }

    bool ReadTrace::check_requirements()
    {
        model::ModelMgr& mm { model::ModelMgr::INSTANCE() };

        if (!f_input) {
            WARN
                << "No input filename provided. (missing quotes?)"
                << std::endl;

            return false;
        }

        model::Model& model { mm.model() };
        if (model.empty()) {
            f_out
                << wrnPrefix
                << "Model not loaded."
                << std::endl;

            return false;
        }

        return true;
    }

    utils::Variant ReadTrace::operator()()
    {
        if (!check_requirements()) {
            return utils::Variant { errMessage };
        }

        bool ok { true };

        boost::filesystem::path tracepath { f_input };
        const auto extension { tracepath.extension() };
        if (!exists(tracepath)) {
            WARN
                << "File `"
                << f_input
                << "` does not exist."
                << std::endl;

            ok = false;
        } else if (!is_regular_file(tracepath)) {
            WARN
                << "File `"
                << f_input
                << "` is not a regular file."
                << std::endl;

            ok = false;
        } else if (extension == ".json") {
            if (!parseJsonTrace(tracepath)) {
                WARN
                    << "Cannot read JSON trace from file `"
                    << tracepath << "`"
                    << std::endl;

                ok = false;
            }
        } else if (extension == ".yaml") {
            if (!parseYamlTrace(tracepath)) {
                WARN
                    << "Cannot read YAML trace from file `"
                    << tracepath << "`"
                    << std::endl;

                ok = false;
            }
        } else if (!parsePlainTrace(tracepath)) {
            WARN
                << "Cannot read PLAIN trace from file `"
                << tracepath << "`"
                << std::endl;

            ok = false;
        }

        return utils::Variant { ok ? okMessage : errMessage };
    }

    bool ReadTrace::parsePlainTrace(boost::filesystem::path& tracepath)
    {
        expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };
        witness::WitnessMgr& wm { witness::WitnessMgr::INSTANCE() };

        witness::Witness_ptr witness = NULL;
        witness::TimeFrame_ptr current = NULL;

        TRACE
            << "Reading PLAIN trace from file "
            << tracepath
            << " ..."
            << std::endl;

        std::string raw;
        std::ifstream src { tracepath.string() };

        if (src.is_open()) {
            while (getline(src, raw)) {
                std::string trimmed { boost::algorithm::trim_copy(raw) };

                /* skip empty lines and comments */
                if (trimmed.empty() || boost::starts_with(trimmed, "--")) {
                    continue;
                }

                const char* id_prefix { "Witness:" };
                if (boost::starts_with(trimmed, id_prefix)) {
                    std::string witness_id {
                        boost::algorithm::trim_copy(
                            boost::algorithm::erase_head_copy(
                                trimmed, strlen(id_prefix)))
                    };

                    std::ostringstream oss;
                    oss
                        << "Loaded from "
                        << tracepath;

                    witness = new ReadTraceWitness(witness_id, oss.str());
                    continue;
                }

                const char* time_prefix { ":: @" };
                if (boost::starts_with(trimmed, time_prefix)) {
                    std::string time_string { boost::algorithm::erase_head_copy(trimmed, strlen(time_prefix)) };
                    DEBUG
                        << "Parsing time value: "
                        << time_string
                        << std::endl;

                    step_t k { (step_t) std::stoi(time_string) };
                    current = &witness->extend();
                    assert(k == witness->last_time());
                    continue;
                }

                if (boost::algorithm::contains(trimmed, "=")) {
                    std::vector<std::string> split;

                    boost::split(split, trimmed, boost::is_any_of("="));
                    if (2 != split.size()) {
                        throw ReadTraceException("FileFormat", "Malformed assignment");
                    }

                    expr::Expr_ptr ctx { em.make_empty() };
                    expr::Expr_ptr lhs {
                        parse::parseExpression(
                            boost::algorithm::trim_copy(split[0]).c_str())
                    };
                    expr::Expr_ptr rhs {
                        parse::parseExpression(
                            boost::algorithm::trim_copy(split[1]).c_str())
                    };

                    DRIVEL
                        << lhs
                        << " = "
                        << rhs
                        << std::endl;

                    current->set_value(em.make_dot(ctx, lhs), rhs);
                    continue;
                }

                ERR
                    << "Encountered unexpected line: "
                    << raw
                    << std::endl;
                throw ReadTraceException("FileFormat", "Unexpected");
            }

            src.close();
            wm.record(*witness);

            return true;
        }

        return false;
    }

    bool ReadTrace::parseJsonTrace(boost::filesystem::path& tracepath)
    {
        TRACE
            << "Reading JSON trace from file "
            << tracepath
            << " ..."
            << std::endl;

        // TODO: not implemented yet
        return false;
    }

    bool ReadTrace::parseYamlTrace(boost::filesystem::path& tracepath)
    {
        TRACE
            << "Reading YAML trace from file "
            << tracepath
            << " ..."
            << std::endl;

        // TODO: not implemented yet
        return false;
    }

    ReadTraceTopic::ReadTraceTopic(Interpreter& owner)
        : CommandTopic(owner)
    {}

    ReadTraceTopic::~ReadTraceTopic()
    {
        TRACE
            << "Destroyed read-trace topic"
            << std::endl;
    }

    void ReadTraceTopic::usage()
    {
        display_manpage("read-trace");
    }

} // namespace cmd

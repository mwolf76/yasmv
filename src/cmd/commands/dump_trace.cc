/*
 * @file dump_trace.cc
 * @brief Command `dump-trace` class implementation.
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

#include <algorithm>
#include <cstdlib>
#include <cstring>

#include <cmd/commands/commands.hh>
#include <cmd/commands/dump_trace.hh>

#include <env/environment.hh>

#include <expr/expr.hh>
#include <expr/expr_mgr.hh>

#include <witness/witness.hh>
#include <witness/witness_mgr.hh>

#include <iostream>

#include <boost/preprocessor/repetition/repeat.hpp>

namespace cmd {

    static std::string build_unsupported_format_error_message(pconst_char format)
    {
        std::ostringstream oss;

        oss
            << "CommandError: format `"
            << format
            << "` is not supported.";

        return oss.str();
    }

    UnsupportedFormat::UnsupportedFormat(pconst_char format)
        : CommandException(build_unsupported_format_error_message(format))
    {}

    static std::string build_bad_request_error_message()
    {
        std::ostringstream oss;

        oss
            << "CommandError: Cannot specify a witness identifier when -a is enabled.";

        return oss.str();
    }

    BadRequest::BadRequest()
        : CommandException(build_bad_request_error_message())
    {}

    DumpTrace::DumpTrace(Interpreter& owner)
        : Command(owner)
        , f_format(strdup(TRACE_FMT_DEFAULT))
        , f_output(NULL)
        , f_all(false)
    {}

    DumpTrace::~DumpTrace()
    {
        free((pchar) f_format);
        free(f_output);
    }

    void DumpTrace::set_format(pconst_char format)
    {
        f_format = strdup(format);
        if (strcmp(f_format, TRACE_FMT_PLAIN) &&
            strcmp(f_format, TRACE_FMT_JSON)) {
            throw UnsupportedFormat(f_format);
        }
    }

    void DumpTrace::add_trace_id(pconst_char trace_id)
    {
        if (f_all) {
            throw BadRequest();
        }

        expr::Atom atom { expr::ExprMgr::INSTANCE().internalize(trace_id) };
        f_trace_ids.push_back(atom);
    }

    void DumpTrace::set_output(pconst_char output)
    {
        free(f_output);
        f_output = strdup(output);
    }

    void DumpTrace::set_all(bool value)
    {
        assert(value); // clearing is not supported

        if (!f_trace_ids.empty()) {
            throw BadRequest();
        }

        f_all = true;
    }

    void DumpTrace::dump_plain(std::ostream& os, const witness::WitnessList& witness_list)
    {
        std::for_each(
            begin(witness_list), end(witness_list),
            [this, &os](witness::Witness_ptr wp) {
                witness::Witness& w { *wp };

                os
                    << "-- "
                    << w.desc()
                    << std::endl
                    << "Witness: "
                    << w.id()
                    << std::endl
                    << std::endl;

                expr::ExprVector input_assignments;
                process_input(w, input_assignments);

                if (0 < input_assignments.size()) {
                    os
                        << ":: ENV"
                        << std::endl;
                    dump_plain_section(os, "input", input_assignments);
                }

                for (step_t time = w.first_time(); time <= w.last_time(); ++time) {
                    os
                        << ":: @"
                        << std::dec
                        << time
                        << std::endl;

                    expr::ExprVector state_vars_assignments;
                    expr::ExprVector defines_assignments;

                    process_time_frame(w, time,
                                       state_vars_assignments,
                                       defines_assignments);

                    dump_plain_section(os, "state", state_vars_assignments);
                    dump_plain_section(os, "defines", defines_assignments);
                }
            });
    }

    void DumpTrace::dump_plain_section(std::ostream& os,
                                        const char* section,
                                        expr::ExprVector& assignments)
    {

        /* a boost hack to generate indentation consts */
#define _SPACE(z, n, str) " "
#define SPACES(n) BOOST_PP_REPEAT(n, _SPACE, NULL)
        const char* TAB { SPACES(3) };

        if (assignments.empty()) {
            return;
        }

        os
            << "-- "
            << section
            << std::endl;

        for (auto eq : assignments) {
            os
                << TAB
                << eq->lhs()
                << " = "
                << eq->rhs()
                << std::endl;
        }

        os
            << std::endl;
    }

    void DumpTrace::dump_json(std::ostream& os, const witness::WitnessList& witness_list)
    {
        expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };

        Json::StreamWriterBuilder builder;
        const std::unique_ptr<Json::StreamWriter> writer { builder.newStreamWriter() };

        Json::Value root, lst { Json::arrayValue };
        std::for_each(
            begin(witness_list), end(witness_list),
            [this, &em, &lst](witness::Witness_ptr wp) {
                Json::Value obj;

                obj["id"] = wp->id();
                obj["description"] = wp->desc();

                /* dump input assignments */
                expr::ExprVector input_vars_assignments;
                process_input(*wp, input_vars_assignments);
                Json::Value input { section_to_json(input_vars_assignments) };
                if (!input.empty()) {
                    obj["input"] = input;
                }

                Json::Value steps { Json::arrayValue };
                for (step_t time = wp->first_time(); time <= wp->last_time(); ++time) {
                    Json::Value step;

                    expr::ExprVector state_vars_assignments;
                    expr::ExprVector defines_assignments;
                    process_time_frame(*wp, time,
                                       state_vars_assignments,
                                       defines_assignments);

                    Json::Value vars { section_to_json(state_vars_assignments) };
                    if (!vars.empty()) {
                        step["state"] = vars;
                    }

                    Json::Value defs { section_to_json(defines_assignments) };
                    if (!defs.empty()) {
                        step["defines"] = defs;
                    }

                    steps.append(step);
                }
                obj["steps"] = steps;
                lst.append(obj);
            });

        root["traces"] = lst;
        os
            << root.toStyledString()
            << std::endl;
    }

    Json::Value DumpTrace::section_to_json(expr::ExprVector& assignments)
    {
        expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };
        Json::Value res;

        std::for_each(
            begin(assignments), end(assignments),
            [&res, &em](expr::Expr_ptr assignment) {
                expr::Atom lhs { assignment->lhs()->rhs()->atom() };
                expr::Expr_ptr rhs { assignment->rhs() };

                if (em.is_identifier(rhs)) {
                    res[lhs] = rhs->atom();
                } else if (em.is_bool_const(rhs)) {
                    res[lhs] = em.is_true(rhs);
                } else if (em.is_array(rhs)) {
                    Json::Value array_value { Json::arrayValue };
                    expr::ExprVector values { em.array_literals(rhs) };

                    std::for_each(begin(values), end(values),
                                  [&array_value, &em](expr::Expr_ptr lit) {
                                      Json::Value scalar;
                                      if (em.is_identifier(lit)) {
                                          scalar = lit->atom();
                                      } else if (em.is_bool_const(lit)) {
                                          scalar = em.is_true(lit);
                                      } else if (em.is_array(lit)) {
                                          assert(false); // nested arrays are not supported
                                      } else if (em.is_constant(lit)) {
                                          scalar = (Json::Value::UInt64) em.const_value(lit);
                                      }
                                      array_value.append(scalar);
                                  });
                    res[lhs] = array_value;
                } else if (em.is_constant(rhs)) {
                    res[lhs] = (Json::Value::UInt64) em.const_value(rhs);
                } else {
                    assert(false);
                }
            });

        return res;
    }

    void DumpTrace::process_input(witness::Witness& w,
                                   expr::ExprVector& input_assignments)
    {
        expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };
        model::ModelMgr& mm { model::ModelMgr::INSTANCE() };
        env::Environment& env { env::Environment::INSTANCE() };

        model::Model& model { mm.model() };
        symb::SymbIter symbols { model };
        while (symbols.has_next()) {
            std::pair<expr::Expr_ptr, symb::Symbol_ptr> pair { symbols.next() };
            symb::Symbol_ptr symb { pair.second };

            if (symb->is_hidden()) {
                continue;
            }

            expr::Expr_ptr ctx { pair.first };
            expr::Expr_ptr name { symb->name() };
            expr::Expr_ptr full { em.make_dot(ctx, name) };

            if (symb->is_variable()) {
                symb::Variable& var { symb->as_variable() };

                /* we're interested only in INPUT vars here ... */
                if (!var.is_input()) {
                    continue;
                }

                expr::Expr_ptr value { env.get(name) };
                if (!value) {
                    value = em.make_undef();
                }

                input_assignments.push_back(em.make_eq(full, value));
            }
        } /* while (symbols.has_next()) */

        OrderingPreservingComparisonFunctor fun { model };
        sort(input_assignments.begin(),
             input_assignments.end(),
             fun);
    }

    /* here UNDEF is used to fill up symbols not showing up in the witness where
       they're expected to. (i. e. UNDEF is only a UI entity) */
    void DumpTrace::process_time_frame(witness::Witness& w, step_t time,
                                        expr::ExprVector& state_vars_assignments,
                                        expr::ExprVector& defines_assignments)
    {
        expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };
        model::ModelMgr& mm { model::ModelMgr::INSTANCE() };
        witness::WitnessMgr& wm { witness::WitnessMgr::INSTANCE() };

        witness::TimeFrame& tf { w[time] };
        model::Model& model { mm.model() };

        symb::SymbIter symbs { model };
        while (symbs.has_next()) {
            std::pair<expr::Expr_ptr, symb::Symbol_ptr> pair { symbs.next() };

            symb::Symbol_ptr symb { pair.second };
            if (symb->is_hidden()) {
                continue;
            }

            expr::Expr_ptr ctx { pair.first };
            expr::Expr_ptr name { symb->name() };
            expr::Expr_ptr full { em.make_dot(ctx, name) };
            if (symb->is_variable()) {
                symb::Variable& var { symb->as_variable() };

                /* INPUT vars do not belong in traces */
                if (var.is_input()) {
                    continue;
                }

                expr::Expr_ptr value {
                    tf.has_value(full)
                        ? tf.value(full)
                        : em.make_undef()
                };
                state_vars_assignments.push_back(em.make_eq(full, value));
            }

            else if (symb->is_define()) {
                symb::Define& define { symb->as_define() };
                expr::Expr_ptr body { define.body() };

                expr::Expr_ptr value {
                    wm.eval(w, ctx, body, time)
                };
                if (!value) {
                    value = em.make_undef();
                }

                defines_assignments.push_back(em.make_eq(full, value));
            }
        } /* while(symbs.has_next()) */

        OrderingPreservingComparisonFunctor fun { model };
        sort(state_vars_assignments.begin(),
             state_vars_assignments.end(), fun);

        sort(defines_assignments.begin(),
             defines_assignments.end(), fun);
    }

    std::ostream& DumpTrace::get_output_stream()
    {
        std::ostream* res { &std::cout };
        if (f_output) {
            if (f_outfile == NULL) {
                DEBUG
                    << "Writing output to file `"
                    << f_output
                    << "`"
                    << std::endl;

                f_outfile = new std::ofstream(f_output, std::ofstream::binary);
            }
            res = f_outfile;
        }

        return *res;
    }

    utils::Variant DumpTrace::operator()()
    {
        std::ostream& os { get_output_stream() };
        witness::WitnessMgr& wm { witness::WitnessMgr::INSTANCE() };

        witness::WitnessList witness_list;
        if (f_all) {
            witness_list = wm.witnesses();
        } else {
            // default to currently selected trace
            if (f_trace_ids.empty()) {
                f_trace_ids.push_back(wm.current().id());
            }

            // built list of witnesses to dump
            std::for_each(
                begin(f_trace_ids), end(f_trace_ids),
                [&wm, &witness_list](expr::Atom trace_id) {
                    witness::Witness& w { wm.witness(trace_id) };
                    witness_list.push_back(&w);
                });
        }

        if (!strcmp(f_format, TRACE_FMT_PLAIN)) {
            dump_plain(os, witness_list);
        } else if (!strcmp(f_format, TRACE_FMT_JSON)) {
            dump_json(os, witness_list);
        } else {
            assert(false);
        }

        return utils::Variant(okMessage);
    }

    DumpTraceTopic::DumpTraceTopic(Interpreter& owner)
        : CommandTopic(owner)
    {}

    DumpTraceTopic::~DumpTraceTopic()
    {
        TRACE
            << "Destroyed dump-trace topic"
            << std::endl;
    }

    void DumpTraceTopic::usage()
    {
        display_manpage("dump-trace");
    }

} // namespace cmd

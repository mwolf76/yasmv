/**
 * @file opts_mgr.cc
 * @brief Options Manager class implementation.
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
#include <iostream>
#include <sstream>
#include <iomanip>

#include <opts_mgr.hh>
#include <sat/engine.hh>
#include <jsoncpp/json/json.h>

#include <utils/logging.hh>

namespace opts {

    namespace {
        constexpr const char* retired_sat_options[] = {
            "sat-random-var-freq", "sat-random-init-act", "sat-ccmin-mode",
            "sat-phase-saving", "sat-garbage-frac", "sat-var-decay",
            "sat-clause-decay", "sat-luby-restart", "sat-restart-first",
            "sat-restart-inc", "sat-elim", "sat-rcheck", "sat-asymm",
            "sat-grow", "sat-clause-lim", "sat-subsumption-lim",
            "sat-simp-garbage-frac"
        };
    }

    // static initialization
    OptsMgr_ptr OptsMgr::f_instance = nullptr;

    OptsMgr::OptsMgr()
        : f_desc("Program options")
        , f_help(false)
        , f_quiet(false)
        , f_color(false)
        , f_started(false)
        , f_version(false)
        , f_skip_inertial_fsm_checks(false)
        , f_word_width(UINT_MAX)
    {
        // clang-format off
        
        // General options
        boost::program_options::options_description general_opts("General options");
        general_opts.add_options()
            ("session-file", boost::program_options::value<std::string>(), "load an immutable model snapshot and serve isolated JSON Lines queries")
            ("query-file", boost::program_options::value<std::string>(), "execute a typed query request and emit one JSON result")
            ("solver-info", "print linked SAT solver provenance as JSON and exit")
            (
                "help",
                "produce help message"
            )
            (
                "version",
                "produce version number"
            )
            (
                "quiet",
                "avoid any extra output"
            )
            (
                "color",
                "enables colorized output in interactive shell"
            )
            (
                "word-width",
                boost::program_options::value<unsigned>(),
                "native word size in bits (default: 16)"
            )
            (
                "verbosity",
                boost::program_options::value<unsigned>(),
                "verbosity level (default: 0)"
            )
            (
                "model",
                boost::program_options::value<std::string>(),
                "input model"
            )
            (
                "root",
                boost::program_options::value<std::string>(),
                "root module (required for models containing multiple modules)"
            )
            ;

        // CNF optimization options
        boost::program_options::options_description cnf_opts("CNF optimization options");
        cnf_opts.add_options()
            (
                "cnf-blocked-clause",
                boost::program_options::value<std::string>(),
                "blocked clause elimination is quarantined (only no is supported)"
            )
            (
                "cnf-duplicate-removal",
                boost::program_options::value<std::string>(),
                "enable duplicate clause removal (yes/no, default: yes)"
            )
            (
                "cnf-tautology-removal",
                boost::program_options::value<std::string>(),
                "enable tautology removal (yes/no, default: yes)"
            )
            (
                "cnf-self-subsumption",
                boost::program_options::value<std::string>(),
                "self-subsuming resolution is quarantined (only no is supported)"
            )
            (
                "cnf-subsumption",
                boost::program_options::value<std::string>(),
                "enable subsumption elimination (yes/no, default: no)"
            )
            (
                "cnf-variable-elimination",
                boost::program_options::value<std::string>(),
                "variable elimination is quarantined (only no is supported)"
            )
            (
                "cnf-microcode-directory",
                boost::program_options::value<std::string>(),
                "microcode directory (default: /microcode)"
            )
            ;

        // FSM options
        boost::program_options::options_description fsm_opts("FSM options");
        fsm_opts.add_options()
            (
                "fsm-inertial-checks",
                boost::program_options::value<std::string>(),
                "required mutual exclusiveness checks for inertial conditions (only yes is supported)"
            )
            ;

        // REACH options
        boost::program_options::options_description reach_opts("REACH options");
        reach_opts.add_options()
            (
                "reach-fast-backward-strategy",
                boost::program_options::value<std::string>(),
                "enable fast backward strategy (yes/no, default: yes)"
            )
            (
                "reach-backward-strategy",
                boost::program_options::value<std::string>(),
                "enable backward strategy (yes/no, default: yes)"
            )
            (
                "reach-fast-forward-strategy",
                boost::program_options::value<std::string>(),
                "enable fast forward strategy (yes/no, default: yes)"
            )
            (
                "reach-forward-strategy",
                boost::program_options::value<std::string>(),
                "enable forward strategy (yes/no, default: yes)"
            )
            ;

        boost::program_options::options_description sat_opts("CaDiCaL solver options");
        sat_opts.add_options()
            ("sat-random-seed", boost::program_options::value<int>(),
             "CaDiCaL random seed (integer 0..2000000000, default: 0)");
        for (const auto option : retired_sat_options)
            sat_opts.add_options()(option,
                boost::program_options::value<std::string>()->implicit_value(""),
                "removed MiniSat option; omit when using CaDiCaL");

        // Combine all option groups
        f_desc
            .add(general_opts)
            .add(cnf_opts)
            .add(fsm_opts)
            .add(reach_opts)
            .add(sat_opts);
        
        // clang-format on

        // positional arguments are models
        f_pos.add("model", -1);
    }

    void OptsMgr::parse_command_line(int argc, const char** argv)
    {
        boost::program_options::store(
            boost::program_options::command_line_parser(
                argc, const_cast<char**>(argv))
                .options(f_desc)
                .positional(f_pos)
                .run(),
            f_vm);

        boost::program_options::notify(f_vm);
        for (const auto option : retired_sat_options)
            if (f_vm.count(option))
                throw std::invalid_argument(std::string("Removed MiniSat option --") + option +
                    ": yasmv now uses CaDiCaL; omit this option. Only --sat-random-seed is retained.");
        if (sat_random_seed() < 0 || sat_random_seed() > 2000000000)
            throw std::invalid_argument("--sat-random-seed must be an integer in 0..2000000000");
        if (f_vm.count("solver-info")) {
            Json::Value info;
            info["name"] = "cadical";
            info["version"] = sat::Engine::solver_version();
            info["signature"] = sat::Engine::solver_signature();
            info["revision"] = CADICAL_BUILD_REVISION;
            info["linkage"] = "static";
            Json::StreamWriterBuilder writer;
            writer["indentation"] = "";
            std::cout << Json::writeString(writer, info) << std::endl;
            std::exit(0);
        }
        for (const char* option : {"cnf-blocked-clause", "cnf-variable-elimination",
                                   "cnf-self-subsumption", "cnf-subsumption",
                                   "cnf-tautology-removal", "cnf-duplicate-removal",
                                   "fsm-inertial-checks"}) {
            if (!f_vm.count(option)) continue;
            const auto value = f_vm[option].as<std::string>();
            if (!is_true(value) && value != "no" && value != "false" &&
                value != "0" && value != "off") {
                throw std::invalid_argument(std::string("Expected yes/no for --") + option);
            }
        }
        // These custom passes do not preserve the incremental solver contract.
        // Keep the options recognizable so existing scripts fail explicitly.
        for (const char* option : {"cnf-blocked-clause", "cnf-variable-elimination",
                                   "cnf-self-subsumption"}) {
            if (f_vm.count(option) && is_true(f_vm[option].as<std::string>())) {
                throw std::invalid_argument(std::string("Unsupported option --") + option +
                    " yes: this CNF pass is quarantined pending incremental correctness validation.");
            }
        }
        if (0 < f_vm.count("help")) {
            f_help = true;
        }

        if (0 < f_vm.count("version")) {
            std::cout
                << PACKAGE_VERSION
                << std::endl;

            exit(0);
        }

        if (0 < f_vm.count("quiet")) {
            f_quiet = true;
        }

        if (0 < f_vm.count("color")) {
            f_color = true;
        }
        
        if (0 < f_vm.count("fsm-inertial-checks")) {
            const auto inertial_value = f_vm["fsm-inertial-checks"].as<std::string>();
            if (!is_true(inertial_value)) {
                throw std::invalid_argument("Unsupported option --fsm-inertial-checks no: guard validation is required.");
            }
            f_skip_inertial_fsm_checks = ! is_true(inertial_value);
        } else {
            f_skip_inertial_fsm_checks = false; // Default: enabled (so skip = false)
        }

        f_started = true;
    }

    unsigned OptsMgr::verbosity() const
    {
        if (0 < f_vm.count("verbosity")) {
            return f_vm["verbosity"].as<unsigned>();
        }
        return DEFAULT_VERBOSITY;
    }

    bool OptsMgr::color() const
    {
        return f_color;
    }

    bool OptsMgr::quiet() const
    {
        return f_quiet;
    }

    void OptsMgr::set_word_width(unsigned value)
    {
        TRACE
            << "Setting word width to "
            << value
            << std::endl;

        f_word_width = value;
    }

    unsigned OptsMgr::word_width() const
    {
        if (UINT_MAX != f_word_width) {
            return f_word_width;
        }
        if (0 < f_vm.count("word-width")) {
            return f_vm["word-width"].as<unsigned>();
        }
        return DEFAULT_WORD_WIDTH;
    }



    std::string OptsMgr::model() const
    {
        std::string res;
        if (0 < f_vm.count("model")) {
            res = f_vm["model"].as<std::string>();
        }

        return res;
    }

    std::string OptsMgr::root() const
    {
        return f_vm.count("root") ? f_vm["root"].as<std::string>() : "";
    }

    bool OptsMgr::help() const
    {
        return f_help;
    }
    
    bool OptsMgr::skip_inertial_fsm_checks() const
    {
        return f_skip_inertial_fsm_checks;
    }

    bool OptsMgr::reach_fast_forward_strategy() const
    {
        if (0 < f_vm.count("reach-fast-forward-strategy")) {
            const auto value = f_vm["reach-fast-forward-strategy"].as<std::string>();
            return is_true(value);
        }
        return DEFAULT_REACH_FAST_FORWARD_STRATEGY;
    }

    bool OptsMgr::reach_forward_strategy() const
    {
        if (0 < f_vm.count("reach-forward-strategy")) {
            const auto value = f_vm["reach-forward-strategy"].as<std::string>();
            return is_true(value);
        }
        return DEFAULT_REACH_FORWARD_STRATEGY;
    }

    bool OptsMgr::reach_fast_backward_strategy() const
    {
        if (0 < f_vm.count("reach-fast-backward-strategy")) {
            const auto value = f_vm["reach-fast-backward-strategy"].as<std::string>();
            return is_true(value);
        }
        return DEFAULT_REACH_FAST_BACKWARD_STRATEGY;
    }

    bool OptsMgr::reach_backward_strategy() const
    {
        if (0 < f_vm.count("reach-backward-strategy")) {
            const auto value = f_vm["reach-backward-strategy"].as<std::string>();
            return is_true(value);
        }
        return DEFAULT_REACH_BACKWARD_STRATEGY;
    }

    int OptsMgr::sat_random_seed() const
    {
        return f_vm.count("sat-random-seed") ? f_vm["sat-random-seed"].as<int>() : DEFAULT_SAT_RANDOM_SEED;
    }
    
    
    bool OptsMgr::cnf_tautology_removal() const
    {
        if (0 < f_vm.count("cnf-tautology-removal")) {
            const auto value = f_vm["cnf-tautology-removal"].as<std::string>();
            return is_true(value);
        }
        return DEFAULT_CNF_TAUTOLOGY_REMOVAL;
    }
    
    bool OptsMgr::cnf_duplicate_removal() const
    {
        if (0 < f_vm.count("cnf-duplicate-removal")) {
            const auto value = f_vm["cnf-duplicate-removal"].as<std::string>();
            return is_true(value);
        }
        return DEFAULT_CNF_DUPLICATE_REMOVAL;
    }
    
    bool OptsMgr::cnf_subsumption() const
    {
        if (0 < f_vm.count("cnf-subsumption")) {
            const auto value = f_vm["cnf-subsumption"].as<std::string>();
            return is_true(value);
        }
        return false; // Default: disabled
    }
    
    bool OptsMgr::cnf_variable_elimination() const
    {
        if (0 < f_vm.count("cnf-variable-elimination")) {
            const auto value = f_vm["cnf-variable-elimination"].as<std::string>();
            return is_true(value);
        }
        return false; // Default: disabled
    }
    
    bool OptsMgr::cnf_self_subsumption() const
    {
        if (0 < f_vm.count("cnf-self-subsumption")) {
            const auto value = f_vm["cnf-self-subsumption"].as<std::string>();
            return is_true(value);
        }
        return false; // Default: disabled
    }
    
    bool OptsMgr::cnf_blocked_clause() const
    {
        if (0 < f_vm.count("cnf-blocked-clause")) {
            const auto value = f_vm["cnf-blocked-clause"].as<std::string>();
            return is_true(value);
        }
        return false; // Default: disabled
    }

    std::string OptsMgr::cnf_microcode_directory() const
    {
        if (0 < f_vm.count("cnf-microcode-directory")) {
            auto value = f_vm["cnf-microcode-directory"].as<std::string>();
            return value;
        }

        return DEFAULT_MICROCODE_DIRECTORY;
    }

    std::string OptsMgr::usage() const
    {
        std::ostringstream oss;
        oss << std::fixed << std::setprecision(2);
        oss << f_desc;
        return oss.str();
    }

    bool OptsMgr::is_true(const std::string& value)
    {
        return (value == "yes" || value == "true" || value == "1" || value == "on");
    }


    using namespace axter;
    verbosity OptsMgr::get_verbosity_level_tolerance() const
    {
        if (!f_started) {
            return log_often;
        }

        switch (verbosity()) {
            case 0:
                return log_always;

            case 1:
                return log_often;

            case 2:
                return log_regularly;

            case 3:
                return log_rarely;

            default:
                return log_very_rarely;
        }
    }

}; // namespace opts

std::string opts::OptsMgr::query_file() const { return f_vm.count("query-file") ? f_vm["query-file"].as<std::string>() : ""; }

std::string opts::OptsMgr::session_file() const { return f_vm.count("session-file") ? f_vm["session-file"].as<std::string>() : ""; }

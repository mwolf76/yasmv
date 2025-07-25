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

#include <opts_mgr.hh>

#include <utils/logging.hh>

namespace opts {

    // static initialization
    OptsMgr_ptr OptsMgr::f_instance = NULL;

    OptsMgr::OptsMgr()
        : f_desc("Program options")
        , f_pos()
        , f_vm()
        , f_help(false)
        , f_quiet(false)
        , f_color(false)
        , f_started(false)
        , f_version(false)
        , f_skip_inertial_fsm_checks(false)
        , f_word_width(UINT_MAX)
    {
        // clang-format off
        f_desc.add_options()
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
                boost::program_options::value<unsigned>()->default_value(DEFAULT_WORD_WIDTH),
                "native word size in bits"
            )

            (
                "verbosity",
                boost::program_options::value<unsigned>()->default_value(DEFAULT_VERBOSITY),
                "verbosity level"
            )

            (
                "model",
                boost::program_options::value<std::string>(),
                "input model"
            )
            
            (
                "skip-inertial-fsm-checks",
                "skip mutual exclusiveness checks for inertial FSM conditions (faster but potentially unsafe)"
            )
            
            (
                "sat-random-var-freq",
                boost::program_options::value<double>()->default_value(DEFAULT_SAT_RANDOM_VAR_FREQ),
                "SAT solver random variable frequency (0.0 = deterministic, higher = more random)"
            )
            
            (
                "sat-random-init-act",
                "enable SAT solver random initial activity (non-deterministic)"
            )
            
            (
                "sat-ccmin-mode",
                boost::program_options::value<int>()->default_value(DEFAULT_SAT_CCMIN_MODE),
                "SAT solver conflict clause minimization mode (0=none, 1=basic, 2=deep)"
            )
            
            (
                "sat-phase-saving",
                boost::program_options::value<int>()->default_value(DEFAULT_SAT_PHASE_SAVING),
                "SAT solver phase saving mode (0=none, 1=limited, 2=full)"
            )
            
            (
                "sat-garbage-frac",
                boost::program_options::value<double>()->default_value(DEFAULT_SAT_GARBAGE_FRAC),
                "SAT solver garbage collection fraction (0.0-1.0)"
            )
            
            (
                "cnf-optimization",
                "enable CNF optimization (may improve or worsen performance)"
            )
            
            (
                "cnf-no-tautology-removal",
                "disable tautology removal in CNF optimization"
            )
            
            (
                "cnf-no-duplicate-removal",
                "disable duplicate clause removal in CNF optimization"
            )
            
            (
                "cnf-no-subsumption",
                "disable subsumption elimination in CNF optimization"
            )
            
            (
                "cnf-no-variable-elimination",
                "disable variable elimination in CNF optimization"
            )
            
            (
                "cnf-no-self-subsumption",
                "disable self-subsuming resolution in CNF optimization"
            )
            
            (
                "cnf-no-blocked-clause",
                "disable blocked clause elimination in CNF optimization"
            )
            ;
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
        if (f_vm.count("help")) {
            f_help = true;
        }

        if (f_vm.count("version")) {
            std::cout
                << PACKAGE_VERSION
                << std::endl;

            exit(0);
        }

        if (f_vm.count("quiet")) {
            f_quiet = true;
        }

        if (f_vm.count("color")) {
            f_color = true;
        }
        
        if (f_vm.count("skip-inertial-fsm-checks")) {
            f_skip_inertial_fsm_checks = true;
        }

        f_started = true;
    }

    unsigned OptsMgr::verbosity() const
    {
        unsigned res { f_vm["verbosity"].as<unsigned>() };
        return res;
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
        return (UINT_MAX != f_word_width) ? f_word_width
                                          : f_vm["word-width"].as<unsigned>();
    }



    std::string OptsMgr::model() const
    {
        std::string res { "" };
        if (f_vm.count("model")) {
            res = f_vm["model"].as<std::string>();
        }

        return res;
    }

    bool OptsMgr::help() const
    {
        return f_help;
    }
    
    bool OptsMgr::skip_inertial_fsm_checks() const
    {
        return f_skip_inertial_fsm_checks;
    }
    
    double OptsMgr::sat_random_var_freq() const
    {
        return f_vm["sat-random-var-freq"].as<double>();
    }
    
    bool OptsMgr::sat_random_init_act() const
    {
        return f_vm.count("sat-random-init-act") > 0;
    }
    
    int OptsMgr::sat_ccmin_mode() const
    {
        return f_vm["sat-ccmin-mode"].as<int>();
    }
    
    int OptsMgr::sat_phase_saving() const
    {
        return f_vm["sat-phase-saving"].as<int>();
    }
    
    double OptsMgr::sat_garbage_frac() const
    {
        return f_vm["sat-garbage-frac"].as<double>();
    }
    
    bool OptsMgr::cnf_optimization() const
    {
        return f_vm.count("cnf-optimization") > 0;
    }
    
    bool OptsMgr::cnf_no_tautology_removal() const
    {
        return f_vm.count("cnf-no-tautology-removal") > 0;
    }
    
    bool OptsMgr::cnf_no_duplicate_removal() const
    {
        return f_vm.count("cnf-no-duplicate-removal") > 0;
    }
    
    bool OptsMgr::cnf_no_subsumption() const
    {
        return f_vm.count("cnf-no-subsumption") > 0;
    }
    
    bool OptsMgr::cnf_no_variable_elimination() const
    {
        return f_vm.count("cnf-no-variable-elimination") > 0;
    }
    
    bool OptsMgr::cnf_no_self_subsumption() const
    {
        return f_vm.count("cnf-no-self-subsumption") > 0;
    }
    
    bool OptsMgr::cnf_no_blocked_clause() const
    {
        return f_vm.count("cnf-no-blocked-clause") > 0;
    }

    std::string OptsMgr::usage() const
    {
        std::ostringstream oss;
        oss << f_desc;
        return oss.str();
    }


    using namespace axter;
    verbosity OptsMgr::get_verbosity_level_tolerance()
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

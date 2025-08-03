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

#include <utils/logging.hh>

namespace opts {

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
            ;

        // CNF optimization options
        boost::program_options::options_description cnf_opts("CNF optimization options");
        cnf_opts.add_options()
            (
                "cnf-blocked-clause",
                boost::program_options::value<std::string>(),
                "enable blocked clause elimination (yes/no, default: no)"
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
                "enable self-subsuming resolution (yes/no, default: no)"
            )
            (
                "cnf-subsumption",
                boost::program_options::value<std::string>(),
                "enable subsumption elimination (yes/no, default: no)"
            )
            (
                "cnf-variable-elimination",
                boost::program_options::value<std::string>(),
                "enable variable elimination (yes/no, default: no)"
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
                "enable mutual exclusiveness checks for inertial conditions (yes/no, default: yes)"
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

        // SAT solver options
        boost::program_options::options_description sat_opts("SAT solver options");
        sat_opts.add_options()
            (
                "sat-ccmin-mode",
                boost::program_options::value<int>(),
                "conflict clause minimization mode (0=none, 1=basic, 2=deep, default: 2)"
            )
            (
                "sat-garbage-frac",
                boost::program_options::value<double>(),
                "garbage collection fraction (0.0-1.0, default: 0.30)"
            )
            (
                "sat-phase-saving",
                boost::program_options::value<int>(),
                "phase saving mode (0=none, 1=limited, 2=full, default: 2)"
            )
            (
                "sat-random-init-act",
                boost::program_options::value<std::string>(),
                "enable random initial activity (yes/no, default: yes)"
            )
            (
                "sat-random-var-freq",
                boost::program_options::value<double>(),
                "random variable frequency (0.0 = deterministic, higher = more random, default: 0.02)"
            )
            (
                "sat-var-decay",
                boost::program_options::value<double>(),
                "variable activity decay factor (0.0-1.0, default: 0.95)"
            )
            (
                "sat-clause-decay",
                boost::program_options::value<double>(),
                "clause activity decay factor (0.0-1.0, default: 0.999)"
            )
            (
                "sat-random-seed",
                boost::program_options::value<double>(),
                "random seed for SAT solver (default: 91648253)"
            )
            (
                "sat-luby-restart",
                boost::program_options::value<std::string>(),
                "use Luby restart sequence (yes/no, default: no)"
            )
            (
                "sat-restart-first",
                boost::program_options::value<int>(),
                "base restart interval in conflicts (default: 100)"
            )
            (
                "sat-restart-inc",
                boost::program_options::value<double>(),
                "restart interval multiplier for geometric restarts (default: 2.0)"
            )
            (
                "sat-elim",
                boost::program_options::value<std::string>(),
                "enable variable elimination preprocessing (yes/no, default: yes)"
            )
            (
                "sat-rcheck",
                boost::program_options::value<std::string>(),
                "check if clauses are already implied (yes/no, default: no)"
            )
            (
                "sat-asymm",
                boost::program_options::value<std::string>(),
                "shrink clauses by asymmetric branching (yes/no, default: no)"
            )
            (
                "sat-grow",
                boost::program_options::value<int>(),
                "allow formula growth during elimination (default: 0)"
            )
            (
                "sat-clause-lim",
                boost::program_options::value<int>(),
                "skip elimination producing long clauses (default: 20)"
            )
            (
                "sat-subsumption-lim",
                boost::program_options::value<int>(),
                "skip subsumption check for large clauses (default: 1000)"
            )
            (
                "sat-simp-garbage-frac",
                boost::program_options::value<double>(),
                "garbage collection fraction during simplification (default: 0.5)"
            )
            ;

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
        if (f_vm.contains("help")) {
            f_help = true;
        }

        if (f_vm.contains("version")) {
            std::cout
                << PACKAGE_VERSION
                << std::endl;

            exit(0);
        }

        if (f_vm.contains("quiet")) {
            f_quiet = true;
        }

        if (f_vm.contains("color")) {
            f_color = true;
        }
        
        if (f_vm.contains("fsm-inertial-checks")) {
            const auto inertial_value = f_vm["fsm-inertial-checks"].as<std::string>();
            f_skip_inertial_fsm_checks = ! is_true(inertial_value);
        } else {
            f_skip_inertial_fsm_checks = false; // Default: enabled (so skip = false)
        }

        f_started = true;
    }

    unsigned OptsMgr::verbosity() const
    {
        if (f_vm.contains("verbosity")) {
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
        if (f_vm.contains("word-width")) {
            return f_vm["word-width"].as<unsigned>();
        }
        return DEFAULT_WORD_WIDTH;
    }



    std::string OptsMgr::model() const
    {
        std::string res;
        if (f_vm.contains("model")) {
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

    bool OptsMgr::reach_fast_forward_strategy() const
    {
        if (f_vm.contains("reach-fast-forward-strategy")) {
            const auto value = f_vm["reach-fast-forward-strategy"].as<std::string>();
            return is_true(value);
        }
        return DEFAULT_REACH_FAST_FORWARD_STRATEGY;
    }

    bool OptsMgr::reach_forward_strategy() const
    {
        if (f_vm.contains("reach-forward-strategy")) {
            const auto value = f_vm["reach-forward-strategy"].as<std::string>();
            return is_true(value);
        }
        return DEFAULT_REACH_FORWARD_STRATEGY;
    }

    bool OptsMgr::reach_fast_backward_strategy() const
    {
        if (f_vm.contains("reach-fast-backward-strategy")) {
            const auto value = f_vm["reach-fast-backward-strategy"].as<std::string>();
            return is_true(value);
        }
        return DEFAULT_REACH_FAST_BACKWARD_STRATEGY;
    }

    bool OptsMgr::reach_backward_strategy() const
    {
        if (f_vm.contains("reach-backward-strategy")) {
            const auto value = f_vm["reach-backward-strategy"].as<std::string>();
            return is_true(value);
        }
        return DEFAULT_REACH_BACKWARD_STRATEGY;
    }

    double OptsMgr::sat_random_var_freq() const
    {
        if (f_vm.contains("sat-random-var-freq")) {
            return f_vm["sat-random-var-freq"].as<double>();
        }
        return DEFAULT_SAT_RANDOM_VAR_FREQ;
    }

    bool OptsMgr::sat_random_init_act() const
    {
        if (f_vm.contains("sat-random-init-act")) {
            const auto value = f_vm["sat-random-init-act"].as<std::string>();
            return is_true(value);
        }
        return DEFAULT_SAT_RANDOM_INIT_ACT;
    }
    
    int OptsMgr::sat_ccmin_mode() const
    {
        if (f_vm.contains("sat-ccmin-mode")) {
            return f_vm["sat-ccmin-mode"].as<int>();
        }
        return DEFAULT_SAT_CCMIN_MODE;
    }
    
    int OptsMgr::sat_phase_saving() const
    {
        if (f_vm.contains("sat-phase-saving")) {
            return f_vm["sat-phase-saving"].as<int>();
        }
        return DEFAULT_SAT_PHASE_SAVING;
    }
    
    double OptsMgr::sat_garbage_frac() const
    {
        if (f_vm.contains("sat-garbage-frac")) {
            return f_vm["sat-garbage-frac"].as<double>();
        }
        return DEFAULT_SAT_GARBAGE_FRAC;
    }
    
    double OptsMgr::sat_var_decay() const
    {
        if (f_vm.contains("sat-var-decay")) {
            return f_vm["sat-var-decay"].as<double>();
        }
        return DEFAULT_SAT_VAR_DECAY;
    }
    
    double OptsMgr::sat_clause_decay() const
    {
        if (f_vm.contains("sat-clause-decay")) {
            return f_vm["sat-clause-decay"].as<double>();
        }
        return DEFAULT_SAT_CLAUSE_DECAY;
    }
    
    double OptsMgr::sat_random_seed() const
    {
        if (f_vm.contains("sat-random-seed")) {
            return f_vm["sat-random-seed"].as<double>();
        }
        return DEFAULT_SAT_RANDOM_SEED;
    }
    
    bool OptsMgr::sat_luby_restart() const
    {
        if (f_vm.contains("sat-luby-restart")) {
            const auto value = f_vm["sat-luby-restart"].as<std::string>();
            return is_true(value);
        }
        return DEFAULT_SAT_LUBY_RESTART;
    }
    
    int OptsMgr::sat_restart_first() const
    {
        if (f_vm.contains("sat-restart-first")) {
            return f_vm["sat-restart-first"].as<int>();
        }
        return DEFAULT_SAT_RESTART_FIRST;
    }
    
    double OptsMgr::sat_restart_inc() const
    {
        if (f_vm.contains("sat-restart-inc")) {
            return f_vm["sat-restart-inc"].as<double>();
        }
        return DEFAULT_SAT_RESTART_INC;
    }
    
    bool OptsMgr::sat_elim() const
    {
        if (f_vm.contains("sat-elim")) {
            const auto value = f_vm["sat-elim"].as<std::string>();
            return is_true(value);
        }
        return DEFAULT_SAT_ELIM;
    }
    
    bool OptsMgr::sat_rcheck() const
    {
        if (f_vm.contains("sat-rcheck")) {
            const auto value = f_vm["sat-rcheck"].as<std::string>();
            return is_true(value);
        }
        return DEFAULT_SAT_RCHECK;
    }
    
    bool OptsMgr::sat_asymm() const
    {
        if (f_vm.contains("sat-asymm")) {
            const auto value = f_vm["sat-asymm"].as<std::string>();
            return is_true(value);
        }
        return DEFAULT_SAT_ASYMM;
    }
    
    int OptsMgr::sat_grow() const
    {
        if (f_vm.contains("sat-grow")) {
            return f_vm["sat-grow"].as<int>();
        }
        return DEFAULT_SAT_GROW;
    }
    
    int OptsMgr::sat_clause_lim() const
    {
        if (f_vm.contains("sat-clause-lim")) {
            return f_vm["sat-clause-lim"].as<int>();
        }
        return DEFAULT_SAT_CLAUSE_LIM;
    }
    
    int OptsMgr::sat_subsumption_lim() const
    {
        if (f_vm.contains("sat-subsumption-lim")) {
            return f_vm["sat-subsumption-lim"].as<int>();
        }
        return DEFAULT_SAT_SUBSUMPTION_LIM;
    }
    
    double OptsMgr::sat_simp_garbage_frac() const
    {
        if (f_vm.contains("sat-simp-garbage-frac")) {
            return f_vm["sat-simp-garbage-frac"].as<double>();
        }
        return DEFAULT_SAT_SIMP_GARBAGE_FRAC;
    }
    
    
    bool OptsMgr::cnf_tautology_removal() const
    {
        if (f_vm.contains("cnf-tautology-removal")) {
            const auto value = f_vm["cnf-tautology-removal"].as<std::string>();
            return is_true(value);
        }
        return DEFAULT_CNF_TAUTOLOGY_REMOVAL;
    }
    
    bool OptsMgr::cnf_duplicate_removal() const
    {
        if (f_vm.contains("cnf-duplicate-removal")) {
            const auto value = f_vm["cnf-duplicate-removal"].as<std::string>();
            return is_true(value);
        }
        return DEFAULT_CNF_DUPLICATE_REMOVAL;
    }
    
    bool OptsMgr::cnf_subsumption() const
    {
        if (f_vm.contains("cnf-subsumption")) {
            const auto value = f_vm["cnf-subsumption"].as<std::string>();
            return is_true(value);
        }
        return false; // Default: disabled
    }
    
    bool OptsMgr::cnf_variable_elimination() const
    {
        if (f_vm.contains("cnf-variable-elimination")) {
            const auto value = f_vm["cnf-variable-elimination"].as<std::string>();
            return is_true(value);
        }
        return false; // Default: disabled
    }
    
    bool OptsMgr::cnf_self_subsumption() const
    {
        if (f_vm.contains("cnf-self-subsumption")) {
            const auto value = f_vm["cnf-self-subsumption"].as<std::string>();
            return is_true(value);
        }
        return false; // Default: disabled
    }
    
    bool OptsMgr::cnf_blocked_clause() const
    {
        if (f_vm.contains("cnf-blocked-clause")) {
            const auto value = f_vm["cnf-blocked-clause"].as<std::string>();
            return is_true(value);
        }
        return false; // Default: disabled
    }

    std::string OptsMgr::cnf_microcode_directory() const
    {
        if (f_vm.contains("cnf-microcode-directory")) {
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

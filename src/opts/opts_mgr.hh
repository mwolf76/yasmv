/**
 * @file opts.hh
 * @brief Command line options management
 *
 * This header file contains the declarations required by the options
 * management system.
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

#ifndef OPTS_H
#define OPTS_H

#include <boost/program_options.hpp>

#include <common/common.hh>
#include <3rdparty/ezlogger/ezlogger_verbosity_level_policy.hpp>

namespace opts {

    class OptsMgr;
    typedef OptsMgr* OptsMgr_ptr;

    // -- system defaults
    const unsigned DEFAULT_WORD_WIDTH { 16 };
    const unsigned DEFAULT_VERBOSITY { 0 };

    // -- CNF defaults
    const bool DEFAULT_CNF_DUPLICATE_REMOVAL { true };
    const bool DEFAULT_CNF_TAUTOLOGY_REMOVAL { true };
    const std::string DEFAULT_MICROCODE_DIRECTORY { "/microcode" };

    // -- SAT defaults
    const double DEFAULT_SAT_RANDOM_VAR_FREQ { 0.02 };  // 2% randomization for performance
    const bool DEFAULT_SAT_RANDOM_INIT_ACT { true };  // Randomized initial activities for performance
    const int DEFAULT_SAT_CCMIN_MODE { 2 };  // Deep conflict clause minimization for performance
    const int DEFAULT_SAT_PHASE_SAVING { 2 };  // Full phase saving for performance
    const double DEFAULT_SAT_GARBAGE_FRAC { 0.30 };  // Higher threshold for better performance in model checking

    // -- REACH defaults
    const bool DEFAULT_REACH_FAST_FORWARD_STRATEGY { true };
    const bool DEFAULT_REACH_FORWARD_STRATEGY { true };
    const bool DEFAULT_REACH_FAST_BACKWARD_STRATEGY { true };
    const bool DEFAULT_REACH_BACKWARD_STRATEGY { true };

    class OptsMgr {

    public:
        static OptsMgr& INSTANCE()
        {
            if (!f_instance)
                f_instance = new OptsMgr();

            return (*f_instance);
        }

        // the usage message
        std::string usage() const;

        // true iff help has been required
        bool help() const;

        // level of verbosity
        unsigned verbosity() const;

        // quiet
        bool quiet() const;

        // colorized
        bool color() const;

        // native word size in bits, used for algebrization of constant ITEs and arrays
        unsigned word_width() const;
        void set_word_width(unsigned);

        // model filename
        std::string model() const;
        
        // skip inertial FSM checks
        bool skip_inertial_fsm_checks() const;

        // REACH strategies
        bool reach_fast_forward_strategy() const;
        bool reach_fast_backward_strategy() const;
        bool reach_forward_strategy() const;
        bool reach_backward_strategy() const;

        // SAT solver configuration
        double sat_random_var_freq() const;
        static bool is_true(const std::string& value) ;
        bool sat_random_init_act() const;
        int sat_ccmin_mode() const;
        int sat_phase_saving() const;
        double sat_garbage_frac() const;
        
        // CNF optimization configuration
        bool cnf_tautology_removal() const;
        bool cnf_duplicate_removal() const;
        bool cnf_subsumption() const;
        bool cnf_variable_elimination() const;
        bool cnf_self_subsumption() const;
        bool cnf_blocked_clause() const;

        // CNF microcode configuration
        std::string cnf_microcode_directory() const;

        // to be invoked by main
        void parse_command_line(int argc, const char** argv);

        // delegate
        axter::verbosity get_verbosity_level_tolerance() const;

    protected:
        OptsMgr();

    private:
        static OptsMgr_ptr f_instance;

        /* local data */
        boost::program_options::options_description f_desc;
        boost::program_options::positional_options_description f_pos;
        boost::program_options::variables_map f_vm;

        bool f_help;
        bool f_quiet;
        bool f_color;
        bool f_started;
        bool f_version;
        bool f_skip_inertial_fsm_checks;

        unsigned f_word_width;
    };

}; // namespace opts

#endif

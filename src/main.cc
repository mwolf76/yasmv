/**
 * @file main.cc
 * @brief Program main body
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
 * @mainpage yasmv - Yet Another Symbolic Model Verifier
 * @author Marco Pensallorto < marco DOT pensallorto AT gmail DOT com>\n
 * Copyright (C) 2011-2016\n
 * @section DownloadSourceCode Download
 * Source code is available on Github:\n
 * https://github.com/mwolf76/yasmv
 * \n\n
 *
 * <H1><CENTER>Overview</CENTER></H1>yasmv (Yet Another Symbolic Model Verifier)
 * started off in fall 2011 as a tentative and partial C++ reimplementation of
 * the NuSMV2 model checker. As a former member of the NuSMV2 development team
 * (in the years from 2008 to 2011), I was never happy with a few architectural
 * choices that were inherited from the long history of the NuSMV model checker
 * and/or were due to the amount of legacy code and tools that relied on its
 * "peculiar" behavior. Don't get me wrong, I really think NuSMV is a great
 * piece of software. And I owe to the developers and researchers in FBK most -
 * if not all - of my scientific and software engineering training. It's just
 * that I have been wondering for years what that project would have been like,
 * if one was completely free to redesign it all from-the-scratch. This is
 * exactly why this project exists in the first place.
 *
 **/

#include <cmd/cmd.hh>

#include <expr/expr.hh>
#include <expr/printer/printer.hh>

#include <model/model.hh>

#include <opts/opts_mgr.hh>

#include <parser/grammars/smvLexer.h>
#include <parser/grammars/smvParser.h>

#include <sat/sat.hh>

#include <boost/chrono.hpp>

static const std::string heading_msg =
    "yasmv - Yet Another Symbolic Model Verifier\n"
    "(c) 2011-2018, Marco Pensallorto < marco DOT pensallorto AT gmail DOT com >\n"
    "https://github.com/mwolf76/yasmv\n";

/* printing helpers: these functions are unused in the code, they're
   here just for debugging purposes withing gdb */
void pe(Expr_ptr e)
{ std::cerr << e << std::endl; }

void pf(TimedExpr e)
{ std::cerr << e << std::endl; }

void pu(UCBI& ucbi)
{ std::cerr << ucbi << std::endl; }

void pt(TCBI& tcbi)
{ std::cerr << tcbi << std::endl; }

void pd(InlinedOperatorDescriptor& md)
{ std::cerr << md << std::endl; }

void batch(Command_ptr cmd)
{
    Interpreter& system = Interpreter::INSTANCE();
    OptsMgr& opts_mgr = OptsMgr::INSTANCE();

    bool quiet { opts_mgr.quiet() };
    bool color { opts_mgr.color() };

    /* In batch mode, we print res unless in quiet mode */
    Variant& res = system(cmd);
    if (! quiet) {
        if (color) {
            std::cout
                << std::endl
                << yellow
                << "<< "
                << res
                << normal << std::endl;
        }
        else {
            std::cout << std::endl << "<< " << res
                      << std::endl;
        }
    }
}

void sighandler(int signum)
{
    static boost::chrono::system_clock::time_point last;

    /* A single Control-Z requires current solving stats. Double
       Control-Z (within 1 sec) requires interruption */
    if (signum == SIGTSTP) {

        EngineMgr& mgr
            (EngineMgr::INSTANCE());

        std::cerr
            << std::endl;

        boost::chrono::system_clock::time_point now
            (boost::chrono::system_clock::now());

        boost::chrono::duration<double> sec
            (boost::chrono::system_clock::now() - last);

        if (sec.count() < 1.00) {
            std::cerr
                << "Interrupting all active threads (this may take a while)..."
                << std::endl;

            mgr.interrupt();
        }
        else {
            mgr.dump_stats(std::cerr);
            last = now;
        }
    }
}

int main(int argc, const char *argv[])
{
    Interpreter& interpreter
        (Interpreter::INSTANCE());

    /* you may also prefer sigaction() instead of signal() */
    signal(SIGTSTP, sighandler);

    try {
        /* parse command line options */
        OptsMgr& opts_mgr = OptsMgr::INSTANCE();
        opts_mgr.parse_command_line(argc, argv);

        if (opts_mgr.help()) {
            std::cout
                << OptsMgr::INSTANCE().usage()
                << std::endl ;

            exit(0);
        }

        if (! opts_mgr.quiet()) {
            std::cout
                << heading_msg
                << std::endl;
        }

        /* load microcode */
        InlinedOperatorMgr& mm
            (InlinedOperatorMgr::INSTANCE());

        size_t nloaders { mm.loaders().size() };

        if (! opts_mgr.quiet()) {
            TRACE
                << nloaders
                << " microcode fragments registered."
                << std::endl;
        }

        /* run options-generated commands (if any) */
        const std::string model_filename = opts_mgr.model();
        if (! model_filename.empty()) {
            ReadModel* cmd
                (reinterpret_cast<ReadModel*>
                 (CommandMgr::INSTANCE().make_read_model()));

            cmd->set_input( model_filename.c_str());
            batch(cmd);
        }

        /* run interactive commands */
        do {
            interpreter();
        } while (! interpreter.is_leaving());

        if (isatty(STDIN_FILENO))
            std::cout << std::endl;
    }

    catch (Exception &e) {
        std::cerr
            << red
            << "Uncaught exception!! "
            << e.what()
            << normal
            << std::endl;
    }

    return interpreter.retcode();

};

/* logging subsystem settings */
namespace axter {
    std::string get_log_prefix_format(const char*FileName,
                                      int LineNo, const char*FunctionName,
                                      ext_data levels_format_usage_data) {

        return ezlogger_format_policy::
            get_log_prefix_format(FileName, LineNo, FunctionName,
                                  levels_format_usage_data);
    }

    std::ostream& get_log_stream() {
        return ezlogger_output_policy::get_log_stream();
    }

    /* delegated to OptsMgr */
    verbosity get_verbosity_level_tolerance() {
        return OptsMgr::INSTANCE().get_verbosity_level_tolerance();
    }
};

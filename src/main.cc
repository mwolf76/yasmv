/**
 * @file main.cc
 * @brief Program main body
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 **/
#include <common.hh>

#include <cmd.hh>

#include <expr.hh>
#include <expr_printer.hh>

#include <model.hh>
#include <analyzer.hh>

#include <mc.hh>
#include <satbmc.hh>

#include <opts.hh>

#include <smvLexer.h>
#include <smvParser.h>

#include <logging.hh>

static const string heading_msg = \
                  "gnuSMV - A Symbolic model checker\n"
                  "(c) 2012, Marco Pensallorto < marco DOT pensallorto AT gmail DOT com >\n";

static void heading()
{ cout << heading_msg << endl; }

static void usage()
{
    cout << OptsMgr::INSTANCE().usage()
         << endl ;
}

// just for debugging purposes withing gdb
static void pe(Expr_ptr e)
{ DEBUG << e << endl; }

static void pf(FQExpr& e)
{ DEBUG << e << endl; }

static void pu(UCBI& ucbi)
{ DEBUG << ucbi << endl; }

static void pt(TCBI& tcbi)
{ DEBUG << tcbi << endl; }

int main(int argc, const char *argv[])
{
    heading();

    // parse command line options
    OptsMgr& opts_mgr = OptsMgr::INSTANCE();
    opts_mgr.parse_command_line(argc, argv);

    if (opts_mgr.help()) {
        usage();
        exit(0);
    }

    // Run command interpreter subsystem
    Interpreter& system = Interpreter::INSTANCE();

    // Run options-generated commands (if any)
    const string model_filename = opts_mgr.model();
    if (! model_filename.empty()) {
        Command_ptr cmd = CommandMgr::INSTANCE().make_load_model(model_filename.c_str());
        Variant& res = system(cmd);
        cerr << res << endl;
    }

    // interactive cmd loop
    do {
        Variant& res = system();
        cerr << res << endl;
    } while (! system.is_leaving());

    return system.retcode();
}

// logging subsystem settings
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

    // delegated to OptsMgr
    verbosity get_verbosity_level_tolerance() {
        return OptsMgr::INSTANCE().get_verbosity_level_tolerance();
    }
};

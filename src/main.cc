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

// logger configuration, has to be inlined in main
#include "logging.cc"

// options management
#include "opts.hh"

#include <smvLexer.h>
#include <smvParser.h>

// these are needed to force linking of modules
extern void link_expr();
extern void link_model();

ostream& operator<<(ostream& os, const Expr_ptr t)
{ Printer (os) << t; return os; }

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

// TODO: proper error handling
void parseFile(const char* fName)
{
    pANTLR3_INPUT_STREAM input;
    pANTLR3_COMMON_TOKEN_STREAM tstream;

    psmvParser psr;
    psmvLexer  lxr;

    DEBUG << "Preparing for parsing file '" << fName << "'" << endl;

    input = antlr3AsciiFileStreamNew((pANTLR3_UINT8) fName);
    if (NULL == input) {
        throw FileInputException(fName);
    }

    lxr = smvLexerNew(input); // smvLexerNew is generated by ANTLR
    assert(lxr);

    tstream = antlr3CommonTokenStreamSourceNew(ANTLR3_SIZE_HINT, TOKENSOURCE(lxr));
    assert(tstream);

    psr = smvParserNew(tstream);  // smvParserNew is generated by ANTLR3
    assert(psr);

    psr->smv(psr);

    psr->free(psr);
    tstream->free(tstream);
    lxr->free(lxr);
    input->close(input);
}

// TODO: proper error handling
ICommand_ptr parseCommand(const char *command)
{
    pANTLR3_INPUT_STREAM input;
    pANTLR3_COMMON_TOKEN_STREAM tstream;

    psmvParser psr;
    psmvLexer  lxr;

    DEBUG << "Preparing for parsing command '" << command << "'" << endl;

    input = antlr3NewAsciiStringInPlaceStream((pANTLR3_UINT8) command, strlen(command), NULL);
    assert(input);

    lxr = smvLexerNew(input); // smvLexerNew is generated by ANTLR
    assert(lxr);

    tstream = antlr3CommonTokenStreamSourceNew(ANTLR3_SIZE_HINT, TOKENSOURCE(lxr));
    assert(tstream);

    psr = smvParserNew(tstream);  // smvParserNew is generated by ANTLR3
    assert(psr);

    ICommand_ptr res = psr->cmd(psr);

    psr->free(psr);
    tstream->free(tstream);
    lxr->free(lxr);
    input->close(input);

    return res;
}

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
    do {
        Variant& res = system();
        cerr << res << endl;
    } while (! system.is_leaving());

    return system.retcode();
}

// int main(int argc, const char *argv[])
// {
//     // hack
//     link_expr();


//     try {
//         const char* fname = opts_mgr.model().c_str();
//         if (0 == strlen(fname)) {
//             usage();
//             exit(0);
//         }
//         parseFile((pANTLR3_UINT8) fname);

//         Printer prn(cout);

//         IModel& M(ModelMgr::INSTANCE().model());

//         Analyzer analyzer;
//         analyzer.process();

//         // Expr_ptr invspec = M.invspecs[0];

//         SATBMCFalsification alg(M, invspec);
//         alg.set_param("k", 10);
//         alg.set_param("incremental", true);
//         // assert(! alg.get_param("incremental").as_boolean());
//         // other params...

//         alg.process(); // TODO support for multiprocessing sync, etc...
//         if (alg.has_witness()) {
//             // const Traces& t = alg.get_traces();

//             // maybe print them
//         }

//         // for (Modules::iterator eye = M.modules.begin(); eye != M.modules.end(); eye ++ ) {
//         //     IModule_ptr pm = eye->second;
//         //     {
//         //         Module& m = dynamic_cast <Module&> (*pm);
//         //         //      const Expr_ptr module_name = m.expr();

//         //         prn << "Module name: "<< m.expr() << "\n";
//         //         const Variables& svars = m.get_localVars();

//         //         prn << "Variables: " << "\n";
//         //         for (Variables::const_iterator veye = svars.begin();
//         //              veye != svars.end(); veye ++ ) {

//         //             IVariable* tmp = veye->second;

//         //             if (StateVar* vp = dynamic_cast<StateVar*> (tmp) ){
//         //                 const StateVar& v = (*vp);
//         //                 prn << v.expr(); cout << endl;
//         //             }
//         //         }
//         //     }
//         // }
//     }

//     catch(Exception& e) {
//         cerr << "error: " << e.what() << "\n";
//         return 1;
//     }

//     return 0;
// }

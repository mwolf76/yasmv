/**
 * @file interpreter.cc
 * @brief Command interpreter subsystem, Interpreter class implementation.
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

#include <config.h>

#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <sstream>

#include <interpreter.hh>

#include <cmd/readline.h.inc>
#include <commands/commands.hh>

#include <parse.hh>
#include <workbench.hh>

#include <utils/logging.hh>

namespace cmd {

    /* A static variable for holding the line. */
    static char* line_buf = NULL;

    /* Read a string, and return a pointer to it.  Returns NULL on
       EOF. */
    static char* rl_gets()
    {
        opts::OptsMgr& om(opts::OptsMgr::INSTANCE());

        /* If the buffer has already been allocated, return the memory
           to the free pool. */
        if (NULL != line_buf) {
            free(line_buf);
            line_buf = NULL;
        }

        /* Get a line from the user. */
        line_buf = readline(om.quiet() ? NULL : ">> ");

        /* If the line has any text in it, save it on the history. */
        if (line_buf && *line_buf) {
            add_history(line_buf);
        }

        return line_buf;
    }

    Interpreter_ptr Interpreter::f_instance = NULL;
    Interpreter& Interpreter::INSTANCE()
    {
        if (!f_instance) {
            f_instance = new Interpreter();
        }

        return *f_instance;
    }

    Interpreter::Interpreter()
        : f_retcode(0)
        , f_leaving(false)

        // default I/O streams
        , f_in(&std::cin)
        , f_out(&std::cout)
        , f_err(&std::cerr)
    {
        const void* instance { this };

        clock_gettime(CLOCK_MONOTONIC, &f_epoch);

        DEBUG
            << "Initialized Interpreter @"
            << instance
            << std::endl;
    }

    Interpreter::~Interpreter()
    {
        const void* instance { this };

        DEBUG
            << "Destroyed Interpreter @"
            << instance
            << std::endl;
    }

    void Interpreter::quit(int retcode)
    {
        if (f_retcode == 0 || retcode != 0) {
            f_retcode = retcode;
        }
        f_leaving = true;
    }

    void Interpreter::record_error(int code)
    {
        if (!isatty(STDIN_FILENO) && f_retcode == 0) {
            f_retcode = code;
        }
    }

    extern CommandVector_ptr parseCommand(const char* command_line);
    utils::Variant& Interpreter::operator()(Command_ptr cmd)
    {
        assert(NULL != cmd);

        try {
            f_last_result = (*cmd)();
        }

        catch (Exception& e) {
            err()
                << "Exception!! "
                << e.what()
                << std::endl;

            f_last_result = utils::Variant(errMessage);
            record_error();
        }
        catch (const std::invalid_argument& e) {
            err() << "Error: " << e.what() << std::endl;
            f_last_result = utils::Variant(errMessage);
            record_error(2);
        }
        catch (const std::exception& e) {
            err() << "Error: " << e.what() << std::endl;
            f_last_result = utils::Variant(errMessage);
            record_error(4);
        }

        if (is_unknown(f_last_result)) {
            record_error(3);
        }

        delete cmd; /* claims ownership! */
        return f_last_result;
    }

    utils::Variant& Interpreter::operator()()
    {
        char* cmdline { NULL };
        std::string batch_line;
        if (isatty(STDIN_FILENO)) {
            cmdline = rl_gets();
        } else {
            if (std::getline(*f_in, batch_line)) {
                cmdline = batch_line.data();
            }
        }

        if (cmdline != NULL) {
            // getline/readline already remove the newline. Empty lines are valid.
            if (cmdline && 0 < strlen(cmdline)) {
                try {
                    CommandVector_ptr cmds { parse::parseCommand(cmdline) };
                    if (cmds) {
                        for (CommandVector::const_iterator i = cmds->begin();
                             cmds->end() != i; ++i) {

                            Command_ptr cmd { *i };
                            if (!is_leaving()) {
                                (*this)(cmd);
                            } else {
                                delete cmd;
                            }
                        }
                        delete cmds;
                    } else {
                        f_last_result = utils::Variant(errMessage);
                        record_error();
                    }
                } catch (Exception& e) {
                    std::string what { e.what() };
                    ERR
                        << what
                        << std::endl;

                    f_last_result = utils::Variant(errMessage);
                    record_error();
                } catch (const std::invalid_argument& e) {
                    err() << "Error: " << e.what() << std::endl;
                    f_last_result = utils::Variant(errMessage);
                    record_error(2);
                } catch (const std::exception& e) {
                    err() << "Error: " << e.what() << std::endl;
                    f_last_result = utils::Variant(errMessage);
                    record_error(4);
                }
            }
        } else {
            f_leaving = true;
        }

        return f_last_result;
    }

}; // namespace cmd

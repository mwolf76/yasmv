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

#include <interpreter.hh>

#include <iostream>
#include <sstream>
#include <config.h>

#include <commands/commands.hh>

#include <cstdio>
#include <cstdlib>


#ifdef HAVE_LIBREADLINE
#  if defined(HAVE_READLINE_READLINE_H)
#    include <readline/readline.h>
#  elif defined(HAVE_READLINE_H)
#    include <readline.h>
#  else /* !defined(HAVE_READLINE_H) */
#    error Unsupported libreadline
#  endif /* !defined(HAVE_READLINE_H) */
#else /* !defined(HAVE_READLINE_READLINE_H) */
/* no readline,  provide fallback */
char* readline(const char *prompt)
{
    static char *buf= NULL;
    const int LINE_BUFSIZE (0x200);

    if (prompt)
        fputs( prompt, stdout);

    buf = (char *) malloc(LINE_BUFSIZE);
    return fgets(buf, LINE_BUFSIZE, stdin);
}
#endif /* HAVE_LIBREADLINE */

#ifdef HAVE_READLINE_HISTORY
#  if defined(HAVE_READLINE_HISTORY_H)
#    include <readline/history.h>
#  elif defined(HAVE_HISTORY_H)
#    include <history.h>
#  else /* !defined(HAVE_HISTORY_H) */
#    error Unsupported readline history
#  endif /* defined(HAVE_READLINE_HISTORY_H) */
#else /* HAVE_READLINE_HISTORY */
/* no history, provide fallback */
void add_history (const char*)
{}
#endif

/* A static variable for holding the line. */
static char* line_buf = NULL;

/* Read a string, and return a pointer to it.
   Returns NULL on EOF. */
static char* rl_gets()
{
    OptsMgr& om
        (OptsMgr::INSTANCE());

    /* If the buffer has already been allocated, return the memory to
       the free pool. */
    if (NULL != line_buf) {
        free (line_buf);
        line_buf = NULL;
    }

    /* Get a line from the user. */
    line_buf = readline(om.quiet() ? NULL : ">> ");

    /* If the line has any text in it, save it on the history. */
    if (line_buf && *line_buf)
        add_history (line_buf);

    return line_buf;
}

Interpreter_ptr Interpreter::f_instance = NULL;
Interpreter& Interpreter::INSTANCE()
{
    if (! f_instance)
        f_instance = new Interpreter();

    return *f_instance;
}

Interpreter::Interpreter()
    : f_retcode(0)
    , f_leaving(false)

      // default I/O streams
    , f_in(& std::cin)
    , f_out(& std::cout)
    , f_err(& std::cerr)
{
    const void* instance
        (this);

    clock_gettime(CLOCK_MONOTONIC, &f_epoch);

    DEBUG
        << "Initialized Interpreter @"
        << instance
        << std::endl;
}

Interpreter::~Interpreter()
{
    const void* instance
        (this);

    DEBUG
        << "Destroyed Interpreter @"
        << instance
        << std::endl;
}

void Interpreter::quit(int retcode)
{
    f_retcode = retcode;
    f_leaving = true;
}

extern CommandVector_ptr parseCommand(const char *command_line);
Variant& Interpreter::operator()(Command_ptr cmd)
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

        f_last_result = Variant(errMessage);
    }

    delete cmd; /* claims ownership! */
    return f_last_result;
}

void chomp(char *p)
{
    assert(p != NULL);
    while (*p)
        ++ p;

    -- p;
    if (isspace(*p))
        *p = 0;
}

Variant& Interpreter::operator()()
{
    char *cmdline { NULL };
    if (isatty(STDIN_FILENO))
        cmdline = rl_gets();
    else {
        /* FIXME: memleaks */
        static char *buf= NULL;
        const int LINE_BUFSIZE (0x200);

        buf = (char *) malloc(LINE_BUFSIZE);
        cmdline = fgets(buf, LINE_BUFSIZE, stdin);
    }

    if (cmdline != NULL) {
        chomp(cmdline);
        if (cmdline && 0 < strlen(cmdline)) {
            try {
                CommandVector_ptr cmds { parseCommand(cmdline) };
                if (cmds) {
                    for (CommandVector::const_iterator i = cmds->begin();
                         cmds->end() != i; ++ i) {

                        Command_ptr cmd { *i };
                        (*this)(cmd);
                    }
                }
                else f_last_result = Variant(errMessage);
            } catch (Exception& e) {
                std::string what { e.what() };
                ERR
                    << what
                    << std::endl;

                f_last_result = Variant(errMessage);
            }
        }
    }
    else {
        f_last_result = Variant(okMessage);
        f_leaving = true;
    }

    return f_last_result;
}

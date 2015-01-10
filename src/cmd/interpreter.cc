
/*
 * @file interpreter.cc
 * @brief Command interpreter subsystem related classes and definitions.
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
 *  Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/
#include <iostream>
#include <sstream>

#include <commands/commands.hh>
#include <interpreter.hh>

#include <config.h>

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
    return fgets( buf, LINE_BUFSIZE, stdin);
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
static char *line_read = (char *)NULL;

/* Read a string, and return a pointer to it.
   Returns NULL on EOF. */
char * rl_gets ()
{
    /* If the buffer has already been allocated, return the memory to
       the free pool. */
    if (line_read) {
      free (line_read);
      line_read = (char *)NULL;
    }

  /* Get a line from the user. */
  line_read = readline (">> ");

  /* If the line has any text in it, save it on the history. */
  if (line_read && *line_read)
      add_history (line_read);

  return (line_read);
}

Interpreter_ptr Interpreter::f_instance = NULL;
Interpreter& Interpreter::INSTANCE()
{
    if (! f_instance) {
        f_instance = new Interpreter();
    }
    return (*f_instance);
}

Interpreter::Interpreter()
    : f_retcode(0)
    , f_leaving(false)

      // default I/O streams
    , f_in(& std::cin)
    , f_out(& std::cout)
    , f_err(& std::cerr)
{
    DEBUG
        << "Initialized command interpreter @" << this
        << std::endl;
}

Interpreter::~Interpreter()
{
    DEBUG
        << "Deinitialized command interpreter @" << this
        << std::endl;
}

void Interpreter::quit(int retcode)
{
    f_retcode = retcode;
    f_leaving = true;
}

extern  Command* parseCommand(const char *command); // in utils.cc
Variant& Interpreter::operator()(Command_ptr cmd)
{
    assert(NULL != cmd);

    try {
        f_last_result = (*cmd)();
    }

    catch (Exception& e) {
        f_last_result = Variant(e.what());
    }

    delete cmd;
    return f_last_result;
}

Variant& Interpreter::operator()()
{
    try {
        char *cmdline;
        if ((cmdline = rl_gets())) {
            Command_ptr cmd = parseCommand(cmdline);
            if (NULL != cmd) {

                bool color (OptsMgr::INSTANCE().color());
                if (color) {
                    std::cout << green
                              << "<< "
                              << cmdline
                              << normal
                              << std::endl;
                }
                else {
                    std::cout << "<< "
                              << cmdline
                              << std::endl;
                }

                if (cmd -> blocking())
                    (*this)(cmd);
                else {
                    Job& j (* new Job(*cmd));
                    register_job(j);

                    std::ostringstream oss;

                    oss
                        << "Job "
                        << j.id()
                        << " started"
                    ;


                    f_last_result = oss.str();
                }
            }
            else {
                f_last_result = Variant("Parsing Error");
            }
        }
        else {
            f_last_result = Variant("BYE");
            f_leaving = true;
        }
    }
    catch (Exception &e) {
        f_last_result = Variant("Caught exception");
    }

    return f_last_result;
}

void Interpreter::register_job( Job& job )
{
    f_jobs.push_back( &job );
}


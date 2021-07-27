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

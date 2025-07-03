BEGIN {
D["PACKAGE_NAME"]=" \"yasmv\""
D["PACKAGE_TARNAME"]=" \"yasmv\""
D["PACKAGE_VERSION"]=" \"0.0.9\""
D["PACKAGE_STRING"]=" \"yasmv 0.0.9\""
D["PACKAGE_BUGREPORT"]=" \"marco.pensallorto@gmail.com\""
D["PACKAGE_URL"]=" \"\""
D["PACKAGE"]=" \"yasmv\""
D["VERSION"]=" \"0.0.9\""
D["HAVE_STDIO_H"]=" 1"
D["HAVE_STDLIB_H"]=" 1"
D["HAVE_STRING_H"]=" 1"
D["HAVE_INTTYPES_H"]=" 1"
D["HAVE_STDINT_H"]=" 1"
D["HAVE_STRINGS_H"]=" 1"
D["HAVE_SYS_STAT_H"]=" 1"
D["HAVE_SYS_TYPES_H"]=" 1"
D["HAVE_UNISTD_H"]=" 1"
D["STDC_HEADERS"]=" 1"
D["HAVE_DLFCN_H"]=" 1"
D["LT_OBJDIR"]=" \".libs/\""
D["PACKAGE_BUILD_DATE"]=" \"Sat Jun 28 14:24:53 UTC 2025\""
D["PROGRAM_NAME"]=" \"yasmv\""
D["PROGRAM_VERSION"]=" \"0.0.7\""
D["PROGRAM_BUILD_DATE"]=" \"Sat Jun 28 14:24:53 UTC 2025\""
D["PROGRAM_WEBSITE"]=" \"https://github.com/mwolf76\""
D["PROGRAM_EMAIL"]=" \"marco.pensallorto@gmail.com\""
D["PROGRAM_BUGREPORT"]=" \"Please report bugs to <marco.pensallorto@gmail.com>\""
D["HAVE_CPP"]=" 1"
D["PROG_CPP"]=" \"gcc -E -x c\""
D["SIZEOF_VOID_P"]=" 8"
D["SIZEOF_INT"]=" 4"
D["SIZEOF_LONG"]=" 8"
D["HAVE_LIBM"]=" 1"
D["HAVE_LIBZ"]=" 1"
D["HAVE_DIRENT_H"]=" 1"
D["HAVE_FLOAT_H"]=" 1"
D["HAVE_LIMITS_H"]=" 1"
D["HAVE_MEMORY_H"]=" 1"
D["HAVE_STDDEF_H"]=" 1"
D["HAVE_STDLIB_H"]=" 1"
D["HAVE_STRING_H"]=" 1"
D["HAVE_SYS_IOCTL_H"]=" 1"
D["HAVE_SYS_PARAM_H"]=" 1"
D["HAVE_SYS_TIME_H"]=" 1"
D["HAVE_SYS_RESOURCE_H"]=" 1"
D["HAVE_UNISTD_H"]=" 1"
D["HAVE_SIGNAL_H"]=" 1"
D["HAVE_SYS_SIGNAL_H"]=" 1"
D["HAVE_ERRNO_H"]=" 1"
D["HAVE_REGEX_H"]=" 1"
D["HAVE_INTTYPES_H"]=" 1"
D["HAVE_MALLOC_H"]=" 1"
D["HAVE_BOOST"]=" 1"
D["HAVE_BOOST_SYSTEM_ERROR_CODE_HPP"]=" 1"
D["HAVE_BOOST_FILESYSTEM_PATH_HPP"]=" 1"
D["HAVE_BOOST_PROGRAM_OPTIONS_HPP"]=" 1"
D["HAVE_BOOST_TEST_UNIT_TEST_HPP"]=" 1"
D["HAVE_BOOST_SYSTEM_ERROR_CODE_HPP"]=" 1"
D["HAVE_BOOST_THREAD_HPP"]=" 1"
D["HAVE_BOOST_SYSTEM_ERROR_CODE_HPP"]=" 1"
D["HAVE_BOOST_CHRONO_HPP"]=" 1"
D["HAVE_PTHREAD_PRIO_INHERIT"]=" 1"
D["HAVE_PTHREAD"]=" 1"
D["HAVE_LIBREADLINE"]=" 1"
D["HAVE_READLINE_READLINE_H"]=" 1"
D["HAVE_READLINE_HISTORY"]=" 1"
D["HAVE_READLINE_HISTORY_H"]=" 1"
D["HAVE__BOOL"]=" 1"
D["HAVE_STDBOOL_H"]=" 1"
D["HAVE_MALLOC"]=" 1"
D["HAVE_REALLOC"]=" 1"
D["RETSIGTYPE"]=" void"
D["LSTAT_FOLLOWS_SLASHED_SYMLINK"]=" 1"
D["HAVE_VPRINTF"]=" 1"
D["HAVE_FLOOR"]=" 1"
D["HAVE_MEMMOVE"]=" 1"
D["HAVE_MEMSET"]=" 1"
D["HAVE_POW"]=" 1"
D["HAVE_STRCASECMP"]=" 1"
D["HAVE_STRCHR"]=" 1"
D["HAVE_STRRCHR"]=" 1"
D["HAVE_STRSTR"]=" 1"
D["HAVE_RANDOM"]=" 1"
D["HAVE_SRANDOM"]=" 1"
D["HAVE_GETPID"]=" 1"
D["HAVE_MKSTEMP"]=" 1"
D["HAVE_MKTEMP"]=" 1"
D["HAVE_TMPNAM"]=" 1"
D["HAVE_GETENV"]=" 1"
D["HAVE_SETVBUF"]=" 1"
D["HAVE_SYSTEM"]=" 1"
D["HAVE_POPEN"]=" 1"
D["HAVE_ISATTY"]=" 1"
  for (key in D) D_is_set[key] = 1
  FS = ""
}
/^[\t ]*#[\t ]*(define|undef)[\t ]+[_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ][_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789]*([\t (]|$)/ {
  line = $ 0
  split(line, arg, " ")
  if (arg[1] == "#") {
    defundef = arg[2]
    mac1 = arg[3]
  } else {
    defundef = substr(arg[1], 2)
    mac1 = arg[2]
  }
  split(mac1, mac2, "(") #)
  macro = mac2[1]
  prefix = substr(line, 1, index(line, defundef) - 1)
  if (D_is_set[macro]) {
    # Preserve the white space surrounding the "#".
    print prefix "define", macro P[macro] D[macro]
    next
  } else {
    # Replace #undef with comments.  This is necessary, for example,
    # in the case of _POSIX_SOURCE, which is predefined and required
    # on some systems where configure will not decide to define it.
    if (defundef == "undef") {
      print "/*", prefix defundef, macro, "*/"
      next
    }
  }
}
{ print }

/* LINTLIBRARY */

#include "util.h"
#include <stdio.h>


/*
 *  util_strsav -- save a copy of a string
 */
char* util_strsav(char const* s)
{
    return strcpy(ALLOC(char, strlen(s) + 1), s);
}

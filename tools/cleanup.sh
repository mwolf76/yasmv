#!/bin/sh
set -e

for x in $(find . -iname "*.cc" -o -iname "*.hh" -o -iname "*.h" -o -iname "*.hh"); do
    echo -n "$x ..."; 2>/dev/null emacs -batch "$x" -Q -f mark-whole-buffer -f untabify -f delete-trailing-whitespace -f save-buffer -kill
    clang-format -i "$x";
    echo "";
done

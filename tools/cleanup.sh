#!/bin/sh
set -e

PACKAGES="src/symb src/expr src/enc src/3rdparty src/test src/compiler src/type src/utils src/opts src/sat src/.deps src/parser src/model src/dd src/env src/witness src/algorithms src/cmd"
for p in $PACKAGES; do
    echo " == processing package $p"
    for x in $(find "$p" -iname "*.cc" -o -iname "*.hh" -o -iname "*.h" -o -iname "*.hh"); do
	echo -n "$x ..."; 2>/dev/null emacs -batch "$x" -Q -f mark-whole-buffer -f untabify -f delete-trailing-whitespace -f save-buffer -kill
	clang-format -i "$x";
	echo "";
    done
done

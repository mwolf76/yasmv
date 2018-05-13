# libyamlcpp.m4: Locate libyamlcpp build and runtime deps for autoconf-based projects.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# Additional permission under section 7 of the GNU General Public
# License, version 3 ("GPLv3"):
#
# If you convey this file as part of a work that contains a
# configuration script generated by Autoconf, you may do so under
# terms of your choice.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.
AC_DEFUN([AC_LIBYAMLCPP], [
  AC_ARG_WITH(
    [libyamlcpp-prefix],
    AC_HELP_STRING(
    [--with-libyamlcpp-prefix=PATH],
    [find the libyamlcpp headers and libraries in `PATH/include` and `PATH/lib`. By default, checks in /usr.]),
    libyamlcpp_prefix="$withval",
    libyamlcpp_prefix="/usr")

    save_CPPFLAGS=$CPPFLAGS
    save_LIBS=$LIBS
    AC_LANG_PUSH([C++])

    LIBYAMLCPP_CPPFLAGS="-I$libyamlcpp_prefix/include"
    CPPFLAGS="$save_CFLAGS $LIBYAMLCPP_CPPFLAGS"

    AC_CHECK_HEADER(yaml-cpp/yaml.h,
    [],
    [AC_MSG_ERROR([libyaml-cpp headers not found])])

    LIBYAMLCPP_LIBS="-L$libyamlcpp_prefix/lib -lyaml-cpp"
    LIBS="$save_LIBS $LIBYAMLCPP_LIBS"

    AC_MSG_CHECKING([whether linking with -lyaml-cpp in $libyamlcpp_prefix works])
    AC_LINK_IFELSE(
        [AC_LANG_PROGRAM(
        [#include <yaml-cpp/yaml.h>]
        [YAML::Emitter dummy;])],
        [AC_MSG_RESULT([yes])],
        [AC_MSG_ERROR([no])])

    AC_LANG_POP([C++])
    CPPFLAGS=$save_CFLAGS
    LIBS=$save_LIBS

    AC_SUBST(LIBYAMLCPP)
    AC_SUBST(LIBYAMLCPP_CPPFLAGS)
    AC_SUBST(LIBYAMLCPP_LIBS)
])
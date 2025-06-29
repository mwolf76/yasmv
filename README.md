develop [![Build Status](https://travis-ci.org/mwolf76/yasmv.svg?branch=develop)](https://travis-ci.org/mwolf76/yasmv)
&nbsp;
master [![Build Status](https://travis-ci.org/mwolf76/yasmv.svg?branch=master)](https://travis-ci.org/mwolf76/yasmv)

## ABOUT

  The yasmv (Yet Another Symbolic Model Verifier) project started off in the Fall
2011 as a tentative and partial C++ re-implementation of the NuSMV model
checker. As a former member of the NuSMV development team (in the years between
2008 and 2011) I'd never been completely happy with a few architectural choices,
inherited from the long history of the NuSMV model checker and/or due to the
amount of legacy code and tools that relied on it.

  Overtime, however, the project has significantly diverged from the original
goal of making a NuSMV re-implementation. The input language for yasmv is now a
dialect of the smv language which retains only partial compatibility with
NuSMV's original input language. In this area, my interest is all about
exploring ways to improve language expressiveness and usability.

  The project has now approached a stage in which the program is usable to
perform basic reachability analysis and step-by-step simulation. The source
distribution includes a few examples to demonstrate how the program can be used
to solve planning problems.

## BUILD

  Here is the complete list of build dependencies. These package names are from
  Ubuntu 14.04 (Trusty), used in Travis CI.

  - antlr3
  - autoconf
  - build-essential
  - gcc
  - g++
  - libantlr3c-dev
  - libboost-all-dev
  - libjsoncpp-dev
  - libtool
  - libyaml-cpp-dev
  - openjdk-7-jdk
  - make
  - minisat
  - zlib1g-dev

  when all the required packages are installed, launching the build should boil
  down to this:
  ```
  $ ./setup.sh
  $ make
  ```

  The build may take quite a while. If your machine has multiple cores using -j
  <number-of-parallel-tasks> option when running `make` should help in reducing
  significantly build time, e.g.

  ```
  $ make -j8
  ```

  Another option is to use `distcc`. The setup.sh script contains a working
  example. Refer to `distcc` documentation for more details.

  On my current development platform - Debian 9.4 ("Stretch") - the whole thing
  builds with no warnings. The parser is written with ANTLR3[*] so you will need
  some JRE installed at build time to generate the parser and lexer code.
  Generated parser and lexer code itself is C++, so as long as you don't change
  the grammar source files you will no longer need the JRE to make the build. No
  JRE is needed when running the final executable either.

## DEBIAN PACKAGE BUILD

  The project includes Debian packaging files in the `debian/` directory, allowing
  you to build .deb packages for easy installation and distribution.

### Prerequisites

  In addition to the standard build dependencies, you'll need the Debian packaging
  tools:

  ```
  $ sudo apt-get install debhelper devscripts build-essential
  ```

### Building the Package

  To build the Debian package:

  ```
  $ dpkg-buildpackage -us -uc -b
  ```

  Options explained:
  - `-us`: Do not sign the source package
  - `-uc`: Do not sign the .changes file
  - `-b`: Build binary-only package

  The build process will:
  1. Clean the source tree
  2. Configure and compile the project
  3. Install files to a temporary directory
  4. Create the .deb package

  **Note**: The package build can take considerable time (10-30 minutes depending
  on your system) as it performs a full clean build with optimization flags.

### Output

  Upon successful completion, you'll find the following files in the parent directory:
  - `yasmv_1.0-1_amd64.deb` - The main package containing the yasmv binary
  - `yasmv-dbgsym_1.0-1_amd64.deb` - Debug symbols package (optional)

### Installation

  To install the package:

  ```
  $ sudo dpkg -i ../yasmv_1.0-1_amd64.deb
  ```

  Or using apt to handle dependencies:

  ```
  $ sudo apt install ../yasmv_1.0-1_amd64.deb
  ```

### Package Details

  The Debian package:
  - Installs yasmv to `/usr/bin/`
  - Sets `YASMV_HOME` to `/usr/share/yasmv`
  - Includes man pages in `/usr/share/man/`
  - Handles dependencies automatically

### Troubleshooting

  If the build fails:
  1. Ensure all build dependencies are installed
  2. Run `./setup.sh` first to configure the build system
  3. Try a regular build with `make` to verify the code compiles
  4. Check for sufficient disk space (the build requires ~2GB)

### Automated Builds

  The project includes GitHub Actions workflows for automated Debian package builds:
  
  - **Release builds**: When a new release is created on GitHub, the workflow
    automatically builds .deb packages and attaches them to the release
  - **Test builds**: Pull requests and pushes to master/develop branches trigger
    test builds to ensure packaging remains functional
  
  You can download pre-built packages from the [Releases](https://github.com/mwolf76/yasmv/releases) page.

## RUN

  If you didn't run the setup.sh script, when done with the build there is one
  more step that needs to be taken in order to being able to run the program.
  yasmv requires access to the microcode data package, which is currently
  released along with the source code as a bz2'd tarball. Unpack the microcode
  tarball with:
  ```
  $ tar xfj microcode.tar.bz2 [ -C < optional-target-parent-directory > ]
  ```

  and ensure the `YASMV_HOME` environment variable points to the
  parent of the `microcode` directory you've just created. For
  example, assuming you want the microcode distribution unpacked in
  the the same location as the program source code:

  ```
  $ tar xfj microcode.tar.bz2
  $ export YASMV_HOME=`pwd`
  $ ./yasmv

  yasmv - Yet Another Symbolic Model Verifier
  (c) 2011-2016, Marco Pensallorto < marco DOT pensallorto AT gmail DOT com >
  https://github.com/mwolf76/yasmv

  [Sat May 21 17:21:57 2016].459 src/main.cc:176 :: 2176 microcode fragments registered.
  >>
  ```

  When launched the program will parse the contents of the `microcode` directory
  and display the number of microcode fragments it found. The default microcode
  distribution consists of 2176 fragments and covers the full set of supported
  algebraic operations on n-bits integers (1 <= n <= 64).

  For further information on microcode, please refer to the `README` file in the
  microcode bzip2'd tarball.

  Unit and functional tests can be run using:
  ```
  $ make test
  ```

  Remark: The default build for C++ code uses a low level of optimization (-O0)
  to make life a whole lot easier for debugging. If you want to, feel free to
  enable higher level of optimization for the C++ code (C code already uses
  '-O2' by default). Do not expect major performance gains though, as core
  services `CUDD` (used in the expression compiler) and `Minisat` (which powers the
  solving engine) are compiled/installed separately and already use a higher
  level of optimization.

[*] Still haven't upgraded to ANTLR4. Nor have plans to do it.

## DISCLAIMER

This code is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE. See the GNU Lesser General Public License for more details.

yasmv is in no way related to, or endorsed by, the NuSMV development board
and/or FBK. yasmv does not contain any code from NuSMV's code base.

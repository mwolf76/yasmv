#!/usr/bin/env python
"""
ucodegen.py - micro code generator for gnuSMV
(c) 2014 Marco Pensallorto < marco DOT pensallorto AT gmail DOT com >

This tool is part of the YASMINE project.
"""

import re
import sys
import os.path
import subprocess

workdir = "/home/markus/Code/github/gnuSMV/tools/ucodegen/workdir"

stanzaTmpl = """
{
  clause c;
  c.push_back( 10 );
  c.push_back( 30 );
  c.push_back( 12 );
  f_ucode.push_back( c );
}
"""
def stanza( clause ):
    res = "{\n         clause c;\n"

    for c in clause:
        res += "         c.push_back( %d );\n" % c

    res += "         f_ucode.push_back( c );\n      }\n"
    return res

moduleTmpl = """/* autogenerate source - do not edit */
#include <vector>
using std::vector;

#include <iostream>
using std::cout;
using std::endl;

typedef vector<int> clause;
typedef vector<clause> microcode;

class %(op)s%(width)d {

public:
    %(op)s%(width)d() {
      %(contents)s
    }

    const microcode& ucode() const {
        return f_ucode;
    }

private:
    microcode f_ucode;

};

int main() {
    %(op)s%(width)d() test;

    const microcode& ucode = test.ucode();
    for (microcode::const_iterator i = ucode.begin(); i != ucode.end(); ++ i) {

        const clause& cl = (*i);
        for (clause::const_iterator j = cl.begin(); j != cl.end(); ++ j) {
            cout << *j << " ";
        }
        cout << endl;

    }
}
"""

# parser states
(
    ST_WAIT_TIME0,
    ST_FETCH_VARS,
    ST_WAIT_PROBLEM,
    ST_READ_PROBLEM,
    ST_WRITE_OUT,
) = range(5)

def main():

    # list of operators to be processed
    ops = [ ( 'mul', '*' ) ]

    width = 8 # testing
    for (opName, opSymb) in ops:

        print opName, opSymb, width

        # 1. create SMV model with given op
        modelName = os.path.join( workdir, opName ) + "%d.smv" % (width, )

        model = file (modelName, "wt")
        model.write('MODULE main\n\n')
        model.write('VAR x : unsigned word[%d];\n'  % width)
        model.write('VAR y : unsigned word[%d];\n'  % width)
        model.write('VAR z : unsigned word[%d];\n\n'  % width)

        model.write('INIT z = x %s y\n'  % opSymb)
        model.close()

        # 2. create a CMD script to generate CNF using custom version of NuSMV2
        scriptName = os.path.join( workdir, opName ) + ".cmd"

        cnfName = os.path.join( workdir, opName ) + "%d" % (width, )

        script = file (scriptName, "wt")
        script.write ('go_bmc\n')
        script.write ('gen_invar_bmc -p TRUE -o %s\n' % cnfName )
        script.write ('quit\n')
        script.close ()

        # 3. invoke custom NuSMV2 to generate CNF
        subprocess.call( [ 'NuSMV', '-quiet', '-source', scriptName, modelName ] )

        # 4. process generated .dimacs file
        dimacsName = os.path.join( workdir, opName ) + "%d.dimacs" % (width, )

        ac, x, y, z, seen, ucode = None, [], [], [], [], []
        parserState = ST_WAIT_TIME0

        dimacs = file(dimacsName)
        for line in dimacs:

            if parserState == ST_WAIT_TIME0:

                if re.match( "c @@@@@ Time 0", line):
                    parserState = ST_FETCH_VARS
                    continue

            elif parserState == ST_FETCH_VARS:
                match = re.match( 'c CNF variable (\d+) => Time 0, Model Variable (\S)\.(\d+)',
                                  line )
                if (match):
                    (index, var, bit) = match.groups()
                    index = int(index)
                    bit = int(bit)

                    assert var in ( 'x', 'y', 'z')
                    assert bit in range( width)

                    if var == 'x':
                        x.insert( 0, index)
                    elif var == 'y':
                        y.insert( 0, index)
                    elif var == 'z':
                        z.insert( 0, index)

                elif re.match( "c @@@@@ Time 1", line ):
                    parserState = ST_WAIT_PROBLEM
                    continue

            elif parserState == ST_WAIT_PROBLEM:

                if re.match( "p cnf", line):
                    parserState = ST_READ_PROBLEM
                    continue

            elif parserState == ST_READ_PROBLEM:

                if re.match( "c End of dimacs dumping", line):
                    parserState = ST_WRITE_OUT
                    continue

                numbers = map( int, line.split(" ")[:-1])
                assert (ac is not None or 1 == len(numbers))

                if ac is None:
                    assert 1 == len(numbers)
                    ac = numbers[0]

                rewrite = []
                for n in numbers:

                    if n == ac:
                        rewrite.append(0)
                        continue
                    elif n in z:
                        rewrite.append( 0 * width + z.index(n))
                        continue
                    elif n in x:
                        rewrite.append( 1 * width + x.index(n))
                        continue
                    elif n in y:
                        rewrite.append( 2 * width + y.index(n))
                        continue
                    elif n not in seen:
                        seen.append(n)

                    rewrite.append( 3 * width + seen.index(n))

                ucode.append(rewrite)

        assert parserState == ST_WRITE_OUT
        assert( len(x) == len(y) and len(x) == len(z))

        print "x = %s" % x
        print "y = %s" % y
        print "z = %s" % z

        sourceName = os.path.join( workdir, opName ) + "%d.cc" % (width, )
        source = file (sourceName, "wt" )

        source.write ( moduleTmpl % {
            'op': opName,
            'width': width,
            'contents': "\n      ".join( map( stanza, ucode ))
        })

if __name__ == "__main__":
    main()

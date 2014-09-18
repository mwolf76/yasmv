#!/usr/bin/env python
"""
ucodegen.py - micro code generator for gnuSMV
(c) 2014 Marco Pensallorto < marco DOT pensallorto AT gmail DOT com >

This tool is part of the YASMINE project.
"""

import re
import sys
import datetime
import os.path
import subprocess

# parser states
(
    ST_WAIT_TIME0,
    ST_FETCH_VARS,
    ST_WAIT_PROBLEM,
    ST_READ_PROBLEM,
    ST_WRITE_OUT,
) = range(5)

def timestamp():
    return datetime.datetime.strftime(datetime.datetime.now(), '%Y-%m-%dT%H:%M:%S')

class BaseMicrocodeGenerator(object):

    minbits = 1
    maxbits = 64
    signedness = ( 'unsigned', 'signed' )

    workdir = "/home/markus/Code/markus/github/gnuSMV/tools/ucodegen/workdir"
    ops     = None

    def __call__(self):
        assert self.ops is not None
        for (opName, opSymb) in self.ops:

            for signed in self.signedness:

                for width in range(self.minbits, 1 + self.maxbits):

                    sourceName = os.path.join(
                        self.workdir, signed[0] + '-' + opName ) + "-%d.json" % width

                    source = file (sourceName, "wt" )

                    print "Generating microcode for %s (%s), width = %d" % (
                        signed[0] + opName, opSymb, width
                    )

                    # 1. create SMV model with given op
                    modelName = os.path.join( self.workdir, signed[0] + opName ) + "%d.smv" % (width, )
                    self.write_smv(modelName, opSymb, signed, width)

                    # 2. create a CMD script to generate CNF using custom version of NuSMV2
                    scriptName = os.path.join( self.workdir, "build_microcode" ) + ".cmd"

                    cnfName = os.path.join( self.workdir, signed[0] + opName ) + "%d" % (width, )

                    script = file (scriptName, "wt")
                    script.write ('go_bmc\n')
                    script.write ('gen_invar_bmc -p TRUE -o %s\n' % cnfName )
                    script.write ('quit\n')
                    script.close ()

                    # 3. invoke custom NuSMV2 to generate CNF
                    subprocess.call( [ 'NuSMV', '-quiet', '-source',
                                       scriptName, modelName ], stderr=file ('/dev/null'))

                    # 4. process generated .dimacs file
                    dimacsName = os.path.join( self.workdir, signed[0] + opName ) + "%d.dimacs" % (width, )

                    ac, x, y, z, seen, ucode = None, [], [], [], [], []
                    parserState = ST_WAIT_TIME0

                    dimacs = file(dimacsName)
                    for line in dimacs:

                        if parserState == ST_WAIT_TIME0:

                            if re.match( "c @@@@@ Time 0", line):
                                parserState = ST_FETCH_VARS
                                continue

                        elif parserState == ST_FETCH_VARS:
                            match = re.match(
                                'c CNF variable (\d+) => Time 0, Model Variable (\S)\.(\d+)', line )

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
                            for n_ in numbers:
                                n, pol = abs(n_), (n_ < 0) and 1 or 0

                                if n in z:
                                    rewrite.append( pol + 2 * (0 * width + z.index(n)))
                                    continue
                                elif n in x:
                                    rewrite.append( pol + 2 * (1 * width + x.index(n)))
                                    continue
                                elif n in y:
                                    rewrite.append( pol + 2 * (2 * width + y.index(n)))
                                    continue
                                elif n not in seen:
                                    seen.append(n)

                                rewrite.append( pol + 2 * (3 * width + seen.index(n)))

                            ucode.append(rewrite)

                    assert parserState == ST_WRITE_OUT
                    source.write( "{ \"generated\": \"%(generated)s\", \"cnf\": [%(cnf)s]}" % {
                        'generated': timestamp(),
                        'cnf': ", ".join( map( str, ucode ))
                    })

class BinaryArithmeticalGenerator (BaseMicrocodeGenerator):

    def __init__(self):
        # list of operators to be processed
        self.ops = [
            ( 'add', '+'  ),
            ( 'sub', '-'  ),
            ( 'mul', '*'  ),
            ( 'div', '/'  ),
            ( 'mod', 'mod'),

            ( 'and', '&' ),
            ( 'or', '|' ),
            ( 'xor', 'xor' ),
            ( 'xnor', 'xnor' ),
            ( 'implies', '->' ),
        ]


    def write_smv(self, modelName, opSymb, signed, width):
        model = file (modelName, "wt")
        model.write('MODULE main\n\n')
        model.write('VAR x : %s word[%d];\n'  % (signed, width))
        model.write('VAR y : %s word[%d];\n'  % (signed, width))
        model.write('VAR z : %s word[%d];\n\n' % (signed, width))
        model.write('INIT z = (x %s y)\n'  % opSymb)
        model.close()

class UnaryArithmeticalGenerator (BaseMicrocodeGenerator):

    def __init__(self):
        # list of operators to be processed
        self.ops = [
            ( 'not', '!' ),
            ( 'neg', '-' )
        ]

    def write_smv(self, modelName, opSymb, signed, width):
        model = file (modelName, "wt")
        model.write('MODULE main\n\n')
        model.write('VAR x : %s word[%d];\n'   % (signed, width))
        model.write('VAR z : %s word[%d];\n\n' % (signed, width))
        model.write('INIT z = (%s x)\n'  % opSymb)
        model.close()

class BinaryRelationalGenerator (BaseMicrocodeGenerator):

    def __init__(self):
        # list of operators to be processed
        self.ops = [
            ( 'eq', '='  ),
            ( 'ne', '!=' ),
            ( 'ge', '>=' ),
            ( 'gt', '>'  ),
            ( 'le', '<=' ),
            ( 'lt', '<'  )
        ]

    def write_smv(self, modelName, opSymb, signed, width):
        model = file (modelName, "wt")
        model.write('MODULE main\n\n')
        model.write('VAR x : %s word[%d];\n'  % (signed, width))
        model.write('VAR y : %s word[%d];\n'  % (signed, width))
        model.write('VAR z : unsigned word[1];\n')
        model.write('INIT z = word1(x %s y)\n'  % opSymb)
        model.close()

def main():
    obj = BinaryArithmeticalGenerator()
    obj()

    obj = UnaryArithmeticalGenerator()
    obj()

    obj = BinaryRelationalGenerator()
    obj()

if __name__ == "__main__":
    main()

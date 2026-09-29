#!/usr/bin/env python3
"""Compile and run the standalone API gate against an explicit pinned checkout."""
import argparse
import math
import os
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile

REVISION = 'c60730422e758ef1cebe7aeddf2dda31c996bf04'
ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, required=True,
                        help='Unmodified CaDiCaL rel-3.0.1 Git checkout')
    parser.add_argument('--build', type=Path, help='Library directory (default: SOURCE/build)')
    parser.add_argument('--cxx', default=os.environ.get('CXX', 'c++'))
    parser.add_argument('--cxxflags', default=os.environ.get('CXXFLAGS', '-O2 -g'))
    parser.add_argument('--suite', choices=('api', 'proof', 'all'), default='api',
                        help='Standalone contract suite (default: api)')
    parser.add_argument('--timeout', type=float, default=60, help='Seconds for the API executable')
    args = parser.parse_args()
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        parser.error('--timeout must be finite and positive')
    source = args.source.resolve()
    build = (args.build or source / 'build').resolve()
    try:
        def git(*arguments):
            return subprocess.check_output(['git', '-C', str(source), *arguments],
                                           text=True, stderr=subprocess.PIPE, timeout=10).strip()
        if Path(git('rev-parse', '--show-toplevel')).resolve() != source:
            raise ValueError('--source must be the CaDiCaL checkout root')
        if git('rev-parse', 'HEAD') != REVISION:
            raise ValueError(f'CaDiCaL must be pinned to {REVISION}')
        git('diff', '--exit-code', 'HEAD', '--')
        header, library = source / 'src/cadical.hpp', build / 'libcadical.a'
        if not header.is_file() or not library.is_file():
            raise ValueError('Build the pinned library first; cadical.hpp or libcadical.a is missing')
        if args.suite != 'api' and not (header.parent / 'tracer.hpp').is_file():
            raise ValueError('Matching pinned tracer.hpp is missing')
        compiler = shlex.split(args.cxx)
        if not compiler:
            raise ValueError('--cxx must name a compiler')
        print(f'CaDiCaL source: {source} ({REVISION})', flush=True)
        print(f'CaDiCaL library: {library}', flush=True)
        with tempfile.TemporaryDirectory(prefix='yasmv-cadical-api-') as directory:
            for suite in (('api', 'proof') if args.suite == 'all' else (args.suite,)):
                binary = Path(directory) / ('cadical-' + suite + '-tests')
                sources = [str(ROOT / ('tests/test_cadical_' + suite + '.cc'))]
                if suite == 'proof':
                    sources.append(str(ROOT / 'src/sat/proof.cc'))
                subprocess.run([*compiler, '-std=c++20', '-Wall', '-Wextra', '-Werror',
                                *shlex.split(args.cxxflags), '-I', str(header.parent),
                                '-I', str(ROOT / 'src'), *sources, str(library),
                                '-pthread', '-o', str(binary)], check=True, timeout=120)
                subprocess.run([str(binary)], check=True, timeout=args.timeout)
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(f'CaDiCaL API gate failed: {error}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())

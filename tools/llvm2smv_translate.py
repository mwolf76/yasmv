#!/usr/bin/env python3
"""Translate admitted LLVM 18 scalar/memory IR and publish a natively validated bundle."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

from llvm2smv_artifact import ArtifactError, publish, read_json

ROOT = Path(__file__).resolve().parents[1]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('-o', '--output', required=True, type=Path, help='New bundle directory (never replaced)')
    parser.add_argument('--memory-bytes', type=int, default=128)
    parser.add_argument('--allocation-generations', type=int, default=4)
    parser.add_argument('--entry', default='main')
    parser.add_argument('--translator', default=os.environ.get('LLVM2SMV', str(ROOT / 'llvm2smv/llvm2smv')))
    parser.add_argument('--checker', default=os.environ.get('YASMV', str(ROOT / 'yasmv')))
    parser.add_argument('--timeout', type=float, default=30, help='Wall seconds per translation/validation process')
    args = parser.parse_args(argv)
    os.environ.setdefault('YASMV_HOME', str(ROOT))
    try:
        if not (0 < args.timeout < float('inf')):
            raise ArtifactError('Timeout must be positive and finite')
        process = subprocess.run([args.translator, '--emit-scalar-bundle', '--diagnostics=json',
            '--entry=' + args.entry, '--memory-bytes=' + str(args.memory_bytes),
            '--allocation-generations=' + str(args.allocation_generations), str(args.input.resolve())], capture_output=True, text=True, timeout=args.timeout)
        if process.returncode != 0:
            sys.stderr.write(process.stderr)
            return 2
        candidate = read_json(process.stdout)
        destination = publish(candidate, args.output, args.checker, timeout=args.timeout)
        manifest = read_json(candidate['files']['manifest.json'])
        print(json.dumps(dict(version=1, status='translated', bundle=str(destination),
                              artifact_id=manifest['artifact_id'], verification_result=None)))
        return 0
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(json.dumps(dict(version=1, status='error', message=str(error))), file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())

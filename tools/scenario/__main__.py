"""Export a replay-validated trace or run a portable scenario without the UI."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from tools.workbench.engine import ROOT, atomic, read
from .format import build
from .replay import replay


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    export = commands.add_parser('export')
    export.add_argument('trace', type=Path)
    export.add_argument('--metadata', type=Path, required=True)
    export.add_argument('--model', type=Path, required=True)
    export.add_argument('--inputs', type=Path, help='JSON compile-time input map')
    export.add_argument('--root', default='')
    export.add_argument('--binary', type=Path, default=ROOT / 'yasmv')
    export.add_argument('--home', type=Path, default=ROOT)
    export.add_argument('--output', type=Path, required=True)
    run = commands.add_parser('replay')
    run.add_argument('scenario', type=Path)
    run.add_argument('--implementation', choices=('faulty', 'deduplicating'), default='faulty')
    run.add_argument('--output', type=Path)
    args = parser.parse_args()
    try:
        if args.command == 'export':
            trace = read(args.trace)
            with tempfile.TemporaryDirectory() as directory:
                request = Path(directory) / 'request.json'
                atomic(request, dict(version=1, model=str(args.model.resolve()), inputs=read(args.inputs) if args.inputs else {},
                                     query=dict(operation='validate-trace', trace=trace)))
                command = [sys.executable, str(ROOT / 'tools/run-query.py'), str(request), '--binary', str(args.binary.resolve()), '--hard-timeout', '60']
                if args.root:
                    command += ['--root', args.root]
                process = subprocess.run(command, capture_output=True, text=True, cwd=directory,
                                         env=dict(os.environ, YASMV_HOME=str(args.home.resolve())), timeout=65)
                validation = json.loads(process.stdout)
                if process.returncode or validation.get('outcome') != 'valid':
                    raise ValueError('Trace did not pass model replay: ' + json.dumps(validation.get('diagnostics', [])))
                result = build(trace, read(args.metadata), validation)
        else:
            result = replay(read(args.scenario), args.implementation)
        if args.output:
            atomic(args.output, result)
        else:
            print(json.dumps(result, indent=2))
        return 3 if result.get('outcome') == 'diverged' else 0
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print(json.dumps(dict(version=1, status='error', diagnostics=[dict(code='scenario-error', message=str(error))])))
        return 2


if __name__ == '__main__':
    sys.exit(main())

#!/usr/bin/env python3
"""Run one isolated M1 query with a hard deadline and atomic final output."""
import argparse
import json
import os
import signal
from pathlib import Path
import subprocess
import sys
import tempfile


def run(request_path, binary, timeout, root=None):
    try:
        request = json.loads(Path(request_path).read_text())
        if not isinstance(request, dict):
            raise ValueError('Request must be an object')
    except (ValueError, OSError) as error:
        return 2, {'version': 1, 'status': 'error', 'outcome': None,
                   'stop_reason': 'validation_error', 'complete': False, 'trace': None,
                   'diagnostics': [{'code': 'invalid-request', 'message': str(error)}]}
    try:
        proc = subprocess.Popen([binary, '--quiet', '--query-file', str(request_path)] + (['--root', root] if root else []),
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True)
    except OSError as error:
        return 4, {'version': 1, 'status': 'error', 'outcome': None,
                   'stop_reason': 'internal_error', 'complete': False, 'trace': None,
                   'diagnostics': [{'code': 'worker-start-failed', 'message': str(error)}]}
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGTERM)
        try:
            proc.communicate(timeout=0.25)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.communicate()
        return 3, {'version': 1, 'request_id': (request.get('query') or {}).get('request_id', '') if isinstance(request.get('query'), dict) else '',
                   'status': 'unknown', 'outcome': None, 'stop_reason': 'deadline',
                   'complete': False, 'trace': None, 'forced_termination': True}
    try:
        result = json.loads(stdout)
        if not isinstance(result, dict) or result.get('version') != 1 or result.get('status') not in ('completed', 'unknown', 'error'):
            raise ValueError('Invalid worker result')
        expected = 0 if result['status'] == 'completed' else 3 if result['status'] == 'unknown' else (4 if result.get('stop_reason') == 'internal_error' else 2)
        if proc.returncode != expected:
            raise ValueError('Worker exit status disagrees with result')
        return expected, result
    except (ValueError, TypeError):
        return 4, {'version': 1, 'status': 'error', 'outcome': None,
                   'stop_reason': 'internal_error', 'complete': False, 'trace': None,
                   'diagnostics': [{'code': 'worker-failed', 'message': stderr[-4096:]}]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('request', type=Path)
    parser.add_argument('--binary', default=str(Path(__file__).resolve().parents[1] / 'yasmv'))
    parser.add_argument('--hard-timeout', type=float, default=60.0, help='seconds, including loading')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--root', help='root module in a multi-module model')
    args = parser.parse_args()
    if args.hard_timeout <= 0:
        parser.error('--hard-timeout must be positive')
    os.environ.setdefault('YASMV_HOME', str(Path(__file__).resolve().parents[1]))
    code, result = run(args.request.resolve(), args.binary, args.hard_timeout, args.root)
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        with tempfile.NamedTemporaryFile(mode='w', dir=args.output.resolve().parent, delete=False) as stream:
            temp = Path(stream.name)
            stream.write(text)
        try:
            temp.replace(args.output)
        finally:
            temp.unlink(missing_ok=True)
    else:
        sys.stdout.write(text)
    return code


if __name__ == '__main__':
    sys.exit(main())

#!/usr/bin/env python3
"""Compare fresh query processes with immutable compiled sessions on fixed inputs."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import statistics
import subprocess
import sys
import tempfile
import threading
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.workbench.sessions import Pool


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--model', type=Path, default=ROOT / 'examples/retry-protocol/faulty.smv')
    parser.add_argument('--target', default='DUPLICATE')
    parser.add_argument('--depth', type=int, default=12)
    parser.add_argument('--runs', type=int, default=5)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if not 1 <= args.runs <= 100:
        parser.error('--runs must be from 1 to 100')
    query = dict(request_id='benchmark', operation='shortest-reach', target=args.target, limits={'depth': args.depth})
    binary = ROOT / 'yasmv'
    source = args.model.read_text()
    report = dict(machine=platform.platform(), processor=platform.machine(), python=platform.python_version(),
                  compiler=subprocess.check_output(['c++', '--version'], text=True).splitlines()[0],
                  cxxflags=re.search(r'^CXXFLAGS = (.*)$', (ROOT / 'Makefile').read_text(), re.MULTILINE).group(1),
                  binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
                  source_sha256=hashlib.sha256(source.encode()).hexdigest(), query=query, samples_ms={})
    baseline = None
    def record(result):
        nonlocal baseline
        signature = {k: result.get(k) for k in ('status', 'outcome', 'identity', 'optimality')}
        if result['status'] != 'completed':
            raise ValueError('Benchmark query did not complete')
        if baseline is None: baseline = signature
        elif signature != baseline: raise ValueError('Fresh and cached analysis results disagree')
    with tempfile.TemporaryDirectory() as directory:
        request = Path(directory) / 'query.json'
        request.write_text(json.dumps(dict(version=1, model=str(args.model.resolve()), query=query)))
        fresh = []
        for _ in range(args.runs):
            start = time.monotonic()
            process = subprocess.run([str(binary), '--quiet', '--query-file', str(request)],
                                     env=dict(os.environ, YASMV_HOME=str(ROOT)), capture_output=True, text=True, timeout=90, check=True)
            fresh.append((time.monotonic() - start) * 1000)
            record(json.loads(process.stdout))
        report['samples_ms']['fresh'] = fresh
        pool = Pool()
        try:
            cached = []
            for _ in range(args.runs + 1):
                start = time.monotonic()
                result = pool.run(str(binary), str(ROOT), dict(source=source, root='', inputs={}), query, threading.Event(), time.monotonic() + 90)
                cached.append((time.monotonic() - start) * 1000)
                record(result)
            report['snapshot_initial_ms'] = cached.pop(0)
            report['samples_ms']['warm_snapshot'] = cached
            report['session_key'] = result['statistics']['session_key']
        finally: pool.close()
    report['result'] = baseline
    report['median_ms'] = {name: statistics.median(values) for name, values in report['samples_ms'].items()}
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report['median_ms']))


if __name__ == '__main__':
    main()

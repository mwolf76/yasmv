#!/usr/bin/env python3
"""Capture bounded interpolation searches and replay fixed obligations under cgroup limits."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time
import uuid

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT_FILES = ('input.cnf', 'interface.json', 'proof.events', 'complete')


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''): h.update(block)
    return h.hexdigest()


def write(path, value):
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def seal(directory):
    hashes = {name: digest(directory / name) for name in ARTIFACT_FILES}
    path = directory / 'hashes.json'
    if path.exists():
        if json.loads(path.read_text()) != hashes: raise ValueError('Captured artifact hash mismatch')
    else: write(path, hashes)
    return hashes


def properties(unit):
    keys = ('LoadState', 'SubState', 'Result', 'MainPID', 'MemoryPeak', 'MemoryCurrent',
            'MemoryMax', 'MemorySwapMax', 'RuntimeMaxUSec', 'CPUUsageNSec',
            'ExecMainCode', 'ExecMainStatus', 'ExecMainStartTimestampMonotonic',
            'ExecMainExitTimestampMonotonic')
    text = subprocess.check_output(['systemctl', '--user', 'show', unit,
                                   *['--property=' + k for k in keys]], text=True)
    return dict(line.split('=', 1) for line in text.splitlines() if '=' in line)


def telemetry_summary(output):
    path = output / 'diagnostics/telemetry.jsonl'
    summary = dict(samples=0, truncated_records=0, maxima={}, queries={})
    if not path.exists(): return summary
    for line in path.read_text().splitlines():
        try: sample = json.loads(line)
        except ValueError:
            summary['truncated_records'] += 1
            continue
        summary['samples'] += 1
        query = summary['queries'].setdefault(str(sample['query_index']), {}) if 'query_index' in sample else None
        for key, value in sample.items():
            if isinstance(value, int) and key not in ('elapsed_ms', 'query_index', 'horizon', 'image'):
                summary['maxima'][key] = max(summary['maxima'].get(key, 0), value)
                if query is not None: query[key] = max(query.get(key, 0), value)
        if query is not None and sample['phase'] == 'query_verified': query['verified'] = True
    return summary


def run(command, output, memory_bytes, wall_seconds, environment, identity):
    unit = 'yasmv-imc-' + uuid.uuid4().hex[:12] + '.service'
    record = dict(version=1, status='starting', command=list(map(str, command)), unit=unit,
                  memory_max_bytes=memory_bytes, wall_seconds=wall_seconds,
                  environment=environment, identity=identity, boot_id=Path('/proc/sys/kernel/random/boot_id').read_text().strip(),
                  started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  binary_sha256=digest(command[0]))
    write(output / 'run.json', record)
    args = ['systemd-run', '--user', '--no-ask-password', '--unit=' + unit,
            '--property=MemoryMax=' + str(memory_bytes), '--property=MemorySwapMax=0',
            '--property=MemoryAccounting=yes', '--property=OOMPolicy=stop',
            '--property=SuccessExitStatus=3',
            '--property=RemainAfterExit=yes', '--property=RuntimeMaxSec=' + str(wall_seconds + 10),
            '--property=WorkingDirectory=' + str(ROOT),
            '--property=StandardOutput=file:' + str(output / 'stdout.json'),
            '--property=StandardError=file:' + str(output / 'stderr.log')]
    for key, value in environment.items(): args.append('--setenv=' + key + '=' + str(value))
    # Avoid inheriting diagnostic settings from the user manager.
    unset = set(('YASMV_IMC_DIAGNOSTICS', 'YASMV_IMC_CAPTURE', 'YASMV_IMC_IMAGES', 'YASMV_IMC_HEAP_RELEASE')) - environment.keys()
    if unset: args.append('--property=UnsetEnvironment=' + ' '.join(sorted(unset)))
    subprocess.run([*args, *map(str, command)], check=True)
    last_print = 0
    try:
        while True:
            state = properties(unit)
            sample = dict(observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(), service=state)
            with (output / 'resources.jsonl').open('a') as stream: stream.write(json.dumps(sample) + '\n')
            record.update(status='running', latest=sample)
            write(output / 'run.json', record)
            if state['LoadState'] == 'not-found' or state['SubState'] not in ('running', 'start', 'start-pre', 'start-post'):
                break
            if time.monotonic() - last_print >= 30:
                print(unit, 'memory=' + state['MemoryCurrent'], 'peak=' + state['MemoryPeak'], flush=True)
                last_print = time.monotonic()
            time.sleep(1)
    except BaseException:
        subprocess.run(['systemctl', '--user', 'stop', unit], check=False)
        record['status'] = 'interrupted'; write(output / 'run.json', record)
        raise
    record['status'] = 'finished'
    record['process_wall_seconds'] = (int(state.get('ExecMainExitTimestampMonotonic') or 0) -
                                      int(state.get('ExecMainStartTimestampMonotonic') or 0)) / 1e6
    try: result = json.loads((output / 'stdout.json').read_text())
    except (ValueError, FileNotFoundError): result = None
    record['query_status'] = result.get('status') if result else 'no_result'
    record['outcome'] = result.get('outcome') if result else None
    record['telemetry'] = telemetry_summary(output)
    write(output / 'run.json', record)
    return record, result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='operation', required=True)
    for name in ('capture', 'replay'):
        cmd = sub.add_parser(name)
        cmd.add_argument('--output', type=Path, required=True)
        cmd.add_argument('--memory-gb', type=int, default=8, help='Decimal GB cgroup cap')
        cmd.add_argument('--wall-seconds', type=int, default=600)
        cmd.add_argument('--heap-release', choices=('auto','off'), default='auto')
    capture = sub.choices['capture']
    capture.add_argument('--model', type=Path, required=True)
    capture.add_argument('--target', default='GOAL')
    capture.add_argument('--images', type=int, required=True)
    capture.add_argument('--capture', default='all', help='Query indices, e.g. 0,12,13; initial projection is 0')
    replay = sub.choices['replay']
    replay.add_argument('--artifact', type=Path, required=True)
    replay.add_argument('--mode', choices=('events', 'solve'), default='events')
    args = parser.parse_args()
    if args.memory_gb < 1 or args.wall_seconds < 1: parser.error('Budgets must be positive')
    if args.operation == 'capture' and args.images < 1: parser.error('--images must be positive')
    output = args.output.resolve(); output.mkdir(parents=True, exist_ok=False)
    environment = dict(YASMV_HOME=str(ROOT), YASMV_IMC_DIAGNOSTICS=str(output / 'diagnostics'),
                       YASMV_IMC_HEAP_RELEASE=args.heap_release)
    if args.operation == 'capture':
        model = args.model.resolve()
        request = dict(version=1, model=str(model), query=dict(operation='check', variant='reachable', method='interpolation',
                       target=args.target, limits=dict(wall_ms=args.wall_seconds * 1000)))
        write(output / 'request.json', request)
        environment.update(YASMV_IMC_CAPTURE=args.capture, YASMV_IMC_IMAGES=str(args.images))
        command = [ROOT / 'yasmv', '--quiet', '--sat-random-seed', '0', '--query-file', output / 'request.json']
        identity = dict(model_sha256=digest(model), images=args.images, capture_selection=args.capture)
    else:
        artifact = args.artifact.resolve()
        if not (artifact / 'hashes.json').exists(): parser.error('Artifact must be sealed by a completed capture run')
        identity = dict(artifact=str(artifact), artifact_hashes=seal(artifact), mode=args.mode)
        command = [ROOT / 'interpolation_replay', artifact, args.mode]
    record, result = run(command, output, args.memory_gb * 10**9, args.wall_seconds, environment, identity)
    record['identity'] = identity
    state = record['latest']['service']
    normal = state['Result'] == 'success' and state['ExecMainCode'] == '1'
    if args.operation == 'capture':
        # Exit 3 is the expected UNKNOWN for a completed fixed-image prefix.
        # A wall timeout, OOM, or partial image is never a completed benchmark.
        record['work_completed'] = bool(normal and record['telemetry']['samples'] and result and (result['status'] == 'completed' or
                result.get('statistics', {}).get('interpolation', {}).get('image_limit_reached')))
        record['captures'] = []
        for directory in sorted((output / 'diagnostics').glob('query-*')):
            marker = directory / 'complete'
            if marker.exists() and marker.read_text() == 'verified-unsat\n':
                record['captures'].append(dict(directory=str(directory), hashes=seal(directory)))
        record['scope'] = 'whole-search-prefix'
    else:
        if seal(artifact) != identity['artifact_hashes']: raise ValueError('Artifact changed during replay')
        record['work_completed'] = bool(normal and state['ExecMainStatus'] == '0' and result and result.get('verified'))
        record['scope'] = 'single-interpolation-obligation'
        if result: record['replay'] = result
    write(output / 'run.json', record)
    print(json.dumps({key: record[key] for key in ('work_completed', 'scope', 'process_wall_seconds', 'query_status')}, indent=2))
    return 0 if record['work_completed'] else 3


if __name__ == '__main__':
    raise SystemExit(main())

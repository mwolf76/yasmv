#!/usr/bin/env python3
"""Compare safety algorithms in fresh processes (Linux)."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shlex
import signal
import statistics
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from llvm2smv_artifact import check_artifact

METHODS = ('bounded', 'simple-path', 'k-induction', 'interpolation')


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def query_for(case, method, wall_ms):
    query = dict(assumptions=case.get('assumptions', []), limits=dict(wall_ms=wall_ms))
    if method == 'simple-path':
        query.update(operation='reach', strategy='forward', target=case['target'])
    else:
        query.update(operation='check-property' if method == 'bounded' else 'prove-property',
                     property=dict(name='safe', expression='!(' + case['target'] + ')'),
                     strategy='interpolation' if method == 'interpolation' else 'auto')
        query['limits']['depth'] = case['depth']
    return query


def measure(command, directory, timeout, home=ROOT):
    """Reap exactly this child with wait4; never use cumulative RUSAGE_CHILDREN."""
    started = time.monotonic()
    stdout_path, stderr_path = directory / 'stdout.txt', directory / 'stderr.txt'
    with stdout_path.open('w') as stdout_file, stderr_path.open('w') as stderr_file:
        process = subprocess.Popen(list(map(str, command)), stdout=stdout_file, stderr=stderr_file,
                                   start_new_session=True, env=dict(os.environ, YASMV_HOME=str(home)))
        timed_out = False
        try:
            while True:
                pid, status, usage = os.wait4(process.pid, os.WNOHANG)
                if pid: break
                if time.monotonic() - started >= timeout:
                    timed_out = True
                    os.killpg(process.pid, signal.SIGKILL)
                    _, status, usage = os.wait4(process.pid, 0)
                    break
                time.sleep(.005)
            process.returncode = os.waitstatus_to_exitcode(status)
        except BaseException:
            try: os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError: pass
            process.wait()
            raise
    elapsed = (time.monotonic() - started) * 1000
    measured = dict(process_wall_ms=elapsed, peak_rss_kib=usage.ru_maxrss, hard_timeout=timed_out,
                    exit_code=process.returncode)
    return measured, stdout_path.read_text(), stderr_path.read_text()


def summarize(result, expected):
    status, outcome = result['status'], result['outcome']
    if status not in ('completed', 'unknown'):
        raise ValueError('Benchmark query failed: ' + json.dumps(result))
    if status == 'unknown':
        if any(result.get(k) for k in ('trace', 'proof', 'optimality')):
            raise ValueError('Incomplete query published evidence')
    elif outcome in ('reachable', 'violated'):
        if expected == 'safe' or not result.get('trace'):
            raise ValueError('Unexpected or missing counterexample')
    elif outcome in ('unreachable', 'proven'):
        if expected == 'unsafe' or result['scope'] != 'unbounded':
            raise ValueError('Unexpected unbounded proof')
    elif outcome != 'holds_bounded':
        raise ValueError('Unexpected benchmark outcome: ' + outcome)
    proof = result.get('proof') or {}
    invariant = proof.get('invariant')
    if result.get('proof_method') == 'interpolation':
        required = {'initial_containment', 'transition_closure', 'target_exclusion'}
        if (not proof.get('verified') or not invariant or
                set(proof.get('obligations', {})) != required or
                set(proof['obligations'].values()) != {'unsatisfiable'} or
                invariant['identity'] != result['identity']):
            raise ValueError('Interpolation proof lacks verified evidence')
    record = {key: result.get(key) for key in
              ('status', 'outcome', 'scope', 'stop_reason', 'proof_method', 'checked_depths', 'statistics')}
    record['invariant_nodes'] = len(invariant['nodes']) if invariant else None
    record['invariant_bytes'] = len(json.dumps(invariant, separators=(',', ':')).encode()) if invariant else None
    record['witness_depth'] = len(result['trace']['steps']) - 1 if result.get('trace') else None
    record['verified'] = proof.get('verified', False)
    return record


def run_query(binary, model, case, query, directory, timeout, home):
    request = directory / 'request.json'
    request.write_text(json.dumps(dict(version=1, model=str(model), inputs=case.get('inputs', {}), query=query)))
    command = [binary, '--quiet', '--query-file', request, '--sat-random-seed', '0']
    if case.get('root'): command += ['--root', case['root']]
    measurement, stdout, stderr = measure(command, directory, timeout, home)
    if measurement['hard_timeout']:
        return measurement, None
    if measurement['exit_code'] not in (0, 3):
        raise ValueError('Checker exited unsuccessfully: ' + stderr + stdout)
    result = json.loads(stdout)
    if (measurement['exit_code'], result['status']) not in ((0, 'completed'), (3, 'unknown')):
        raise ValueError('Checker status and exit code disagree')
    return measurement, result


def prepare(case, directory, translator):
    source = ROOT / case['source']
    if source.suffix != '.ll': return source, {}
    started = time.monotonic()
    run = subprocess.run([str(translator), '--emit-scalar-bundle', '--diagnostics=json', str(source)],
                         text=True, capture_output=True, timeout=60, check=True)
    files = check_artifact(json.loads(run.stdout))
    path = directory / 'model.smv'
    path.write_text(files['model.smv'])
    return path, dict(translation_ms=(time.monotonic() - started) * 1000,
                      artifact_id=json.loads(files['manifest.json'])['artifact_id'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, default=ROOT / 'tests/benchmarks/interpolation/cases.json')
    parser.add_argument('--binary', type=Path, default=ROOT / 'yasmv')
    parser.add_argument('--home', type=Path, default=ROOT)
    parser.add_argument('--translator', type=Path, default=ROOT / 'llvm2smv/llvm2smv')
    parser.add_argument('--case', action='append', help='Select case IDs; repeat to select several')
    parser.add_argument('--runs', type=int, default=3)
    parser.add_argument('--wall-ms', type=int, default=5000)
    parser.add_argument('--hard-timeout', type=float, default=15)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if not sys.platform.startswith('linux'): parser.error('Peak RSS accounting requires Linux')
    if not 1 <= args.runs <= 100 or args.wall_ms <= 0 or not args.wall_ms / 1000 < args.hard_timeout < 3600:
        parser.error('Require 1..100 runs and 0 < wall budget < hard timeout < 3600 seconds')
    cases = json.loads(args.manifest.read_text())['cases']
    if args.case:
        if set(args.case) - {case['id'] for case in cases}: parser.error('Unknown case ID')
        cases = [case for case in cases if case['id'] in args.case]
    binary = args.binary.resolve()
    solver = subprocess.run([str(binary), '--solver-info'], text=True, capture_output=True, check=True)
    report = dict(version=1, complete=False, platform=platform.platform(), machine=platform.machine(),
                  binary_sha256=digest(binary), runner_sha256=digest(Path(__file__)), solver=json.loads(solver.stdout),
                  manifest_sha256=digest(args.manifest), runs=args.runs, wall_ms=args.wall_ms,
                  hard_timeout_seconds=args.hard_timeout, cases=[],
                  notes=['Serial fresh processes; no warmup or compiled-session reuse. Method order rotates each repetition.',
                         'Process wall and Linux peak RSS include loading, compilation, solving, internal verification and serialization.',
                         'Standalone counterexample replay is mandatory and timed separately. LLVM translation is outside query timing.',
                         'Depth caps apply to bounded search, k-induction and interpolation. Simple-path exhaustion has only the shared wall budget.',
                         'UNKNOWN and bounded negatives are retained, never counted as unbounded proofs. Hard timeouts have no evidence or solver counters.',
                         'Small fixed workloads are a baseline, not a scalability or default-selection claim.'])
    report['cpu'] = next((line.split(':', 1)[1].strip() for line in Path('/proc/cpuinfo').read_text().splitlines()
                          if line.startswith('model name')), platform.machine())
    makefile = args.home / 'Makefile'
    report['build_flags'] = [line for line in makefile.read_text().splitlines()
                             if line.startswith(('CXX = ', 'CXXFLAGS = ', 'CADICAL_'))] if makefile.exists() else []
    compiler = next((line.split(' = ', 1)[1] for line in report['build_flags'] if line.startswith('CXX = ')), None)
    if compiler:
        report['compiler'] = subprocess.check_output(shlex.split(compiler) + ['--version'], text=True).splitlines()[0]
    if any(Path(c['source']).suffix == '.ll' for c in cases): report['translator_sha256'] = digest(args.translator)
    # Save each completed sample so interrupted benchmark runs remain inspectable.
    def save():
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    with tempfile.TemporaryDirectory(prefix='yasmv-imc-benchmark-') as temporary:
        directory = Path(temporary)
        for case in cases:
            model, translation = prepare(case, directory, args.translator)
            row = dict(case, source_sha256=digest(ROOT / case['source']), model_sha256=digest(model),
                       translation=translation, methods={method: dict(query=query_for(case, method, args.wall_ms), samples=[])
                                                       for method in METHODS})
            report['cases'].append(row)
            identity = None
            for repeat in range(args.runs):
                for method in METHODS[repeat % 4:] + METHODS[:repeat % 4]:
                    group = row['methods'][method]
                    measurement, result = run_query(binary, model, case, group['query'], directory,
                                                    args.hard_timeout, args.home)
                    sample = dict(repetition=repeat, **measurement)
                    if result is not None:
                        sample.update(summarize(result, case['expected']))
                        if identity is None: identity = result['identity']
                        elif identity != result['identity']: raise ValueError('Method model/configuration identities differ')
                        if result.get('trace'):
                            replay_measurement, replay = run_query(binary, model, case,
                                dict(operation='validate-trace', trace=result['trace'], limits=dict(wall_ms=args.wall_ms)),
                                directory, args.hard_timeout, args.home)
                            if replay is None or replay['status'] != 'completed' or replay['outcome'] != 'valid':
                                raise ValueError('Counterexample failed standalone replay')
                            sample['replay'] = dict(replay_measurement, outcome='valid')
                    else:
                        sample.update(status='unknown', outcome=None, stop_reason='hard_timeout')
                    group['samples'].append(sample)
                    group['median_process_wall_ms'] = statistics.median(s['process_wall_ms'] for s in group['samples'])
                    peaks = [s['peak_rss_kib'] for s in group['samples'] if s['peak_rss_kib'] is not None]
                    group['max_peak_rss_kib'] = max(peaks) if peaks else None
                    save()
                    print(case['id'], method, repeat + 1, sample['outcome'], round(sample['process_wall_ms']), flush=True)
            row['identity'] = identity
            save()
    report['complete'] = True
    save()


if __name__ == '__main__':
    main()

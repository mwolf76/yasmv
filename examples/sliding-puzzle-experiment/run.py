#!/usr/bin/env python3
"""Run the 63-puzzle controls, finite induction probes, and unbounded interpolation."""
import argparse
import importlib.util
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
from generate import boards, neighbors
from check import slide
spec = importlib.util.spec_from_file_location('benchmark', ROOT / 'tools/benchmark-interpolation.py')
benchmark = importlib.util.module_from_spec(spec)
spec.loader.exec_module(benchmark)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--wall-ms', type=int, default=120000)
    parser.add_argument('--output', type=Path, default=HERE / 'results')
    args = parser.parse_args()
    if args.wall_ms <= 0: parser.error('--wall-ms must be positive')
    args.output.mkdir(parents=True, exist_ok=True)
    model = HERE / 'puzzle-63.smv'
    initial, goal = boards(8)
    adjacent, _ = neighbors(8, 63)[0]
    successor = initial.copy()
    successor[63], successor[adjacent] = successor[adjacent], successor[63]
    target = ' && '.join(f'cell_{i} = {v}' for i,v in enumerate(successor))
    jobs = [('initial', dict(operation='check-init')),
            ('one-slide', dict(operation='reach', target=target, limits=dict(depth=1))),
            *[(f'induction-{k}', dict(operation='prove-property',
                    property=dict(name='safe', expression='!GOAL'), limits=dict(depth=k))) for k in (1, 2, 4)],
            ('interpolation', dict(operation='reach', strategy='interpolation', target='GOAL'))]
    report = dict(version=1, model_sha256=benchmark.digest(model), binary_sha256=benchmark.digest(ROOT/'yasmv'),
                  side=8, complete=False, runs=[])
    for name, query in jobs:
        query.setdefault('limits', {})['wall_ms'] = args.wall_ms if name == 'interpolation' else 30000
        measurement, result = benchmark.run_query(ROOT/'yasmv', model, {}, query, args.output,
                                                  query['limits']['wall_ms']/1000 + 20, ROOT)
        (args.output/(name+'-request.json')).write_text(json.dumps(dict(version=1, model=str(model), query=query), indent=2)+'\n')
        if result is not None:
            (args.output/(name+'.json')).write_text(json.dumps(result, indent=2)+'\n')
        row = dict(name=name, query=query, **measurement, status=result['status'] if result else 'unknown',
                   outcome=result['outcome'] if result else None,
                   stop_reason=result['stop_reason'] if result else 'hard_timeout',
                   statistics=result.get('statistics') if result else None)
        if name in ('initial', 'one-slide'):
            assert result and result['status']=='completed', 'Control query did not complete'
            assert result['outcome']==('satisfiable' if name=='initial' else 'reachable')
        if result and name.startswith('induction'):
            row['step_status'] = (result.get('proof') or {}).get('step_status')
            trace = (result.get('proof') or {}).get('induction_counterexample', {}).get('trace')
            if trace:
                frames = trace['steps']
                for i, frame in enumerate(frames):
                    board = [int(frame['values'][f'cell_{j}']) for j in range(64)]
                    assert sorted(board) == list(range(64))
                    assert (board == goal) == (i == len(frames)-1)
                    if i < len(frames)-1:
                        expected = slide(board,8,frame['values']['move'])
                        assert expected == tuple(int(frames[i+1]['values'][f'cell_{j}']) for j in range(64))
                row['induction_path_checked'] = True
            if result['status']=='completed': assert row['step_status']=='satisfiable'
        if name=='interpolation' and result:
            if result['status']=='completed':
                assert result['outcome']=='unreachable' and result['proof']['verified']
            else: assert result['proof'] is None and result['trace'] is None
        if result and result.get('trace'):
            _, replay = benchmark.run_query(ROOT/'yasmv', model, {},
                dict(operation='validate-trace', trace=result['trace'], limits=dict(wall_ms=30000)), args.output, 50, ROOT)
            assert replay and replay['status']=='completed' and replay['outcome']=='valid'
            row['trace_replayed'] = True
        report['runs'].append(row)
        (args.output/'summary.json').write_text(json.dumps(report, indent=2)+'\n')
        print(name, row['status'], row['outcome'], row.get('step_status'), round(measurement['process_wall_ms']), flush=True)
    # Shared scratch files are not evidence; named requests/results above are.
    for name in ('request.json', 'stdout.txt', 'stderr.txt'):
        (args.output/name).unlink(missing_ok=True)
    report['complete'] = True
    (args.output/'summary.json').write_text(json.dumps(report,indent=2)+'\n')


if __name__ == '__main__': main()

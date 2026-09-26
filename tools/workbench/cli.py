"""Structured agent transport and human result rendering; terminal input belongs to yasmv."""
import argparse
import json
import os
from pathlib import Path
import signal
import sys

from .client import Client, capabilities, completed, exit_code
from . import protocol


def render(result):
    if result['status'] != 'completed':
        print('!! ' + result['status'].upper() + ': ' + result.get('stop_reason', 'error'))
        for diagnostic in result.get('diagnostics', []):
            print('   ' + diagnostic.get('message', str(diagnostic)))
        return
    data = result.get('data')
    if isinstance(data, dict):
        if 'directory' in data:
            print(('-- Workspace cleared: ' if data.get('cleared') else '-- Workspace: ') + data['directory'])
            for key, value in data.get('selections', {}).items():
                if value: print('   ' + key + ': ' + value)
        elif 'expressions' in data:
            print('-- ' + data['kind'].capitalize())
            for name, expression in data['expressions'].items(): print('   ' + name + ' = ' + expression)
            if not data['expressions']: print('   (none)')
        elif 'symbols' in data:
            print('-- State symbols')
            for name, symbol in data['symbols'].items():
                t = symbol['type']
                spelling = ('int' if t.get('signed') else 'uint') + str(t['width']) if t['kind'] == 'integer' else t['kind']
                if t['kind'] == 'enum': spelling = '{' + ', '.join(t['literals']) + '}'
                if t['kind'] == 'array': spelling = json.dumps(t)
                flags = ', '.join(key for key in ('frozen', 'input') if symbol.get(key))
                print('   ' + name + ' : ' + spelling + (' (' + flags + ')' if flags else ''))
        elif 'operations' in data:
            print('-- Agent operations (yasmv --agent)')
            for name, operation in data['operations'].items(): print('   ' + name + '  ' + operation['description'])
        elif 'items' in data:
            print('-- ' + str(data['total']) + ' entries')
            for item in data['items']: print('   ' + '  '.join(f'{key}={value}' for key, value in item.items()))
        elif 'revision' in data:
            print('-- Revision: ' + data['revision'])
            if data.get('validation') == 'not_checked': print('   Expressions will be checked when used.')
        elif 'job_id' in data and 'request' not in data:
            print('-- Job: ' + data['job_id'])
            if 'cancel_requested' in data: print('   Cancellation requested: ' + str(data['cancel_requested']).lower())
        else:
            print(json.dumps(data, indent=2))
        return
    labels = {'reachable': 'Target is reachable', 'unreachable': 'Target is unreachable within the bound',
              'violated': 'Safety property violated', 'holds_bounded': 'Safety holds through the bound; unbounded result is unknown',
              'proven': 'Safety property proven by verified induction', 'simulated': 'Simulation done', 'deadlocked': 'Simulation deadlocked',
              'exported': 'Scenario exported', 'matched': 'Implementation matches the scenario', 'diverged': 'Implementation diverges from the scenario',
              'unsatisfiable': 'Constraints are inconsistent', 'satisfiable': 'Constraints are satisfiable'}
    progress = result.get('progress_summary') or result.get('progress')
    if progress:
        labels.update(proven='Every execution eventually reaches the goal', violated='Guaranteed progress violated', valid='Progress artifact validated')
        if progress['kind'] == 'loop':
            print('-- Repeating execution: last state returns to state ' + str(progress['loop_start']))
        elif progress['kind'] == 'deadlock':
            print('-- Execution gets stuck before reaching the goal')
        if progress.get('vacuous'):
            print('-- VACUOUS: no legal initial states; this does not establish a runnable system')
        assumptions = progress.get('assumptions', progress.get('query', {}).get('assumptions', []))
        if assumptions: print('   Under assumptions: ' + ', '.join(assumptions))
    print('-- ' + labels.get(result.get('outcome'), result.get('outcome') or 'Completed'))
    if result.get('optimality'): print('   Shortest witness: ' + str(result['optimality']['depth']) + ' transitions')
    if result.get('job_id'): print('   Job: ' + result['job_id'])
    if result.get('scenario_id'): print('   Scenario: ' + result['scenario_id'])
    replay = result.get('implementation_replay', {})
    if replay.get('first_divergence'): print('   First divergence: ' + json.dumps(replay['first_divergence']))
    if result.get('evidence'): print('   Evidence: ' + ', '.join(result['evidence']) + ' (job show -full)')


def error_result(error):
    internal = not isinstance(error, (ValueError, OSError, UnicodeError))
    return protocol.failure('', 'internal_error' if internal else 'validation_error', str(error))


def agent(client):
    """Sequential command envelopes; submitted jobs run concurrently in Engine."""
    seen = set()
    status = 0
    for line in sys.stdin:
        identifier = None
        seq = 0
        def emit(event, data):
            nonlocal seq
            print(json.dumps(dict(version=1, request_id=identifier, seq=seq, event=event, **data), allow_nan=False), flush=True)
            seq += 1
        try:
            request = protocol.loads(line)
            protocol.fields(request, ('version', 'request_id', 'operation', 'arguments'), ('version', 'request_id', 'operation', 'arguments'))
            if type(request['version']) is not int or request['version'] != 1:
                raise ValueError('Unsupported protocol major version')
            identifier = request['request_id']
            if not isinstance(identifier, str) or not protocol.ID.fullmatch(identifier):
                identifier = None
                raise ValueError('Invalid request_id')
            if identifier in seen:
                raise ValueError('Duplicate request_id in this connection')
            seen.add(identifier)
            if not isinstance(request['operation'], str):
                raise ValueError('Operation must be a string')
            result = client.dispatch(request['operation'], request['arguments'], emit)
        except Exception as error:
            result = error_result(error)
        emit('result', {'result': result})
        status = status or exit_code(result)
        if client.stopping.is_set():
            break
    return status


def main(argv=None):
    parser = argparse.ArgumentParser(prog='yasmv --agent', description=__doc__)
    parser.add_argument('--store', type=Path, default=Path('.yasmv-workbench'))
    parser.add_argument('--binary', type=Path)
    parser.add_argument('--home', type=Path)
    parser.add_argument('--reuse-models', action='store_true')
    parser.add_argument('command', choices=('agent', 'capabilities', 'bridge'))
    client = None
    try:
        options = parser.parse_args(argv)
        if options.command == 'capabilities':
            print(json.dumps(completed(capabilities())))
            return 0
        if options.command == 'bridge':
            from .native import serve
            return serve(options)
        client = Client(options.store, options.binary, options.home or os.environ.get('YASMV_HOME'), options.reuse_models)
        def interrupt(signum, frame):
            if signum == signal.SIGTERM: client.stopping.set()
            if client.waiting: client.engine.cancel(client.waiting)
            else: raise KeyboardInterrupt
        signal.signal(signal.SIGINT, interrupt)
        signal.signal(signal.SIGTERM, interrupt)
        return agent(client)
    except KeyboardInterrupt:
        return 3
    except Exception as error:
        result = error_result(error)
        print(json.dumps(result))
        return exit_code(result)
    finally:
        if client: client.close()

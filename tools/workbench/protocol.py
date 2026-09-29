"""Versioned job protocol. No checker is started until the envelope is validated."""
import json
import math
import re

VERSION = 1
OPERATIONS = ('check-progress', 'validate-progress', 'shortest-reach', 'check-property', 'prove-property', 'validate-model', 'pick-state', 'reach', 'validate-trace', 'simulate', 'explain-init', 'explain-step', 'explain-reach', 'export-scenario', 'replay-scenario')
CAPABILITIES = {
    'version': VERSION, 'operations': list(OPERATIONS), 'events': ['started', 'progress', 'result'],
    'trace_version': 1, 'bounded_only': False, 'progress': {'form': 'universal-eventuality', 'backend': 'explicit-sat-graph', 'fairness': 'none', 'artifact_version': 1}, 'proof_methods': ['k-induction', 'interpolation', 'finite-graph-ranking'], 'interpolation': {'reach': 'unbounded', 'prove_property': 'positive-depth-cap', 'invariant_version': 1}, 'shortest_witnesses': True, 'compiled_sessions': 'process-snapshot', 'watch_types': ['boolean'],
    'explanations': ['initial', 'single_step_continuation', 'bounded_reach'],
    'scenario_adapters': ['retry-protocol-v1'], 'selected_prefix': True, 'process_isolation': True,
    'limits': ['states', 'depth', 'wall_ms', 'conflicts', 'propagations'],
}
ID = re.compile(r'^[a-zA-Z0-9_-]{1,80}$')


def loads(text):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError('Duplicate JSON field: ' + key)
            result[key] = value
        return result
    def finite(value):
        number = float(value)
        if not math.isfinite(number):
            raise ValueError('Nonfinite JSON number')
        return number
    try:
        value = json.loads(text, object_pairs_hook=pairs, parse_float=finite, parse_constant=finite)
    except RecursionError:
        raise ValueError('JSON nesting is too deep') from None
    pending = [(value, 0)]
    while pending:
        item, depth = pending.pop()
        if depth > 256:
            raise ValueError('JSON nesting exceeds 256 levels')
        if isinstance(item, dict):
            pending.extend((child, depth + 1) for child in item.values())
        elif isinstance(item, list):
            pending.extend((child, depth + 1) for child in item)
    return value


def fields(value, names, required=()):
    if not isinstance(value, dict) or set(value) - set(names) or set(required) - set(value):
        raise ValueError('Invalid object fields; expected ' + ', '.join(names))


def integer(value, low, high, name):
    if type(value) is not int or not low <= value <= high:
        raise ValueError(f'{name} must be an integer from {low} to {high}')


def expressions(value):
    if not isinstance(value, dict) or len(value) > 32:
        raise ValueError('Expected up to 32 named expressions')
    for key, expr in value.items():
        if not key or len(key) > 120 or not isinstance(expr, str) or not expr.strip() or len(expr) > 4096:
            raise ValueError('Invalid named expression')


def revision(value):
    fields(value, ('source', 'name', 'root', 'inputs', 'goals', 'watches', 'scenario', 'properties'), ('source',))
    if not isinstance(value['source'], str) or not value['source'].strip() or len(value['source'].encode()) > 1024 * 1024:
        raise ValueError('Source must contain 1 byte to 1 MiB')
    for key in ('name', 'root'):
        if key in value and (not isinstance(value[key], str) or len(value[key]) > 200):
            raise ValueError('Invalid ' + key)
    for key in ('inputs', 'goals', 'watches', 'properties'):
        expressions(value.get(key, {}))
    if value.get('scenario') is not None:
        from tools.scenario.format import metadata
        metadata(value['scenario'])
    result = dict(source=value['source'], name=value.get('name', 'Untitled model'), root=value.get('root', ''),
                inputs=value.get('inputs', {}), goals=value.get('goals', {}), watches=value.get('watches', {}))
    if 'properties' in value:
        result['properties'] = value['properties']
    if value.get('scenario') is not None:
        result['scenario'] = value['scenario']
    return result


def request(value):
    fields(value, ('version', 'request_id', 'revision', 'query', 'hard_timeout'), ('version', 'request_id', 'revision', 'query'))
    if type(value['version']) is not int or value['version'] != VERSION:
        raise ValueError('Unsupported protocol major version')
    for key in ('request_id', 'revision'):
        if not isinstance(value[key], str) or not ID.fullmatch(value[key]):
            raise ValueError('Invalid ' + key)
    timeout = value.get('hard_timeout', 60)
    if type(timeout) not in (int, float) or not math.isfinite(timeout) or not 0.05 <= timeout <= 300:
        raise ValueError('Hard timeout must be between 0.05 and 300 seconds')
    q = value['query']
    fields(q, ('operation', 'strategy', 'target', 'assumptions', 'limits', 'trace', 'trace_id', 'prefix_length', 'until', 'watches', 'explanation', 'scenario_id', 'implementation', 'property', 'progress'), ('operation',))
    op = q['operation']
    if op not in OPERATIONS:
        raise ValueError('Unsupported operation')
    for key in ('target', 'until'):
        if key in q and (not isinstance(q[key], str) or not q[key].strip() or len(q[key]) > 4096):
            raise ValueError('Invalid ' + key)
    if ('target' in q) != (op in ('reach', 'shortest-reach', 'explain-reach', 'check-progress')) or ('until' in q and op != 'simulate'):
        raise ValueError('Target is required only for reach; until is supported only for simulate')
    if op in ('check-property', 'prove-property'):
        if not isinstance(q.get('property'), str) or not q['property'].strip() or len(q['property']) > 120:
            raise ValueError('Select a named safety property from the revision')
    elif 'property' in q:
        raise ValueError('Property applies only to safety queries')
    strategy = q.get('strategy', 'auto')
    if strategy not in ('auto', 'interpolation'):
        raise ValueError('Unsupported query strategy')
    if strategy == 'interpolation' and op not in ('reach', 'prove-property'):
        raise ValueError('Interpolation requires unbounded reach or prove-property')
    unbounded = strategy == 'interpolation' and op == 'reach'
    limits = q.get('limits', {})
    if unbounded and 'depth' in limits:
        raise ValueError('Interpolation reach does not accept a depth limit')
    fields(limits, CAPABILITIES['limits'])
    for key, val in limits.items():
        integer(val, 0, 10000 if key == 'depth' else 2147483647, key)
    if not unbounded and op in ('reach', 'shortest-reach', 'simulate', 'explain-reach', 'check-property', 'prove-property'):
        integer(limits.get('depth'), 1 if op in ('simulate', 'prove-property') else 0, 10000, 'depth')
    elif 'depth' in limits and not (op == 'explain-step' and limits['depth'] == 1):
        raise ValueError('Depth applies only to reach and simulate')
    if op in ('check-progress', 'validate-progress'):
        integer(limits.get('states'), 1, 1000000, 'states')
        integer(limits.get('wall_ms'), 0, 2147483647, 'wall_ms')
    elif 'states' in limits and op != 'pick-state':
        raise ValueError('State limit applies only to progress and pick-state')
    if op == 'validate-progress':
        if not isinstance(q.get('progress'), dict):
            raise ValueError('Progress validation requires an artifact')
        if q.get('assumptions') or q.get('watches'):
            raise ValueError('Progress validation uses the artifact context')
    elif 'progress' in q:
        raise ValueError('Progress artifacts require validate-progress')
    assumptions = q.get('assumptions', [])
    if not isinstance(assumptions, list) or len(assumptions) > 32 or any(not isinstance(a, str) or not a.strip() or len(a) > 4096 for a in assumptions):
        raise ValueError('Invalid assumptions')
    if op == 'validate-model' and assumptions:
        raise ValueError('Model validation does not accept assumptions')
    if 'watches' in q:
        expressions(q['watches'])
    if op in ('validate-trace', 'simulate', 'explain-step', 'export-scenario'):
        if ('trace' in q) == ('trace_id' in q):
            raise ValueError('Specify exactly one trace or trace_id')
        if 'trace' in q and not isinstance(q['trace'], dict):
            raise ValueError('Trace must be an object')
        if 'trace_id' in q and (not isinstance(q['trace_id'], str) or not ID.fullmatch(q['trace_id'])):
            raise ValueError('Invalid trace_id')
    elif 'trace' in q or 'trace_id' in q:
        raise ValueError('This operation does not accept a trace')
    if 'prefix_length' in q:
        if op not in ('simulate', 'explain-step'):
            raise ValueError('Prefix length applies only to continuation')
        integer(q['prefix_length'], 1, 10001, 'prefix_length')
    explaining = op.startswith('explain-')
    if 'explanation' in q:
        if not explaining:
            raise ValueError('Explanation options require an explanation operation')
        options = q['explanation']
        fields(options, ('minimize', 'checks', 'wall_ms', 'active_ids', 'exact_depth'))
        for key in ('minimize', 'exact_depth'):
            if key in options and type(options[key]) is not bool:
                raise ValueError('Explanation flags must be Boolean')
        for key in ('checks', 'wall_ms'):
            if key in options:
                integer(options[key], 0, 1000000, key)
        if 'active_ids' in options and (not isinstance(options['active_ids'], list) or any(not isinstance(i, str) for i in options['active_ids'])):
            raise ValueError('active_ids must be an array of strings')
        if options.get('exact_depth') and op != 'explain-reach':
            raise ValueError('exact_depth applies only to explain-reach')
        if 'active_ids' in options and op == 'explain-reach' and not options.get('exact_depth'):
            raise ValueError('Reach subset rechecks require exact_depth')
    if explaining and q.get('watches'):
        raise ValueError('Explanation queries do not evaluate watches')
    if op == 'replay-scenario':
        if not isinstance(q.get('scenario_id'), str) or not ID.fullmatch(q['scenario_id']):
            raise ValueError('Scenario replay requires a saved scenario_id')
        if q.get('implementation') not in ('faulty', 'deduplicating'):
            raise ValueError('Select faulty or deduplicating implementation')
    elif 'scenario_id' in q or 'implementation' in q:
        raise ValueError('Scenario fields require replay-scenario')
    if op in ('export-scenario', 'replay-scenario') and (assumptions or 'watches' in q or limits):
        raise ValueError('Scenario jobs use saved query context and a hard timeout only')
    return value


def failure(request_id, reason, message, unknown=False):
    return {'version': VERSION, 'request_id': request_id, 'status': 'unknown' if unknown else 'error',
            'outcome': None, 'stop_reason': reason, 'complete': False, 'trace': None,
            'diagnostics': [{'code': reason, 'message': message}]}

"""Versioned job protocol. No checker is started until the envelope is validated."""
import json
import math
import re

VERSION = 1
OPERATIONS = ('validate-model', 'pick-state', 'reach', 'validate-trace', 'simulate')
CAPABILITIES = {
    'version': VERSION, 'operations': list(OPERATIONS), 'events': ['started', 'progress', 'result'],
    'trace_version': 1, 'bounded_only': True, 'watch_types': ['boolean'],
    'selected_prefix': True, 'process_isolation': True,
    'limits': ['depth', 'wall_ms', 'conflicts', 'propagations'],
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
    fields(value, ('source', 'name', 'root', 'inputs', 'goals', 'watches'), ('source',))
    if not isinstance(value['source'], str) or not value['source'].strip() or len(value['source'].encode()) > 1024 * 1024:
        raise ValueError('Source must contain 1 byte to 1 MiB')
    for key in ('name', 'root'):
        if key in value and (not isinstance(value[key], str) or len(value[key]) > 200):
            raise ValueError('Invalid ' + key)
    for key in ('inputs', 'goals', 'watches'):
        expressions(value.get(key, {}))
    return dict(source=value['source'], name=value.get('name', 'Untitled model'), root=value.get('root', ''),
                inputs=value.get('inputs', {}), goals=value.get('goals', {}), watches=value.get('watches', {}))


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
    fields(q, ('operation', 'target', 'assumptions', 'limits', 'trace', 'trace_id', 'prefix_length', 'until', 'watches'), ('operation',))
    op = q['operation']
    if op not in OPERATIONS:
        raise ValueError('Unsupported operation')
    for key in ('target', 'until'):
        if key in q and (not isinstance(q[key], str) or not q[key].strip() or len(q[key]) > 4096):
            raise ValueError('Invalid ' + key)
    if ('target' in q) != (op == 'reach') or ('until' in q and op != 'simulate'):
        raise ValueError('Target is required only for reach; until is supported only for simulate')
    limits = q.get('limits', {})
    fields(limits, CAPABILITIES['limits'])
    for key, val in limits.items():
        integer(val, 0, 10000 if key == 'depth' else 2147483647, key)
    if op in ('reach', 'simulate'):
        integer(limits.get('depth'), 1 if op == 'simulate' else 0, 10000, 'depth')
    elif 'depth' in limits:
        raise ValueError('Depth applies only to reach and simulate')
    assumptions = q.get('assumptions', [])
    if not isinstance(assumptions, list) or len(assumptions) > 32 or any(not isinstance(a, str) or not a.strip() or len(a) > 4096 for a in assumptions):
        raise ValueError('Invalid assumptions')
    if op == 'validate-model' and assumptions:
        raise ValueError('Model validation does not accept assumptions')
    if 'watches' in q:
        expressions(q['watches'])
    if op in ('validate-trace', 'simulate'):
        if ('trace' in q) == ('trace_id' in q):
            raise ValueError('Specify exactly one trace or trace_id')
        if 'trace' in q and not isinstance(q['trace'], dict):
            raise ValueError('Trace must be an object')
        if 'trace_id' in q and (not isinstance(q['trace_id'], str) or not ID.fullmatch(q['trace_id'])):
            raise ValueError('Invalid trace_id')
    elif 'trace' in q or 'trace_id' in q:
        raise ValueError('This operation does not accept a trace')
    if 'prefix_length' in q:
        if op != 'simulate':
            raise ValueError('Prefix length applies only to simulate')
        integer(q['prefix_length'], 1, 10001, 'prefix_length')
    return value


def failure(request_id, reason, message, unknown=False):
    return {'version': VERSION, 'request_id': request_id, 'status': 'unknown' if unknown else 'error',
            'outcome': None, 'stop_reason': reason, 'complete': False, 'trace': None,
            'diagnostics': [{'code': reason, 'message': message}]}

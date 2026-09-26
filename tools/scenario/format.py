"""Exact typed scenario export. A successful model replay is required to export."""
from copy import deepcopy
import hashlib
import json
import re

ACTIONS = ('SEND', 'DELIVER', 'DROP_REQUEST', 'ACK', 'DROP_ACK', 'RETRY', 'GIVE_UP', 'IDLE')
OBSERVATIONS = ('phase', 'retries', 'executions', 'seen')
POLICY = dict(reset=True, mode='deterministic', observe='initial_and_after_each_action',
              final_action='not_executed', comparison='exact_typed')


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True, allow_nan=False).encode()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def fields(value, required, optional=()):
    require(isinstance(value, dict) and set(required) <= set(value) <= set(required) | set(optional),
            'Invalid scenario fields; expected ' + ', '.join(required))


def typed(value, type_spec):
    require(isinstance(type_spec, dict), 'Missing value type')
    kind = type_spec.get('kind')
    if kind == 'integer':
        fields(type_spec, ('kind', 'width', 'signed'))
        width = type_spec['width']
        require(type(width) is int and 1 <= width <= 64 and type(type_spec['signed']) is bool, 'Invalid integer type')
        require(isinstance(value, str) and re.fullmatch(r'0|-?[1-9][0-9]*', value), 'Integer values must be canonical decimal strings')
        n = int(value)
        lo, hi = (-(1 << (width - 1)), (1 << (width - 1)) - 1) if type_spec['signed'] else (0, (1 << width) - 1)
        require(lo <= n <= hi, 'Integer value exceeds its declared width')
    elif kind == 'boolean':
        fields(type_spec, ('kind',))
        require(type(value) is bool, 'Expected Boolean observation')
    elif kind == 'enum':
        fields(type_spec, ('kind', 'literals'))
        require(isinstance(type_spec['literals'], list) and all(isinstance(v, str) for v in type_spec['literals']), 'Invalid enum type')
        require(isinstance(value, str) and value in type_spec['literals'], 'Unknown enum literal')
    elif kind == 'array':
        fields(type_spec, ('kind', 'length', 'element'))
        require(type(type_spec['length']) is int and isinstance(value, list) and len(value) == type_spec['length'], 'Invalid array length')
        for element in value:
            typed(element, type_spec['element'])
    elif kind == 'string':
        fields(type_spec, ('kind',))
        require(isinstance(value, str), 'Expected string argument')
    else:
        raise ValueError('Unsupported scenario value type')
    return value


def metadata(value):
    fields(value, ('version', 'name', 'description', 'models', 'goals', 'watches', 'default_depth', 'actions', 'adapter'))
    require(type(value['version']) is int and value['version'] == 1, 'Unsupported scenario metadata version')
    require(value['adapter'] == 'retry-protocol-v1', 'Unsupported adapter')
    require(isinstance(value['name'], str) and isinstance(value['description'], str), 'Invalid scenario description')
    require(type(value['default_depth']) is int and 0 <= value['default_depth'] <= 10000, 'Invalid default scenario depth')
    require(isinstance(value['models'], list) and value['models'], 'Missing scenario models')
    for model in value['models']:
        fields(model, ('name', 'file'))
        require(all(isinstance(v, str) and v for v in model.values()), 'Invalid model catalog entry')
    for key in ('goals', 'watches'):
        require(isinstance(value[key], dict) and all(isinstance(v, str) and v for v in value[key].values()), 'Invalid scenario expressions')
    a = value['actions']
    fields(a, ('symbol', 'controllable', 'observed', 'arguments', 'timing', 'mapping', 'observations'))
    require(isinstance(a['symbol'], str) and a['symbol'], 'Missing action symbol')
    require(isinstance(a['timing'], str), 'Invalid action timing description')
    require(isinstance(a['controllable'], list) and all(isinstance(s, str) for s in a['controllable']), 'Invalid controllable labels')
    require(len(a['controllable']) == len(set(a['controllable'])), 'Duplicate controllable label')
    require(isinstance(a['mapping'], dict) and set(a['mapping']) == set(a['controllable']), 'Every controllable action needs an explicit mapping')
    require(all(action in ACTIONS for action in a['mapping'].values()), 'Adapter does not support an action mapping')
    require(isinstance(a['observed'], list) and all(isinstance(s, str) for s in a['observed']), 'Invalid observed symbols')
    require(len(a['observed']) == len(set(a['observed'])), 'Duplicate observed symbol')
    require(isinstance(a['observations'], dict) and set(a['observations']) == set(a['observed']), 'Every observed symbol needs an explicit mapping')
    require(all(isinstance(v, str) for v in a['observations'].values()) and sorted(a['observations'].values()) == sorted(OBSERVATIONS), 'Adapter requires exactly phase, retries, executions and seen observations')
    require(isinstance(a['arguments'], dict) and set(a['arguments']) == {'job_id'}, 'Adapter requires the job_id argument')
    for mapping in a['arguments'].values():
        require(isinstance(mapping, dict) and (set(mapping) == {'symbol'} or set(mapping) == {'constant'}), 'Argument requires one symbol or constant binding')
        require(all(isinstance(v, str) and v for v in mapping.values()), 'Retry job IDs must map to a nonempty string or symbol')
    return deepcopy(value)


def build(trace, mapping, validation, revision=None, artifact_id=None):
    mapping = metadata(mapping)
    require(validation.get('status') == 'completed' and validation.get('outcome') == 'valid'
            and validation.get('trace') == trace, 'Export requires successful replay of this exact trace')
    a = mapping['actions']
    symbols = trace['symbols']
    require(a['symbol'] in symbols, 'Action symbol is not present in trace')
    action_type = symbols[a['symbol']]['type']
    require(action_type['kind'] == 'enum' and set(action_type['literals']) <= set(a['mapping']), 'All action literals need a controllable mapping')
    observations = {}
    for symbol in a['observed']:
        require(symbol in symbols, 'Missing observation mapping: ' + symbol)
        observations[a['observations'][symbol]] = dict(symbol=symbol, type=symbols[symbol]['type'])
    def observe(frame):
        return {field: typed(frame['values'].get(meta['symbol']), meta['type']) for field, meta in observations.items()}
    steps = trace['steps']
    require(bool(steps), 'Cannot export an empty trace')
    actions = []
    for k, frame in enumerate(steps[:-1]):
        label = typed(frame['values'].get(a['symbol']), action_type)
        require(label in a['mapping'], 'Unmapped action: ' + label)
        arguments = {}
        for name, binding in a['arguments'].items():
            if 'constant' in binding:
                value, typ = binding['constant'], {'kind': 'string'}
            else:
                symbol = binding['symbol']
                require(symbol in symbols, 'Missing argument symbol: ' + symbol)
                value, typ = frame['values'].get(symbol), symbols[symbol]['type']
            arguments[name] = dict(type=typ, value=typed(value, typ))
        require(arguments['job_id']['value'] == 'job-1', 'Toy adapter supports only job-1')
        actions.append(dict(index=k, label=label, action=a['mapping'][label], arguments=arguments, expected=observe(steps[k + 1])))
    value = dict(version=1, kind='executable-scenario', adapter=mapping['adapter'], policy=POLICY,
                 model_identity=trace['identity'], trace_identity=dict(id=trace['id'], digest=digest(trace), artifact_id=artifact_id),
                 revision=revision, query=trace['query'], model_trace_validation=dict(status='valid', method='checker-replay', recorded_at_export=True),
                 observations=observations, initial=observe(steps[0]), actions=actions)
    value['id'] = digest(value)
    validate(value)
    return value


def validate(value):
    fields(value, ('version', 'kind', 'id', 'adapter', 'policy', 'model_identity', 'trace_identity', 'revision', 'query', 'model_trace_validation', 'observations', 'initial', 'actions'))
    require(type(value['version']) is int and value['version'] == 1 and value['kind'] == 'executable-scenario', 'Unsupported executable scenario version')
    require(value['adapter'] == 'retry-protocol-v1' and value['policy'] == POLICY, 'Unsupported adapter or replay policy')
    payload = {k: v for k, v in value.items() if k != 'id'}
    require(value['id'] == digest(payload), 'Scenario integrity mismatch; content changed since export')
    require(isinstance(value['model_identity'], dict) and isinstance(value['query'], dict), 'Missing model/query identity')
    fields(value['trace_identity'], ('id', 'digest', 'artifact_id'))
    require(isinstance(value['trace_identity']['id'], str) and value['trace_identity']['id'], 'Missing trace identity')
    require(isinstance(value['trace_identity']['digest'], str) and re.fullmatch('[a-f0-9]{64}', value['trace_identity']['digest']), 'Invalid trace digest')
    require(value['revision'] is None or isinstance(value['revision'], str), 'Invalid revision identity')
    require(value['model_trace_validation'] == dict(status='valid', method='checker-replay', recorded_at_export=True), 'Missing export-time model validation record')
    require(isinstance(value['observations'], dict) and set(value['observations']) == set(OBSERVATIONS), 'Missing required observations')
    for field, entry in value['observations'].items():
        fields(entry, ('symbol', 'type'))
        require(isinstance(entry['symbol'], str), 'Invalid observation symbol')
        expected_kind = 'enum' if field == 'phase' else 'boolean' if field == 'seen' else 'integer'
        require(isinstance(entry['type'], dict), 'Missing observation type')
        require(entry['type'].get('kind') == expected_kind, 'Adapter observation type mismatch: ' + field)
    def check_observation(observation):
        fields(observation, OBSERVATIONS)
        for field, item in observation.items():
            typed(item, value['observations'][field]['type'])
    check_observation(value['initial'])
    require(isinstance(value['actions'], list) and len(value['actions']) <= 10000, 'Invalid action sequence')
    for index, action in enumerate(value['actions']):
        fields(action, ('index', 'label', 'action', 'arguments', 'expected'))
        require(type(action['index']) is int and action['index'] == index and isinstance(action['label'], str), 'Invalid action index or label')
        require(action['action'] in ACTIONS, 'Unsupported adapter action')
        fields(action['arguments'], ('job_id',))
        fields(action['arguments']['job_id'], ('type', 'value'))
        argument = action['arguments']['job_id']
        typed(argument['value'], argument['type'])
        require(argument['value'] == 'job-1', 'Toy adapter supports only job-1')
        check_observation(action['expected'])
    return value

"""Transport-independent command service for the yasmv CLI and agent protocol."""
from copy import deepcopy
from pathlib import Path
import threading
import time
import uuid

from . import protocol
from .engine import Engine, atomic, read


def schema(properties=None, required=()):
    return dict(type='object', properties=properties or {}, required=list(required), additionalProperties=False)


STRING = {'type': 'string', 'minLength': 1}
BOOL = {'type': 'boolean'}
INTEGER = {'type': 'integer', 'minimum': 0, 'maximum': 1000000}
REV = {'revision': STRING}
PAGE = {'offset': INTEGER, 'limit': {'type': 'integer', 'minimum': 1, 'maximum': 1000}}
QUERY = {'$ref': 'workbench-v1.schema.json#/properties/query'}
TIMEOUT = {'type': 'number', 'minimum': 0.05, 'maximum': 300}
OPERATIONS = {}


def operation(name, description, properties=None, required=()):
    OPERATIONS[name] = dict(description=description, arguments=schema(properties, required))


operation('capabilities', 'Discover operations, argument schemas, query contract, and exit codes.')
operation('workspace.show', 'Show workspace path and interactive selections.')
operation('workspace.clear', 'Delete saved workspace artifacts and selections; requires no active jobs.')
operation('model.load', 'Save source from a local file as an immutable revision and validate it.',
          dict(file=STRING, name=STRING, root=STRING, metadata=STRING, inputs={'type': 'object'}, hard_timeout=TIMEOUT), ('file',))
operation('model.save', 'Save a revision document and validate it.', {'document': {'type': 'object'}, 'hard_timeout': TIMEOUT}, ('document',))
operation('model.list', 'List immutable model revisions.', PAGE)
operation('model.use', 'Select an existing revision for interactive commands.', REV, ('revision',))
operation('model.show', 'Read an exact saved revision.', REV, ('revision',))
operation('model.symbols', 'Validate a model and return its state symbols, types, and source constraints.',
          dict(REV, hard_timeout=TIMEOUT), ('revision',))
operation('metadata.set', 'Save a named goal, safety property, watch, or input in a new revision.',
          dict(REV, kind={'type': 'string', 'enum': ['goals', 'properties', 'watches', 'inputs']}, name=STRING, expression=STRING),
          ('revision', 'kind', 'name', 'expression'))
operation('metadata.list', 'Read named goals, properties, watches, or inputs.',
          dict(REV, kind={'type': 'string', 'enum': ['goals', 'properties', 'watches', 'inputs']}), ('revision', 'kind'))
operation('scenario.configure', 'Save scenario mappings in a new revision.', dict(REV, file=STRING), ('revision', 'file'))
for name, description in [('query.run', 'Run a bounded job and return a compact result with evidence references.'),
                          ('job.submit', 'Start a job without waiting; use job.events, job.show, job.wait, or job.cancel.')]:
    operation(name, description, dict(REV, query=QUERY, job_id=STRING, hard_timeout=TIMEOUT), ('revision', 'query'))
operation('job.list', 'List compact job summaries.', PAGE)
operation('job.show', 'Retrieve a job summary, or its full request and evidence.', {'job_id': STRING, 'full': BOOL}, ('job_id',))
operation('job.wait', 'Wait for a job; return its compact result.', {'job_id': STRING}, ('job_id',))
operation('job.cancel', 'Cancel a running job in this runner.', {'job_id': STRING}, ('job_id',))
operation('job.events', 'Read a bounded page of job events after a sequence number.',
          {'job_id': STRING, 'after': {'type': 'integer', 'minimum': -1}, 'limit': PAGE['limit']}, ('job_id',))
operation('trace.list', 'List validated trace summaries, optionally filtered by revision.', dict(PAGE, revision=STRING))
operation('trace.show', 'Read a trace slice with exact values and optional change filtering.',
          dict(PAGE, trace_id=STRING, changes=BOOL), ('trace_id',))
operation('trace.compare', 'Compare corresponding states in two traces; revisions remain explicit.',
          dict(PAGE, trace_id=STRING, other=STRING), ('trace_id', 'other'))
operation('trace.export', 'Write the complete native trace artifact to a local file.', {'trace_id': STRING, 'file': STRING}, ('trace_id', 'file'))
operation('progress.show', 'Retrieve a saved progress certificate or counterexample.', {'job_id': STRING}, ('job_id',))
operation('progress.export', 'Export a portable progress artifact from a completed job.', {'job_id': STRING, 'file': STRING}, ('job_id', 'file'))
operation('trace.import', 'Replay a local native trace before saving it as trusted evidence.',
          dict(REV, file=STRING, hard_timeout=TIMEOUT), ('revision', 'file'))
operation('scenario.list', 'List saved executable scenarios.', PAGE)
operation('scenario.show', 'Read a complete executable scenario.', {'scenario_id': STRING}, ('scenario_id',))
operation('scenario.export', 'Replay a trace and export an executable scenario using its revision mappings.',
          dict(REV, trace_id=STRING, file=STRING, hard_timeout=TIMEOUT), ('revision', 'trace_id'))
operation('scenario.replay', 'Replay a saved scenario against a built-in implementation.',
          dict(REV, scenario_id=STRING, implementation={'type': 'string', 'enum': ['faulty', 'deduplicating']}, hard_timeout=TIMEOUT),
          ('revision', 'scenario_id', 'implementation'))


def capabilities():
    return dict(version=1, operations=OPERATIONS, query=protocol.CAPABILITIES,
                request_schema='cli-v1.schema.json', query_schema='workbench-v1.schema.json',
                context='Analysis requests require explicit revision IDs; interactive aliases resolve before dispatch.',
                events=['started', 'progress', 'result'],
                exit_codes={'completed': 0, 'invalid': 2, 'unknown': 3, 'internal_error': 4})


def validate(value, spec, name='arguments'):
    if '$ref' in spec:
        if not isinstance(value, dict):
            raise ValueError(name + ' must be an object')
        return  # Query semantics and nested fields are checked by protocol.request.
    types = {'object': dict, 'string': str, 'integer': int, 'boolean': bool}
    expected = spec.get('type')
    if expected == 'number':
        if type(value) not in (int, float):
            raise ValueError(name + ' must be a number')
    elif expected and type(value) is not types[expected]:
        raise ValueError(name + ' must be ' + expected)
    if expected == 'object' and 'properties' in spec:
        protocol.fields(value, spec['properties'], spec.get('required', []))
        for key, child in value.items():
            validate(child, spec['properties'][key], name + '.' + key)
    if 'enum' in spec and value not in spec['enum']:
        raise ValueError(name + ' must be one of ' + ', '.join(spec['enum']))
    if 'minLength' in spec and not value.strip():
        raise ValueError(name + ' must not be empty')
    if 'minimum' in spec and value < spec['minimum'] or 'maximum' in spec and value > spec['maximum']:
        raise ValueError(name + ' is outside the supported range')


def completed(data):
    return dict(status='completed', data=data)


def exit_code(result):
    if result['status'] == 'completed':
        return 0
    if result['status'] == 'unknown':
        return 3
    return 4 if result.get('stop_reason') in ('internal_error', 'worker_failed') else 2


def compact(result):
    result = deepcopy(result)
    evidence = {}
    if result.get('progress'):
        artifact = result['progress']
        result['progress_summary'] = {k: artifact[k] for k in ('kind', 'loop_start', 'vacuous', 'initial_satisfiable') if k in artifact}
        result['progress_summary']['target'] = artifact['query']['target']
        result['progress_summary']['assumptions'] = artifact['query'].get('assumptions', [])
    for key in ('trace', 'explanation', 'proof', 'constraints', 'watches', 'symbols', 'progress'):
        value = result.pop(key, None)
        if value is not None:
            evidence[key] = True
    result['evidence'] = evidence
    return result


def page(values, args):
    offset, limit = args.get('offset', 0), args.get('limit', 20)
    return dict(total=len(values), offset=offset, items=values[offset:offset + limit],
                next_offset=offset + limit if offset + limit < len(values) else None)


class Client:
    def __init__(self, directory, binary=None, home=None, reuse_models=False):
        self.engine = Engine(directory, binary, home, reuse_models)
        self.state_path = self.engine.directory / 'cli-state.json'
        try:
            self.state = read(self.state_path) if self.state_path.exists() else {}
            if not isinstance(self.state, dict):
                raise ValueError('Invalid CLI selection state')
        except Exception:
            self.engine.close()
            raise
        self.waiting = None
        self.stopping = threading.Event()

    def close(self):
        self.engine.close()

    def select(self, **values):
        self.state.update(values)
        atomic(self.state_path, self.state)

    def resolve(self, kind, value=None):
        if value and value != 'last':
            return value
        key = {'revision': 'revision', 'trace': 'trace_id', 'job': 'job_id', 'scenario': 'scenario_id'}[kind]
        if not self.state.get(key):
            raise ValueError('No selected ' + kind + '; supply an explicit ID')
        return self.state[key]

    def query(self, args, wait=True, emit=None):
        identifier = args.get('job_id', uuid.uuid4().hex)
        request = dict(version=1, request_id=identifier, revision=args['revision'], query=args['query'],
                       hard_timeout=args.get('hard_timeout', 60))
        self.engine.submit(request)
        self.select(job_id=identifier)
        if wait:
            return self.wait(identifier, emit)
        return completed(dict(job_id=identifier, revision=args['revision']))

    def wait(self, identifier, emit=None):
        self.engine.job(identifier)  # Reject unknown IDs before waiting.
        self.waiting = identifier
        sequence = -1
        try:
            while True:
                if self.stopping.is_set():
                    self.engine.cancel(identifier)
                for event in self.engine.events(identifier, sequence):
                    sequence = event['seq']
                    if event['event'] == 'result':
                        result = dict(event['result'], job_id=identifier, revision=self.engine.job(identifier)['request']['revision'])
                        selections = {key: result[key] for key in ('trace_id', 'scenario_id') if result.get(key)}
                        self.select(job_id=identifier, **selections)
                        return compact(result)
                    if emit:
                        emit(event['event'], dict(job_id=identifier, **{k: v for k, v in event.items() if k not in ('event', 'seq', 'version', 'request_id')}))
                time.sleep(.04)
        finally:
            self.waiting = None

    def save(self, document, timeout, emit):
        revision = self.engine.save_revision(document)
        result = self.query(dict(revision=revision['id'], query={'operation': 'validate-model'}, hard_timeout=timeout), emit=emit)
        if result['status'] == 'completed' and result.get('outcome') == 'valid':
            self.select(revision=revision['id'], trace_id=None, scenario_id=None)
        return dict(result, revision=revision['id'])

    def dispatch(self, name, args, emit=None):
        if name not in OPERATIONS:
            raise ValueError('Unknown operation: ' + name)
        validate(args, OPERATIONS[name]['arguments'])
        e = self.engine
        if name == 'capabilities':
            return completed(capabilities())
        if name == 'workspace.clear':
            with e.guard:
                e.clear()
                self.state = {}
                atomic(self.state_path, self.state)
            return completed(dict(directory=str(e.directory), cleared=True, selections={}))
        if name == 'workspace.show':
            return completed(dict(directory=str(e.directory), selections=self.state))
        if name == 'model.list':
            return completed(page(e.revisions(), args))
        if name in ('model.load', 'model.save'):
            if name == 'model.save':
                document = args['document']
            else:
                path = Path(args['file'])
                document = dict(source=path.read_text(), name=args.get('name', path.stem), root=args.get('root', ''), inputs=args.get('inputs', {}))
                if args.get('metadata'):
                    document['scenario'] = read(args['metadata'])
            return self.save(document, args.get('hard_timeout', 60), emit)
        if name in ('model.use', 'model.show'):
            rev = e.revision(args['revision'])
            if name == 'model.use':
                self.select(revision=rev['id'], trace_id=None, scenario_id=None)
                return completed(dict(revision=rev['id'], name=rev['name']))
            return completed(rev)
        if name == 'model.symbols':
            result = self.query(dict(args, query={'operation': 'validate-model'}), emit=emit)
            if result['status'] == 'completed':
                full = e.job(result['job_id'])['result']
                result['data'] = dict(symbols=full.get('symbols', {}), constraints=full.get('constraints', []))
            return result
        if name in ('metadata.set', 'metadata.list', 'scenario.configure'):
            rev = e.revision(args['revision'])
            if name == 'metadata.list':
                return completed(dict(revision=rev['id'], kind=args['kind'], expressions=rev.get(args['kind'], {})))
            rev.pop('id')
            if name == 'scenario.configure':
                rev['scenario'] = read(args['file'])
            else:
                rev.setdefault(args['kind'], {})[args['name']] = args['expression']
            saved = e.save_revision(rev)
            self.select(revision=saved['id'], trace_id=None, scenario_id=None)
            return completed(dict(revision=saved['id'], validation='not_checked'))
        if name in ('query.run', 'job.submit'):
            return self.query(args, wait=name == 'query.run', emit=emit)
        if name == 'job.wait':
            return self.wait(args['job_id'], emit)
        if name == 'job.cancel':
            e.job(args['job_id'])
            return completed(dict(job_id=args['job_id'], cancel_requested=e.cancel(args['job_id'])))
        if name == 'job.events':
            events = e.events(args['job_id'], args.get('after', -1))
            e.job(args['job_id'])
            values = deepcopy(events[:args.get('limit', 20)])
            for event in values:
                if event['event'] == 'result':
                    event['result'] = compact(event['result'])
            return completed(dict(job_id=args['job_id'], events=values,
                                  next_after=values[-1]['seq'] if values else args.get('after', -1), more=len(events) > len(values)))
        if name == 'job.show':
            job = e.job(args['job_id'])
            if not args.get('full') and job['result'] is not None:
                job['result'] = compact(job['result'])
            return completed(dict(job, job_id=args['job_id']))
        if name == 'job.list':
            values = [dict(job_id=j['request']['request_id'], revision=j['request']['revision'], operation=j['request']['query']['operation'],
                           status=j['result']['status'] if j['result'] else 'running', outcome=(j['result'] or {}).get('outcome')) for j in e.jobs()]
            return completed(page(values, args))
        if name == 'trace.list':
            return completed(page(sorted(e.traces(args.get('revision')), key=lambda t: t['id']), args))
        if name in ('trace.show', 'trace.compare', 'trace.export'):
            artifact = e.trace(args['trace_id'])
            trace = artifact['trace']
            if name == 'trace.export':
                atomic(args['file'], trace)
                return completed(dict(file=str(Path(args['file']).resolve()), trace_id=artifact['id']))
            if name == 'trace.compare':
                other = e.trace(args['other'])
                a, b = trace['steps'], other['trace']['steps']
                diffs = []
                for index in range(max(len(a), len(b))):
                    left = a[index]['values'] if index < len(a) else {}
                    right = b[index]['values'] if index < len(b) else {}
                    values = {key: dict(left=left.get(key), right=right.get(key), left_present=key in left, right_present=key in right)
                              for key in sorted(left.keys() | right.keys()) if (key in left, left.get(key)) != (key in right, right.get(key))}
                    if values or index >= min(len(a), len(b)):
                        diffs.append(dict(step=index, values=values))
                return completed(dict(page(diffs, args), left_revision=artifact['revision'], right_revision=other['revision'],
                                      left=artifact['id'], right=other['id']))
            values = deepcopy(trace['steps'])
            if args.get('changes'):
                for index in range(len(values) - 1, 0, -1):
                    values[index]['values'] = {key: value for key, value in values[index]['values'].items()
                                              if key not in values[index - 1]['values'] or value != values[index - 1]['values'][key]}
            result = dict(page(values, args), trace_id=artifact['id'], revision=artifact['revision'], symbols=trace['symbols'], validated=artifact['validated'])
            start, limit = args.get('offset', 0), args.get('limit', 20)
            result['watches'] = {key: values[start:start + limit] for key, values in artifact.get('watches', {}).items()}
            return completed(result)
        if name in ('progress.show', 'progress.export'):
            result = read(e.path('jobs', args['job_id']) / 'result.json')
            artifact = result.get('progress')
            if result['status'] != 'completed' or not artifact:
                raise ValueError('This job has no verified progress artifact')
            if name == 'progress.show':
                return completed(artifact)
            atomic(args['file'], artifact)
            return completed(dict(file=str(Path(args['file']).resolve()), job_id=args['job_id']))
        if name == 'trace.import':
            return self.query(dict(revision=args['revision'], query=dict(operation='validate-trace', trace=read(args['file'])),
                                   hard_timeout=args.get('hard_timeout', 60)), emit=emit)
        if name == 'scenario.list':
            return completed(page(sorted(e.scenarios(), key=lambda s: s['id']), args))
        if name == 'scenario.show':
            return completed(e.scenario(args['scenario_id']))
        if name in ('scenario.export', 'scenario.replay'):
            q = dict(operation='export-scenario', trace_id=args['trace_id']) if name == 'scenario.export' else dict(
                operation='replay-scenario', scenario_id=args['scenario_id'], implementation=args['implementation'])
            result = self.query(dict(revision=args['revision'], query=q, hard_timeout=args.get('hard_timeout', 60)), emit=emit)
            if result['status'] == 'completed' and name == 'scenario.export' and args.get('file'):
                atomic(args['file'], e.scenario(result['scenario_id']))
            return result
        raise ValueError('Unimplemented operation: ' + name)

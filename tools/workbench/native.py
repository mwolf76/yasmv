"""Private bridge: the C++ interpreter owns model/trace selection and the terminal."""
from copy import deepcopy
import contextlib
import io
import json
import os
from pathlib import Path
import signal
import sys

from .client import Client
from .cli import render, error_result
from .engine import encoded
from . import protocol


class Native:
    def __init__(self, options):
        self.options = options
        self.client = None
        self.context = {}
        self.trace_ids = {}

    def open(self, directory):
        if self.client and self.client.engine.active:
            raise ValueError('Wait for active jobs before switching workspaces')
        if self.client and Path(directory).resolve() == self.client.engine.directory:
            return
        candidate = Client(directory, self.options.binary, self.options.home or os.environ.get('YASMV_HOME'))
        if self.client: self.client.close()
        self.client = candidate
        self.trace_ids.clear()

    def bind(self, context, save_model=True):
        self.context = context
        if not self.client: self.open(self.options.store)
        c = self.client
        if not context:
            c.select(revision=None, trace_id=None, scenario_id=None)
            return
        if not save_model:
            return
        identity = context['identity']
        if any(identity.get('environment_constraints', [])):
            raise ValueError('Workspace jobs do not yet support native extra environment constraints')
        options = []
        for key, value in identity['options'].items():
            options.extend(['--' + key.replace('_', '-'), ('yes' if value else 'no') if type(value) is bool else str(value)])
        options.extend(['--cnf-microcode-directory', context['microcode_directory']])
        if c.engine.active and options != c.engine.worker_options:
            raise ValueError('Wait for active jobs before changing solver options')
        c.engine.worker_options = options
        document = context['document']
        old = c.engine.revision(c.state['revision']) if c.state.get('revision') else None
        if old and all(old.get(key) == document.get(key) for key in ('source', 'root', 'inputs')):
            revision = old
        else:
            # Reuse saved metadata for this exact native model/configuration.
            paths = sorted((c.engine.directory / 'revisions').glob('*/revision.json'), key=lambda p: p.stat().st_mtime_ns)
            matches = [c.engine.revision(p.parent.name) for p in paths]
            revision = next((r for r in reversed(matches) if all(r.get(k) == document.get(k) for k in ('source', 'root', 'inputs'))), None)
            if revision is None:
                document = deepcopy(document)
                if old and all(old.get(k) == document.get(k) for k in ('source', 'root')):
                    for key in ('goals', 'properties', 'watches', 'scenario'):
                        if key in old: document[key] = old[key]
                revision = c.engine.save_revision(document)
            c.select(revision=revision['id'], trace_id=None, scenario_id=None)
        c.engine.expected_identities[revision['id']] = identity
        c.select(revision=revision['id'])

    def current_revision(self):
        if not self.context:
            raise ValueError('No validated model is loaded; use read-model first')
        return self.client.resolve('revision')

    def trace(self, name=None):
        c = self.client
        if name and name != 'last':
            artifact = self.context.get('traces', {}).get(name)
            if artifact is None:  # Accept an explicit durable ID after model replay.
                artifact = c.engine.trace(name)['trace']
        else:
            artifact = self.context.get('trace')
        if not artifact:
            raise ValueError('No current trace; use pick-state, reach, or read-trace first')
        revision = self.current_revision()
        key = encoded([revision, artifact])
        if key not in self.trace_ids:
            result = c.query(dict(revision=revision, query=dict(operation='validate-trace', trace=artifact)))
            if result['status'] != 'completed' or result.get('outcome') != 'valid':
                raise ValueError('Selected native trace does not replay in the current model: ' + json.dumps(result.get('diagnostics', [])))
            self.trace_ids[key] = result['trace_id']
        c.select(trace_id=self.trace_ids[key])
        return self.trace_ids[key]

    def execute(self, request):
        op, args = request['operation'], deepcopy(request['arguments'])
        if op == 'workspace.open': self.open(args['directory'])
        if op == 'workspace.clear':
            if not self.client: self.open(self.options.store)
            result = self.client.dispatch(op, args)
            self.trace_ids.clear()
            return result, None
        needs_revision = op in ('metadata.set', 'metadata.list', 'model.symbols', 'query.run', 'scenario.configure', 'scenario.export', 'scenario.replay')
        self.bind(request['context'], save_model=needs_revision or op in ('workspace.open', 'trace.compare'))
        c = self.client
        if op in ('workspace.open', 'workspace.show'):
            result = deepcopy(c.dispatch('workspace.show', {}))
            selections = result['data']['selections']
            selections.pop('trace_id', None)
            selections['model'] = self.context.get('document', {}).get('name')
            selections['trace'] = self.context.get('trace_name')
            return result, None
        if needs_revision: args['revision'] = self.current_revision()
        background = args.pop('background', False)
        if op == 'query.run':
            q = args['query']
            if 'target' in q:
                q['target'] = c.engine.revision(args['revision'])['goals'].get(q['target'], q['target'])
            if q['operation'] in ('simulate', 'explain-step'):
                q['trace_id'] = self.trace(args.pop('native_trace', None))
            if background: op = 'job.submit'
        if op == 'trace.compare':
            args['trace_id'] = self.trace(args['trace_id'])
            args['other'] = self.trace(args['other'])
        if op == 'scenario.export': args['trace_id'] = self.trace()
        if op in ('scenario.replay', 'scenario.show'):
            args['scenario_id'] = c.resolve('scenario', args.get('scenario_id'))
        if op == 'progress.export': args['job_id'] = c.resolve('job')
        if op.startswith('job.') and op not in ('job.list', 'job.submit'):
            args['job_id'] = c.resolve('job', args.get('job_id'))
        result = c.dispatch(op, args)
        if op in ('metadata.set', 'scenario.configure'):
            c.engine.expected_identities[c.state['revision']] = self.context['identity']
        artifact = None
        # Only a newly completed analysis or waited job changes the native selection.
        if op in ('query.run', 'job.wait') and result.get('trace_id') and result['status'] == 'completed':
            artifact = c.engine.trace(result['trace_id'])['trace']
            self.trace_ids[encoded([result['revision'], artifact])] = result['trace_id']
        return result, artifact

    def close(self):
        if self.client: self.client.close()


def serve(options):
    native = Native(options)
    def interrupt(signum, frame):
        if native.client and native.client.waiting:
            native.client.engine.cancel(native.client.waiting)
            if signum == signal.SIGTERM: native.client.stopping.set()
        elif signum == signal.SIGTERM:
            raise KeyboardInterrupt
    signal.signal(signal.SIGINT, interrupt)
    signal.signal(signal.SIGTERM, interrupt)
    try:
        for line in sys.stdin:
            try:
                result, trace = native.execute(protocol.loads(line))
            except Exception as error:
                result, trace = error_result(error), None
            output = io.StringIO()
            with contextlib.redirect_stdout(output): render(result)
            print(json.dumps(dict(result=result, trace=trace, text=output.getvalue())), flush=True)
            if native.client and native.client.stopping.is_set(): break
    except KeyboardInterrupt:
        pass
    finally:
        native.close()
    return 0

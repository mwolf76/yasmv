#!/usr/bin/env python3
"""CLI and agent acceptance through the actual yasmv entry point."""
import json
import os
from pathlib import Path
import queue
import re
import pty
import select
import shutil
import time
import signal
import subprocess
import sys
import tempfile
import threading
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.workbench.client import OPERATIONS, capabilities


class CLITests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.store = Path(self.temp.name) / 'workspace with spaces'
        self.env = dict(os.environ, YASMV_HOME=str(ROOT))

    def run_cli(self, mode, script=None, code=0):
        command = [str(ROOT / 'yasmv'), '--' + mode]
        if mode == 'agent': command += ['--store', str(self.store)]
        result = subprocess.run(command, input=script, text=True, capture_output=True,
                                env=self.env, cwd=self.temp.name, timeout=180)
        self.assertEqual(result.returncode, code, result.stdout + result.stderr)
        return [json.loads(line) for line in result.stdout.splitlines()]

    def native(self, script, code=0, options=()):
        result = subprocess.run([str(ROOT / 'yasmv'), '--quiet', *options],
                                input=f'workspace open "{self.store}"\n' + script + '\nquit\n',
                                text=True, capture_output=True, env=self.env, cwd=self.temp.name, timeout=240)
        self.assertEqual(result.returncode, code, result.stdout + result.stderr)
        return result.stdout + result.stderr

    def results(self):
        return [json.loads(path.read_text()) for path in self.store.glob('jobs/*/result.json')]

    def test_retry_native_workflow(self):
        example = ROOT / 'examples/retry-protocol'
        export = Path(self.temp.name) / 'trace.json'
        scenario = Path(self.temp.name) / 'scenario.json'
        text = self.native(f'''read-model "{example}/faulty.smv"
goal set duplicate DUPLICATE
property set once !DUPLICATE
watch set duplicate DUPLICATE
show-symbols
reach duplicate -shortest -depth 12
list-traces
dump-trace -f json -o "{export}"
compare-traces workspace_1 workspace_1
scenario configure "{example}/scenario.json"
scenario export -o "{scenario}"
scenario replay faulty
scenario replay deduplicating
explain-step -at 0 -c action = ACK -minimize
job show -full
simulate -at 0 -c action = ACK -depth 1
read-trace "{export}"
check-property once -depth 12
''')
        self.assertIn('Shortest witness: 5 transitions', text)
        self.assertIn('[*] workspace_1', text)
        self.assertIn('Implementation matches', text)
        self.assertIn('Implementation diverges', text)
        self.assertIn('Constraints are inconsistent', text)
        self.assertIn('Safety property violated', text)
        self.assertTrue(scenario.exists())
        self.assertEqual(len(json.loads(export.read_text())['steps']), 6)
        self.assertTrue(any(r.get('explanation') for r in self.results()))
        proven = self.native(f'''read-model "{example}/deduplicating.smv"
property set once !DUPLICATE
prove-property once -depth 12
''')
        self.assertIn('Safety property proven', proven)

    def test_native_state_and_command_composition(self):
        source = ROOT / 'tests/models/query.smv'
        export = Path(self.temp.name) / 'trace.json'
        text = self.native(f'''do goal set target x; watch set current x;
pick-state
explain-step -at 0 -c x
on failure echo "blocked"
simulate -depth 1
list-traces
select-trace sim-1
select-trace workspace_1
simulate -k 1
dump-trace -f json -o "{export}"
''', options=(str(source),))
        self.assertIn('blocked', text)
        self.assertIn('workspace_1', text)
        self.assertEqual([step['values']['x'] for step in json.loads(export.read_text())['steps']], [False, True, False])

    def test_inputs_options_and_metadata_follow_native_model(self):
        source = Path(self.temp.name) / 'input.smv'
        source.write_text('MODULE main\n#input\nVAR enabled:boolean;\nVAR x:boolean;\nINIT x=enabled;\n')
        export = Path(self.temp.name) / 'trace.json'
        text = self.native(f'''set enabled TRUE
read-model "{source}"
goal set target x
reach target -depth 0
set enabled FALSE
goal list
reach !x -depth 0
dump-trace -f json -o "{export}"
''', options=('--word-width', '8', '--sat-random-seed', '7'))
        self.assertIn('target = x', text)
        artifact = json.loads(export.read_text())
        self.assertEqual(artifact['identity']['inputs'], {'enabled': 'FALSE'})
        self.assertEqual(artifact['identity']['options']['word_width'], 8)
        self.assertEqual(artifact['steps'][0]['values'], {'enabled': False, 'x': False})

    def test_invalid_model_cannot_use_workspace_selection(self):
        source = ROOT / 'tests/models/query.smv'
        self.native(f'read-model "{source}"\ngoal set target x')
        bad = Path(self.temp.name) / 'bad.smv'; bad.write_text('broken model')
        text = self.native(f'read-model "{bad}"\nshow-symbols', code=2)
        self.assertIn('No validated model', text)

    def test_unknown_and_batch_failure_status(self):
        source = ROOT / 'tests/models/query.smv'
        text = self.native(f'read-model "{source}"\nreach TRUE -depth 0 -wall-ms 0\ngoal list', code=3)
        self.assertIn('UNKNOWN', text)
        text = self.native('show-symbols\nworkspace show', code=2)
        self.assertIn('No validated model', text)
        self.assertIn('Workspace:', text)

    def test_native_jobs_and_workspace_switch(self):
        source = ROOT / 'tests/models/query.smv'
        other = Path(self.temp.name) / 'other'
        text = self.native(f'''read-model "{source}"
goal set target x
reach FALSE -depth 10000 -async
job cancel
job wait
workspace open "{other}"
show-symbols
workspace open "{self.store}"
goal list
reach target -shortest -depth 1 -async
job wait
list-traces
''', code=3)
        self.assertIn('cancelled', text)
        self.assertIn('target = x', text)
        self.assertIn('Shortest witness: 1 transitions', text)
        self.assertIn('[*] workspace_1', text)

    def test_native_exit_cancels_outstanding_work(self):
        source = ROOT / 'tests/models/query.smv'
        self.native(f'read-model "{source}"\nreach FALSE -depth 10000 -async')
        results = self.results()
        self.assertEqual(len(results), 1)
        self.assertEqual(results[0]['status'], 'unknown')
        self.assertEqual(results[0]['stop_reason'], 'cancelled')

    def test_command_words_remain_model_identifiers(self):
        source = Path(self.temp.name) / 'names.smv'
        source.write_text('MODULE main\nVAR property:boolean;\nVAR goal:boolean;\nINIT property && goal;\n')
        text = self.native(f'read-model "{source}"\nreach property && goal -depth 0')
        self.assertIn('Target is reachable', text)
        for command in ('reach TRUE -depth "bad"', 'explain-step -at 9223372036854775807'):
            with self.subTest(command=command):
                self.native(command, code=2)

    def test_exact_values_and_empty_initial_state(self):
        source = Path(self.temp.name) / 'wide.smv'
        source.write_text('#word-width 64\nMODULE main\nVAR x : uint64;\nINIT x = (uint64)18446744073709551615;\n')
        export = Path(self.temp.name) / 'trace.json'
        self.native(f'read-model "{source}"\nreach TRUE -depth 0\ndump-trace -f json -o "{export}"')
        self.assertEqual(json.loads(export.read_text())['steps'][0]['values']['x'], '18446744073709551615')
        source.write_text('MODULE main\nVAR x : boolean;\nINIT FALSE;\n')
        text = self.native(f'read-model "{source}"\nshow-symbols\nexplain-init')
        self.assertIn('x : boolean', text)
        self.assertIn('Constraints are inconsistent', text)

    def start_agent(self):
        process = subprocess.Popen([str(ROOT / 'yasmv'), '--agent', '--store', str(self.store), '--reuse-models'],
                                   stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                                   cwd=self.temp.name, env=self.env)
        messages = queue.Queue()
        process.cli_messages = messages
        def reader():
            for line in process.stdout:
                try:
                    messages.put(json.loads(line))
                except Exception as error:
                    messages.put(error)
        thread = threading.Thread(target=reader, daemon=True)
        thread.start()
        def cleanup():
            if process.poll() is None:
                process.stdin.close()
                try:
                    process.wait(timeout=30)
                except subprocess.TimeoutExpired:
                    process.kill(); process.wait()
            thread.join(timeout=5)
            process.stdout.close(); process.stderr.close()
        self.addCleanup(cleanup)
        counter = 0
        def send(operation, arguments):
            nonlocal counter
            counter += 1
            identifier = 'request-' + str(counter)
            process.stdin.write(json.dumps(dict(version=1, request_id=identifier, operation=operation, arguments=arguments)) + '\n')
            process.stdin.flush()
            events = []
            while True:
                event = messages.get(timeout=120)
                self.assertIsInstance(event, dict)
                self.assertEqual(event['request_id'], identifier)
                self.assertEqual(event['seq'], len(events))
                events.append(event)
                if event['event'] == 'result':
                    return event['result']
        return process, send

    def test_agent_jobs_cancellation_and_explicit_context(self):
        process, send = self.start_agent()
        source = 'MODULE main\n#inertial\nVAR x : boolean;\nINIT !x;\nTRANS x := !x;\n'
        loaded = send('model.save', {'document': {'source': source}})
        self.assertEqual(loaded['outcome'], 'valid')
        revision = loaded['revision']
        symbols = send('model.symbols', {'revision': revision})
        self.assertTrue(any(d['type']['kind'] == 'boolean' for d in symbols['data']['symbols'].values()))
        invalid = send('query.run', {'query': {'operation': 'pick-state'}})
        self.assertEqual(invalid['status'], 'error')
        started = send('job.submit', dict(revision=revision, job_id='long-job', query=dict(operation='reach', target='FALSE', limits={'depth': 10000})))
        self.assertEqual(started['data']['job_id'], 'long-job')
        self.assertTrue(send('job.cancel', {'job_id': 'long-job'})['data']['cancel_requested'])
        cancelled = send('job.wait', {'job_id': 'long-job'})
        self.assertEqual(cancelled['status'], 'unknown')
        self.assertEqual(cancelled['stop_reason'], 'cancelled')
        events = send('job.events', {'job_id': 'long-job', 'limit': 1})['data']
        self.assertEqual(len(events['events']), 1)
        self.assertTrue(events['more'])
        found = send('query.run', dict(revision=revision, query=dict(operation='shortest-reach', target='x', limits={'depth': 2})))
        self.assertEqual(found['optimality']['depth'], 1)
        trace_id = found['trace_id']
        other = send('model.save', {'document': {'source': source.replace('INIT !x', 'INIT x')}})['revision']
        rejected = send('query.run', dict(revision=other, query=dict(operation='simulate', trace_id=trace_id, limits={'depth': 1})))
        self.assertEqual(rejected['status'], 'error')
        self.assertEqual(send('query.run', dict(revision=revision, query=dict(operation='reach', target='x', limits={'depth': 0})))['outcome'], 'unreachable')
        process.stdin.close()
        self.assertEqual(process.wait(timeout=30), 2)  # First failed request stays reflected in batch status.

    def test_signal_cancels_synchronous_agent_job_and_recovers(self):
        process, send = self.start_agent()
        loaded = send('model.save', {'document': {'source': (ROOT / 'tests/models/query.smv').read_text()}})
        self.assertEqual(loaded['status'], 'completed')
        request = dict(version=1, request_id='interrupt', operation='query.run', arguments=dict(
            revision=loaded['revision'], query=dict(operation='reach', target='FALSE', limits={'depth': 10000})))
        process.stdin.write(json.dumps(request) + '\n')
        process.stdin.flush()
        first = process.cli_messages.get(timeout=30)
        self.assertEqual(first['event'], 'started')
        process.send_signal(signal.SIGINT)
        while True:
            event = process.cli_messages.get(timeout=60)
            if event['event'] == 'result':
                self.assertEqual(event['result']['status'], 'unknown')
                self.assertEqual(event['result']['stop_reason'], 'cancelled')
                break
        self.assertEqual(send('capabilities', {})['status'], 'completed')
        process.stdin.close()
        self.assertEqual(process.wait(timeout=30), 3)

    def test_protocol_recovery_and_discovery(self):
        good = dict(version=1, request_id='ok', operation='capabilities', arguments={})
        lines = ['{"version":1,"version":1}', json.dumps(dict(good, version=True)), json.dumps(good), json.dumps(good),
                 json.dumps(dict(good, request_id='next', arguments={'surprise': 1})),
                 json.dumps(dict(good, request_id='final'))]
        events = self.run_cli('agent', script='\n'.join(lines) + '\n', code=2)
        self.assertEqual([e['result']['status'] for e in events], ['error', 'error', 'completed', 'error', 'error', 'completed'])
        advertised = events[2]['result']['data']['operations']
        self.assertEqual(set(advertised), set(OPERATIONS))
        self.assertIn('revision', advertised['query.run']['arguments']['required'])
        discovery = self.run_cli('capabilities')[0]
        self.assertEqual(discovery['data'], capabilities())

    def test_native_help_lists_commands_and_opens_matching_pages(self):
        # Exercise the real help command without requiring a formatter or pager in CI.
        helpers = Path(self.temp.name) / 'helpers'
        helpers.mkdir()
        for name, body in [('nroff', 'cat "$@"'), ('less', 'cat')]:
            executable = helpers / name
            executable.write_text('#!/bin/sh\n' + body + '\n')
            executable.chmod(0o755)
        environment = dict(self.env, PATH=str(helpers) + os.pathsep + os.environ['PATH'])
        topics = ('workspace', 'goal', 'property', 'watch', 'show-symbols',
                  'capabilities', 'job', 'scenario', 'explain-init', 'explain-step',
                  'explain-reach', 'check-property', 'prove-property', 'compare-traces',
                  'reach')
        commands = 'help\n' + ''.join(f'help {topic} # open the listed topic\n' for topic in topics)
        result = subprocess.run([str(ROOT / 'yasmv'), '--quiet'],
                                input=commands + '86400 * 365\nquit\n',
                                text=True, capture_output=True, env=environment, timeout=30)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        for topic in topics:
            self.assertIn('- ' + topic + '\n', result.stdout)
        headings = re.findall(r'^YASMV manual\s+(\S+)\s*$', result.stdout, re.MULTILINE)
        self.assertEqual(headings, list(topics))
        self.assertNotIn('- workbench\n', result.stdout)
        self.assertIn('31536000', result.stdout)
        self.assertIn('workspace open "<directory>"', result.stdout)
        self.assertIn('versioned', result.stdout)
        self.assertNotIn('Syntax error', result.stderr)
        for command, message in [('help unknown_topic', 'Unknown help topic'),
                                 ('help workbench', 'Unknown help topic'),
                                 ('workbench', 'No validated model'),
                                 ('help workspace trailing', 'unexpected trailing command input')]:
            with self.subTest(command=command):
                failed = subprocess.run([str(ROOT / 'yasmv'), '--quiet'], input=command + '\nquit\n',
                                        text=True, capture_output=True, env=environment, timeout=30)
                self.assertEqual(failed.returncode, 2, failed.stdout + failed.stderr)
                self.assertIn(message, failed.stdout + failed.stderr)

    def test_single_prompt_source_snapshot_and_signal_recovery(self):
        master, slave = pty.openpty()
        process = subprocess.Popen([str(ROOT / 'yasmv')], stdin=slave, stdout=slave, stderr=slave,
                                   cwd=self.temp.name, env=self.env, close_fds=True)
        os.close(slave)
        pending = b''
        def expect(text):
            nonlocal pending
            end = time.monotonic() + 60
            while text not in pending:
                self.assertLess(time.monotonic(), end, pending.decode(errors='replace'))
                ready, _, _ = select.select([master], [], [], 1)
                if ready:
                    pending += os.read(master, 65536)
            pending = pending.split(text, 1)[1]
        try:
            expect(b'>> ')
            source = Path(self.temp.name) / 'snapshot.smv'
            source.write_text('MODULE main\n#inertial\nVAR x:boolean;\nINIT !x;\nTRANS x:=!x;\n')
            os.write(master, f'workspace open "{self.store}"\n'.encode())
            expect(b'>> ')
            os.write(master, f'read-model "{source}"\n'.encode())
            expect(b'>> ')
            source.write_text('broken source after load')
            os.write(master, b'reach x -shortest -depth 1\n')
            expect(b'Shortest witness: 1 transitions')
            expect(b'>> ')
            os.write(master, b'reach FALSE -depth 10000\n')
            # Wait until the worker has published its request before signalling.
            end = time.monotonic() + 30
            while not any('10000' in p.read_text() for p in self.store.glob('jobs/*/request.json')):
                self.assertLess(time.monotonic(), end)
                time.sleep(.05)
            process.send_signal(signal.SIGINT)
            expect(b'cancelled')
            expect(b'>> ')
            os.write(master, b'list-traces\n')
            expect(b'workspace_1')
            expect(b'>> ')
            os.write(master, b'quit\n')
            self.assertEqual(process.wait(timeout=20), 0)
        finally:
            if process.poll() is None:
                process.kill(); process.wait()
            os.close(master)

    def test_relocated_client_discovery(self):
        prefix = Path(self.temp.name) / 'installed'
        (prefix / 'bin').mkdir(parents=True)
        binary = prefix / 'bin/yasmv'
        shutil.copy2(ROOT / 'yasmv', binary)
        data = prefix / 'share/yasmv'
        (data / 'tools/workbench').mkdir(parents=True)
        # Marker proves the relocated data directory wins over build-tree fallback.
        (data / 'tools/workbench/launch.py').write_text('import json; print(json.dumps({"installed": True}))\n')
        result = subprocess.run([str(binary), '--capabilities'], capture_output=True, text=True,
                                env=self.env, cwd=self.temp.name, timeout=20)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout), {'installed': True})


if __name__ == '__main__':
    unittest.main()

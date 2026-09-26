"""Loopback HTTP transport and static UI. No external runtime dependencies."""
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import mimetypes
from pathlib import Path
import signal
import sys
from urllib.parse import parse_qs, urlsplit

from .engine import ROOT, read
from .protocol import CAPABILITIES, loads

STATIC = Path(__file__).with_name('static')


def examples():
    directory = ROOT / 'examples/retry-protocol'
    scenario = read(directory / 'scenario.json')
    return [dict(name=m['name'], source=(directory / m['file']).read_text(),
                 goals=scenario['goals'], watches=scenario['watches'], description=scenario['description'],
                 default_depth=scenario['default_depth']) for m in scenario['models']]


def make_server(engine, port=8765):
    class Handler(BaseHTTPRequestHandler):
        def log_message(self, format, *args):
            print(format % args, file=sys.stderr)

        def reply(self, code, value, content_type='application/json; charset=utf-8'):
            body = value if isinstance(value, bytes) else json.dumps(value).encode()
            self.send_response(code)
            self.send_header('Content-Type', content_type)
            self.send_header('Content-Length', str(len(body)))
            self.send_header('Cache-Control', 'no-store')
            self.send_header('X-Content-Type-Options', 'nosniff')
            self.send_header('Content-Security-Policy', "default-src 'self'; connect-src 'self'; img-src 'self' data:; style-src 'self'; script-src 'self'; base-uri 'none'; frame-ancestors 'none'")
            self.end_headers()
            self.wfile.write(body)

        def dispatch(self, post=False):
            try:
                host = self.headers.get('Host', '')
                valid = {f'127.0.0.1:{self.server.server_port}', f'localhost:{self.server.server_port}'}
                if host not in valid or self.headers.get('Origin', 'http://' + host) != 'http://' + host:
                    self.reply(403, {'error': 'Only same-origin loopback requests are accepted'})
                    return
                url = urlsplit(self.path)
                route = url.path.strip('/').split('/')
                body = None
                if post:
                    if self.headers.get('Content-Type', '').split(';')[0] != 'application/json':
                        raise ValueError('POST requires application/json')
                    size = int(self.headers.get('Content-Length', '0'))
                    if not 0 < size <= 16 * 1024 * 1024:
                        raise ValueError('Request body must be 1 byte to 16 MiB')
                    self.connection.settimeout(10)
                    body = loads(self.rfile.read(size).decode())
                if not post and url.path in ('/', '/index.html', '/app.js', '/style.css'):
                    path = STATIC / ('index.html' if url.path == '/' else url.path[1:])
                    self.reply(200, path.read_bytes(), mimetypes.guess_type(path)[0] + '; charset=utf-8')
                elif not post and route == ['api', 'capabilities']:
                    self.reply(200, CAPABILITIES)
                elif not post and route == ['api', 'examples']:
                    self.reply(200, examples())
                elif route == ['api', 'revisions']:
                    self.reply(201 if post else 200, engine.save_revision(body) if post else engine.revisions())
                elif not post and len(route) == 3 and route[:2] == ['api', 'revisions']:
                    self.reply(200, engine.revision(route[2]))
                elif route == ['api', 'jobs']:
                    self.reply(202, {'id': engine.submit(body)}) if post else self.reply(200, engine.jobs())
                elif len(route) >= 3 and route[:2] == ['api', 'jobs']:
                    if not post and len(route) == 3:
                        self.reply(200, engine.job(route[2]))
                    elif not post and len(route) == 4 and route[3] == 'events':
                        engine.job(route[2])
                        after = int(parse_qs(url.query).get('after', ['-1'])[0])
                        events = engine.events(route[2], after)
                        self.reply(200, ''.join(json.dumps(e) + '\n' for e in events).encode(), 'application/x-ndjson')
                    elif post and len(route) == 4 and route[3] == 'cancel':
                        engine.job(route[2])
                        self.reply(200, {'cancel_requested': engine.cancel(route[2])})
                    else:
                        self.reply(404, {'error': 'Unknown endpoint'})
                elif not post and route == ['api', 'traces']:
                    self.reply(200, engine.traces(parse_qs(url.query).get('revision', [None])[0]))
                elif not post and len(route) == 3 and route[:2] == ['api', 'traces']:
                    self.reply(200, engine.trace(route[2]))
                else:
                    self.reply(404, {'error': 'Unknown endpoint'})
            except FileNotFoundError:
                self.reply(404, {'error': 'Artifact not found'})
            except (ValueError, UnicodeError) as error:
                self.reply(400, {'error': str(error)})
            except (BrokenPipeError, ConnectionResetError):
                pass

        def do_GET(self):
            self.dispatch()

        def do_POST(self):
            self.dispatch(True)

    return ThreadingHTTPServer(('127.0.0.1', port), Handler)


def serve(engine, port):
    server = make_server(engine, port)
    print(f'Workbench: http://127.0.0.1:{server.server_port}  Artifacts: {engine.directory}', file=sys.stderr)
    previous = signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(KeyboardInterrupt()))
    try:
        server.serve_forever(poll_interval=0.2)
    except KeyboardInterrupt:
        pass
    finally:
        signal.signal(signal.SIGTERM, previous)
        server.server_close()

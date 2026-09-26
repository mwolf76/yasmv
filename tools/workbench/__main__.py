"""Local workbench or JSON Lines artifact runner (Python standard library only)."""
import argparse
import json
from pathlib import Path
import signal
import sys
import time

from .engine import Engine
from .protocol import CAPABILITIES, failure, loads


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--store', type=Path, default=Path('.yasmv-workbench'))
    parser.add_argument('--binary', type=Path)
    parser.add_argument('--home', type=Path)
    commands = parser.add_subparsers(dest='command', required=True)
    commands.add_parser('capabilities')
    serve = commands.add_parser('serve')
    serve.add_argument('--port', type=int, default=8765)
    put = commands.add_parser('revision')
    put.add_argument('file', type=Path, help='JSON revision containing source, inputs, goals and watches')
    run = commands.add_parser('run')
    run.add_argument('file', type=Path, help='One versioned job request; emits JSON Lines')
    args = parser.parse_args()
    if args.command == 'capabilities':
        print(json.dumps(CAPABILITIES))
        return 0
    engine = None
    identifier = ''
    try:
        engine = Engine(args.store, args.binary, args.home)
        if args.command == 'revision':
            print(json.dumps(engine.save_revision(loads(args.file.read_text()))))
        elif args.command == 'serve':
            from .server import serve
            serve(engine, args.port)
        else:
            request = loads(args.file.read_text())
            identifier = request.get('request_id', '') if isinstance(request, dict) else ''
            identifier = engine.submit(request)
            signal.signal(signal.SIGTERM, lambda *_: engine.cancel(identifier))
            signal.signal(signal.SIGINT, lambda *_: engine.cancel(identifier))
            seq = -1
            while True:
                for event in engine.events(identifier, seq):
                    print(json.dumps(event), flush=True)
                    seq = event['seq']
                    if event['event'] == 'result':
                        status = event['result']['status']
                        return 0 if status == 'completed' else 3 if status == 'unknown' else 2
                time.sleep(0.05)
        return 0
    except (OSError, ValueError) as error:
        result = failure(identifier, 'validation_error', str(error))
        print(json.dumps(dict(version=1, request_id=identifier, seq=0, event='result', result=result)), flush=True)
        return 2
    finally:
        if engine:
            engine.close()


if __name__ == '__main__':
    sys.exit(main())

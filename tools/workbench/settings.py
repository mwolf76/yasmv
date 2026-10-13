"""Typed interactive preferences. Structured clients never load this registry."""
from copy import deepcopy
import os
from pathlib import Path
import re

from . import protocol
from .engine import atomic


def duration(value):
    if value == 'unlimited':
        return -1
    match = re.fullmatch(r'([0-9]+)(ms|s|m|h)', value)
    if not match:
        raise ValueError('Expected a duration such as 30s, 5m, 2h, or unlimited')
    milliseconds = int(match[1]) * {'ms': 1, 's': 1000, 'm': 60000, 'h': 3600000}[match[2]]
    if not 0 <= milliseconds <= 2147483647:
        raise ValueError('Duration exceeds the supported millisecond range')
    return milliseconds


def execution(value):
    if value not in ('sync', 'async'):
        raise ValueError('Execution must be sync or async')
    return value


def states(value):
    if not re.fullmatch(r'[0-9]+', value) or not 1 <= int(value) <= 1000000:
        raise ValueError('State limit must be from 1 to 1000000')
    return int(value)


REGISTRY = {
    'check.timeout': ('30s', duration, 'Checking budget: duration or unlimited'),
    'check.execution': ('sync', execution, 'Launch checks synchronously or asynchronously'),
    'check.progress.max_states': ('10000', states, 'Maximum stored non-goal progress states'),
}


class Settings:
    def __init__(self):
        base = Path(os.environ.get('XDG_CONFIG_HOME', Path.home() / '.config'))
        self.path = base / 'yasmv' / 'settings.json'
        self.saved = {}
        self.session = {}
        if self.path.exists():
            document = protocol.loads(self.path.read_text())
            protocol.fields(document, ('version', 'settings'), ('version', 'settings'))
            if type(document['version']) is not int or document['version'] != 1 or not isinstance(document['settings'], dict):
                raise ValueError('Invalid settings file: ' + str(self.path))
            for name, value in document['settings'].items():
                self.validate(name, value)
            self.saved = document['settings']

    def validate(self, name, value):
        if name not in REGISTRY:
            raise ValueError('Unknown setting: ' + name)
        if not isinstance(value, str):
            raise ValueError('Setting values must be strings')
        return REGISTRY[name][1](value)

    def value(self, name):
        return self.session.get(name, self.saved.get(name, REGISTRY[name][0]))

    def inspect(self, name):
        self.validate(name, self.value(name) if name in REGISTRY else '')
        default, _, description = REGISTRY[name]
        return dict(name=name, value=self.value(name), default=default, description=description,
                    source='session' if name in self.session else 'user' if name in self.saved else 'builtin')

    def execute(self, args):
        action = args['action']
        name = args.get('name')
        if action == 'set':
            self.validate(name, args['value'])
            self.session[name] = args['value']
        elif action == 'reset':
            if name not in REGISTRY:
                raise ValueError('Unknown setting: ' + str(name))
            self.session[name] = REGISTRY[name][0]
        elif action == 'save':
            values = {key: self.value(key) for key in REGISTRY if self.value(key) != REGISTRY[key][0]}
            self.path.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
            atomic(self.path, dict(version=1, settings=values))
            self.saved, self.session = values, {}
        elif action not in ('list', 'show'):
            raise ValueError('Unknown settings action')
        names = [name] if name is not None else list(REGISTRY)
        return dict(status='completed', data=dict(settings=[self.inspect(key) for key in names], file=str(self.path)))

    def apply(self, args):
        args = deepcopy(args)
        query = args['query']
        limits = query.setdefault('limits', {})
        limits.setdefault('wall_ms', self.validate('check.timeout', self.value('check.timeout')))
        if query['variant'] == 'progress':
            limits.setdefault('states', self.validate('check.progress.max_states', self.value('check.progress.max_states')))
        args.setdefault('background', self.value('check.execution') == 'async')
        # The worker watchdog must not impose the old 60-second ceiling.
        args['hard_timeout'] = -1 if limits['wall_ms'] == -1 else max(.05, limits['wall_ms'] / 1000 + 10)
        return args

#!/usr/bin/env python3
"""Independent finite Python protocol; enumerate the graph or replay action labels."""
import argparse
from collections import deque
from dataclasses import dataclass, asdict
import json


@dataclass(frozen=True)
class State:
    phase: str = 'READY'
    retries: int = 0
    executions: int = 0
    seen: bool = False


def actions(s):
    return {'READY': ('SEND',), 'WAITING': ('DELIVER', 'DROP_REQUEST'),
            'REPLY': ('ACK', 'DROP_ACK'), 'RETRYING': ('RETRY',) if s.retries < 2 else ('GIVE_UP',),
            'DONE': ('IDLE',), 'FAILED': ('IDLE',)}[s.phase]


def step(s, action, deduplicate=False):
    if action not in actions(s):
        raise ValueError(f'{action} is not enabled in {s.phase}')
    phase, retries, executions, seen = s.phase, s.retries, s.executions, s.seen
    if action in ('SEND', 'RETRY'):
        phase = 'WAITING'
        retries += action == 'RETRY'
    elif action == 'DELIVER':
        phase = 'REPLY'
        executions += not (deduplicate and seen)
        seen = True
    elif action in ('DROP_REQUEST', 'DROP_ACK'):
        phase = 'RETRYING'
    elif action == 'ACK':
        phase = 'DONE'
    elif action == 'GIVE_UP':
        phase = 'FAILED'
    return State(phase, retries, executions, seen)


def graph(deduplicate=False):
    paths = {State(): []}
    queue = deque(paths)
    edges = []
    while queue:
        s = queue.popleft()
        for action in actions(s):
            t = step(s, action, deduplicate)
            edges.append((s, action, t))
            if t not in paths:
                paths[t] = paths[s] + [action]
                queue.append(t)
    duplicate = next((p for s, p in paths.items() if s.executions > 1), None)
    return {'states': len(paths), 'edges': len(edges), 'duplicate': duplicate,
            'max_distance': max(map(len, paths.values()))}


def replay(labels, deduplicate=False):
    states = [State()]
    for label in labels:
        states.append(step(states[-1], label, deduplicate))
    return states


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--deduplicate', action='store_true')
    parser.add_argument('actions', nargs='*')
    args = parser.parse_args()
    print(json.dumps([asdict(s) for s in replay(args.actions, args.deduplicate)] if args.actions
                     else graph(args.deduplicate), indent=2))

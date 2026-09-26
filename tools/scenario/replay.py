"""Implementation replay, independent of SAT/model-trace replay."""
import importlib.util
from pathlib import Path
import sys

from .format import validate, typed

# Only this built-in adapter is loadable. Metadata cannot name executable code.
path = Path(__file__).resolve().parents[2] / 'examples/retry-protocol/runner.py'
spec = importlib.util.spec_from_file_location('yasmv_retry_implementation', path)
protocol = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = protocol
spec.loader.exec_module(protocol)


def replay(scenario, implementation='faulty'):
    validate(scenario)
    if implementation not in ('faulty', 'deduplicating'):
        raise ValueError('Unknown implementation')
    state = protocol.State()
    result = dict(version=1, scenario_id=scenario['id'], implementation=implementation,
                  status='completed', outcome='matched', actions_executed=0,
                  model_trace_validation='recorded_at_export_not_rechecked',
                  observations=[], first_divergence=None, duplicate_execution=False)
    def check(expected, step, action):
        actual = dict(phase=state.phase, retries=str(state.retries), executions=str(state.executions), seen=state.seen)
        result['observations'].append(dict(step=step, values=actual))
        result['duplicate_execution'] = state.executions > 1
        for field, value in actual.items():
            try:
                typed(value, scenario['observations'][field]['type'])
                matches = value == expected[field]
            except ValueError:
                matches = False
            if not matches:
                result['outcome'] = 'diverged'
                result['first_divergence'] = dict(step=step, action=action, field=field, expected=expected[field], actual=value)
                return False
        return True
    if not check(scenario['initial'], 0, None):
        return result
    for action in scenario['actions']:
        try:
            state = protocol.step(state, action['action'], implementation == 'deduplicating')
        except ValueError as error:
            result['outcome'] = 'diverged'
            result['first_divergence'] = dict(step=action['index'] + 1, action=action['action'], field='action',
                                              expected='enabled', actual=str(error))
            break
        result['actions_executed'] += 1
        if not check(action['expected'], action['index'] + 1, action['action']):
            break
    return result

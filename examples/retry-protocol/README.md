# Retrying delivery

One logical job (`job-1`) is sent to a receiver. A request or acknowledgement may
be lost. The sender retries at most twice, then gives up. A faulty receiver
executes every delivered copy. The deduplicating receiver remembers the job and
executes it once, while still acknowledging subsequent deliveries.

## Explore

From the repository root, after building `yasmv` and extracting microcode:

```sh
python3 -m tools.workbench serve
```

Open the printed loopback URL. Choose **Faulty receiver**, save and validate, and
search for **Duplicate execution** through depth **12**. The first witness has
five transitions:

| Step | Action | Result |
| --- | --- | --- |
| 0 | SEND | Request enters the channel |
| 1 | DELIVER | First execution; reply becomes available |
| 2 | DROP_ACK | Sender does not receive the reply |
| 3 | RETRY | Same job is sent again |
| 4 | DELIVER | Second execution: `DUPLICATE` holds at state 5 |

The selected action in state `k` drives transition `k → k+1`. The final state's
action has not executed. Watches display `DUPLICATE`, `SUCCEEDED`, and `EXHAUSTED`.
Select a state and branch; every state through that selection is pinned,
including its outgoing action. To change that action, search afresh or select an
earlier prefix. The parent remains available for comparison and export.

Choose **Deduplicating receiver** and repeat. The result is **no witness through
depth 12**, with reachability beyond that bound reported as unknown. The UI does
not promote the example's independently enumerated result to a solver proof.

## Independent oracle

`runner.py` is a separate Python state machine. It does not parse SMV or call the
checker. It can enumerate its complete finite graph or execute explicit action
labels:

```sh
python3 examples/retry-protocol/runner.py
python3 examples/retry-protocol/runner.py --deduplicate
python3 examples/retry-protocol/runner.py SEND DELIVER DROP_ACK RETRY DELIVER
```

| Variant | Reachable protocol states | Edges | Maximum shortest distance | Duplicate execution |
| --- | ---: | ---: | ---: | --- |
| Faulty | 32 | 44 | 10 | First possible after 5 actions |
| Deduplicating | 20 | 28 | 8 | None |

These counts omit the SMV state's next action choice: the oracle represents
that choice as an edge label. Tests compare every state of the duplicate witness
with this oracle and retain the expected graph sizes and shortest failure path.

## Modeling choices and scope

- One fixed job ID, with two retries and at most three deliveries/executions.
- Four-bit unsigned counters with explicit invariants keep values within these
  bounds; no wraparound is reachable.
- Request and reply loss are separate controllable actions. There is no hidden
  fairness or eventual-delivery assumption.
- DONE and FAILED stutter forever under IDLE. RETRYING permits RETRY below the
  bound and GIVE_UP at the bound.
- `action` is an ordinary per-state variable. `#input` remains compile-time
  substitution and is not used as a time-varying action channel.
- `scenario.json` names goals, Boolean watches, controllable labels, observed
  state, and argument bindings. Its schema is
  [`scenario-v1.schema.json`](../../docs/formats/scenario-v1.schema.json).
- Durable deduplication, receiver crashes/restarts, multiple job IDs, concurrent
  senders, timers, and real network delivery are outside this tiny model. They
  are natural future variants, with explicit bounds and persistence assumptions.

General trace-to-executable-scenario export and adapter execution remain M3.

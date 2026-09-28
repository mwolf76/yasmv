# SAT solver parameters

yasmv uses the pinned CaDiCaL 3.0.1 backend. Solver output is suppressed so
machine-readable responses remain clean.

## Supported option

`--sat-random-seed=SEED` accepts integers from 0 through 2000000000.
The default is 0. Fractional, non-finite, negative, and out-of-range values are
rejected. Other CaDiCaL options use upstream defaults.

```sh
./yasmv --sat-random-seed=7 model.smv
./yasmv --solver-info
```

## Removed MiniSat options

The following flags are recognized only to produce a migration error. Omit
them; no approximate mapping to CaDiCaL is made.

- `--sat-random-var-freq`, `--sat-random-init-act`
- `--sat-ccmin-mode`, `--sat-phase-saving`, `--sat-garbage-frac`
- `--sat-var-decay`, `--sat-clause-decay`
- `--sat-luby-restart`, `--sat-restart-first`, `--sat-restart-inc`
- `--sat-elim`, `--sat-rcheck`, `--sat-asymm`, `--sat-grow`
- `--sat-clause-lim`, `--sat-subsumption-lim`, `--sat-simp-garbage-frac`

The supported yasmv CNF passes remain separate from native solver preprocessing.
Query propagation budgets now use cooperative search-propagation thresholds,
which may overshoot between callbacks; they are not strict preprocessing-work
limits. See [the backend guide](CADICAL_BACKEND.md) for build requirements,
budget semantics, cancellation, and provenance.

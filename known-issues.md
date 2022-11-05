This file contains a list of issues that were found at some point, and
will need to be fixed and covered by tests.

- constant-too-large check fails in the corner case (value = 1, width = 1)

```
 cat playground/bug.smv && echo 'pick-state; dump-traces' | ./yasmv playground/bug.smv
#word-width 1
MODULE bug;

VAR
	x : int;

INIT
	x = 1;


yasmv - Yet Another Symbolic Model Verifier
(c) 2011-2021, Marco Pensallorto < marco DOT pensallorto AT gmail DOT com >
https://github.com/mwolf76/yasmv


<< Ok
-- One feasible initial state found
-- Simulation trace for module `bug`
Witness: sim-1

:: @0
-- state
   x = -1
```

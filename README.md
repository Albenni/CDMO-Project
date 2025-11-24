# SAT

## Main scripts

- `sat_decision.py` – decision version.
- `sat_optimization.py` – optimization version.

Both scripts share the same command-line interface:

```bash
python sat_decision.py <N> <SOLVER>|--list [--sym|--no-sym]
python sat_optimization.py <N> <SOLVER>|--list [--sym|--no-sym]
```

### Arguments

`<N>`
Number of teams.

`<SOLVER>`
SAT solver to use. Supported solvers:

- `glucose3` – Glucose 3.0
- `minisat22` – MiniSat 2.2
- `z3` – Z3

`--list`
List available solvers.

`--sym`/`--no-sym`
Enable/disable symmetry breaking (default: enabled).

# MIP

--n
Number of teams.

--solver
Solver to use: cbc | highs.
Default: cbc.

--timelimit
Maximum total time (in seconds) for Stage A + Stage B.
Default: 300.

--splitA
Fraction of the total time to allocate to Phase A (0–1).
Default: 0.95.

--no_symbreak
Disable symmetry breaking (flag).

--no_warmstart
Disable the initial greedy warm-start (flag).

--no_objective
Run only Phase A, without orientation optimization (flag).

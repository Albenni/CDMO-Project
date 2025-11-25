# CP

## Main scripts

- script/run_cp.py — CP driver (decision and optimization).
- script/run_cp.sh — takes exactly one argument (N) and executes all Simmetry breaking / Implied Constraints variants for both decision and optimization models.

Syntax:
python script/run_cp.py <dec|opt> <N> [noSB] [noIC] [--solver <cp-sat|chuffed|gecode>]

### Arguments

- <dec|opt> : run the decision model (dec) or the optimization model (opt).
- <N> : number of teams (must be even; note n=4 is excluded by the period-usage rule).
- noSB / noIC (optional, positional) : disable Symmetry Breaking / Implied Constraints.
  Omit both for the baseline (SB+IC enabled).
- --solver <name> (optional) : force a single MiniZinc solver: cp-sat | chuffed | gecode.
  If omitted, the script runs its internal default list.

### Output

- Results are merged into: res/CP/<N>.json
- Each approach is keyed like:
  cp-sat_dec, cp-sat_dec_noSB, cp-sat_opt_noIC, chuffed_opt_noSB_noIC, ...

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

To run all tests in the report, use:

```bash
./run_mip.sh <N>
```

To run a single test:

```bash
python source/MIP/mip.py --n <N> --solver <cbc>
```

## Available Parameters

- --n
  Number of teams.

- --solver
  Solver to use: `cbc` | `highs`
  _Default: cbc_

- --timelimit
  Maximum total time (in seconds) for Stage A + Stage B.
  _Default: 300_

- --splitA
  Fraction of the total time allocated to Stage A (0–1).
  _Default: 0.95_

- --no_symbreak
  Disable symmetry breaking.

- --no_warmstart
  Disable the initial greedy warm-start.

- --no_objective
  Run only Stage A (skip orientation optimization).

- --executable_path
  Path to the CPLEX executable (required only for CPLEX, not for CBC or HiGHS).

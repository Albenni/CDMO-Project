#!/usr/bin/env python3
# Run both decision and optimization for all solvers (300s per solver).
# JSON keys: <solver>_dec and <solver>_opt. Fields:
# - time: int seconds (elapsed if solved/proven-opt; else 300)
# - optimal: DEC -> always False ; OPT -> True iff optimality proven
# - obj: DEC -> None ; OPT -> positive int if a solution exists, else None
# - sol: (n/2) x (n-1) matrix of [home, away] or [] if no solution

import json
import math
import os
import sys
import time
from datetime import timedelta

# line-buffered logs for immediate printing
try:
    sys.stdout.reconfigure(line_buffering=True)
    sys.stderr.reconfigure(line_buffering=True)
except Exception:
    pass


def log(msg: str):
    sys.stderr.write(msg + "\n")
    sys.stderr.flush()


try:
    from minizinc import Model, Solver, Instance, Status
except Exception:
    print("Please install the 'minizinc' Python package and the MiniZinc toolchain.")
    sys.exit(1)

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
SRC_CP = os.path.join(ROOT, "source", "CP")
OUTDIR = os.path.join(ROOT, "res", "CP")

TLIMIT = 300  # fixed per-solver time limit (seconds)


def pick_solver(candidates):
    for name in candidates:
        try:
            return Solver.lookup(name), name
        except Exception:
            continue
    return None, None


def pack_solution(H, A, n):
    if H is None or A is None:
        return []
    periods, weeks = n // 2, n - 1
    data = []
    for p in range(periods):
        row = []
        for w in range(weeks):
            row.append([int(H[p][w]), int(A[p][w])])
        data.append(row)
    return data


def solve_once(model_path, n, solver_names, mode):
    """
    mode ∈ {'dec','opt'}.
    Returns (used_solver_name, result_dict) with:
      - time: elapsed if (dec & has_solution) or (opt & proven_opt), else TLIMIT
      - optimal: DEC -> False ; OPT -> proven_opt
      - obj: DEC -> None ; OPT -> int if a solution exists, else None
      - sol: solution matrix or []
    """
    solver, used = pick_solver(solver_names)
    if solver is None:
        return (
            used or solver_names[-1],
            {"time": TLIMIT, "optimal": False, "obj": None, "sol": []},
        )

    model = Model(model_path)
    inst = Instance(solver, model)
    inst["n"] = n

    log(f"[run] {used} | mode={mode} | tlimit={TLIMIT}s")
    t0 = time.perf_counter()
    try:
        res = inst.solve(timeout=timedelta(seconds=TLIMIT))
        elapsed = math.floor(time.perf_counter() - t0)
    except Exception as e:
        log(f"[run] {used} | ERROR: {e}")
        return used, {"time": TLIMIT, "optimal": False, "obj": None, "sol": []}

    status = res.status
    # API compat: has_solution may be a method
    has_solution = getattr(status, "has_solution", lambda: False)()
    proven_opt = (status == Status.OPTIMAL_SOLUTION) or (
        getattr(status, "name", "") in {"OPTIMAL_SOLUTION", "OPTIMAL"}
    )

    # pull arrays if there is a solution
    H = A = None
    if has_solution:
        try:
            H, A = res["H"], res["A"]
        except Exception:
            H = A = None

    # objective
    if mode == "dec":
        obj_field = None
    else:
        obj_field = (
            int(res.objective)
            if (
                has_solution and hasattr(res, "objective") and res.objective is not None
            )
            else None
        )

    # time policy
    time_field = (
        elapsed
        if ((mode == "dec" and has_solution) or (mode == "opt" and proven_opt))
        else TLIMIT
    )

    sol_field = (
        pack_solution(H, A, n)
        if (has_solution and H is not None and A is not None)
        else []
    )

    # optimal flag per your rule:
    # - DEC: always False
    # - OPT: True iff optimality proven
    optimal_field = False if mode == "dec" else proven_opt

    log(
        f"[done] {used} | mode={mode} | status={getattr(status,'name',status)} | "
        f"time={time_field}s | optimal={optimal_field} | obj={obj_field}"
    )

    return used, {
        "time": time_field,
        "optimal": bool(optimal_field),
        "obj": obj_field,
        "sol": sol_field,
    }


def main():
    if len(sys.argv) != 2:
        print("Usage: python run_cp.py N")
        sys.exit(1)

    n = int(sys.argv[1])

    # non-blocking guards
    if n % 2 != 0:
        log("[guard] n must be even; the model is defined for even n.")
    if n == 4:
        log("[guard] n=4 is infeasible with the 'at most 2 per period' constraint.")

    os.makedirs(OUTDIR, exist_ok=True)
    dec_model = os.path.join(SRC_CP, "sts_decision.mzn")
    opt_model = os.path.join(SRC_CP, "sts_opt.mzn")

    solver_specs = [
        ["gecode"],
        ["chuffed"],
        ["or-tools", "org.or-tools"],
    ]

    results = {}

    # decision runs (optimal always False)
    for spec in solver_specs:
        used_name, out = solve_once(dec_model, n, spec, "dec")
        key = used_name if used_name else "|".join(spec)
        if key == "or-tools":
            key = "ortools"
        results[f"{key}_dec"] = out

    # optimization runs (optimal True only if proven optimal)
    for spec in solver_specs:
        used_name, out = solve_once(opt_model, n, spec, "opt")
        key = used_name if used_name else "|".join(spec)
        if key == "or-tools":
            key = "ortools"
        results[f"{key}_opt"] = out

    out_path = os.path.join(OUTDIR, f"{n}.json")
    with open(out_path, "w") as fh:
        json.dump(results, fh, indent=2)
    log(f"[write] {out_path}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
# Decision-only runner (300s per solver). Writes <solver>_dec blocks only.
# Changes:
# - Gecode temporarily disabled
# - Better logging: explicit [skip] when OR-Tools is not available

import json, math, os, sys, time
from datetime import timedelta

# line-buffered logs (better live output in PowerShell)
try:
    sys.stdout.reconfigure(line_buffering=True)
    sys.stderr.reconfigure(line_buffering=True)
except Exception:
    pass


def log(msg: str):
    sys.stderr.write(msg + "\n")
    sys.stderr.flush()


try:
    from minizinc import Model, Solver, Instance
except Exception:
    print("Please install the 'minizinc' Python package and the MiniZinc toolchain.")
    sys.exit(1)

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
SRC_CP = os.path.join(ROOT, "source", "CP")
OUTDIR = os.path.join(ROOT, "res", "CP")

TLIMIT = 300  # fixed per-solver time limit (seconds)


def pick_solver(candidates):
    """Try to lookup any of the given solver IDs. Return (solver_obj, used_name) or (None, None)."""
    for name in candidates:
        try:
            s = Solver.lookup(name)
            # sanity: log found solver id
            log(f"[info] found solver id '{name}'")
            return s, name
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


def solve_dec(model_path, n, solver_names):
    solver, used = pick_solver(solver_names)
    if solver is None:
        used = "/".join(solver_names)
        log(f"[skip] {used} | mode=dec | solver not available (lookup failed)")
        return used, {"time": TLIMIT, "optimal": False, "obj": None, "sol": []}

    model = Model(model_path)
    inst = Instance(solver, model)
    inst["n"] = n

    log(f"[run] {used} | mode=dec | tlimit={TLIMIT}s")
    t0 = time.perf_counter()
    try:
        res = inst.solve(timeout=timedelta(seconds=TLIMIT), all_solutions=False)
        elapsed = math.floor(time.perf_counter() - t0)
    except Exception as e:
        log(f"[done] {used} | mode=dec | ERROR: {e}")
        return used, {"time": TLIMIT, "optimal": False, "obj": None, "sol": []}

    st = res.status
    has_solution = getattr(st, "has_solution", lambda: False)()

    H = A = None
    if has_solution:
        try:
            H, A = res["H"], res["A"]
        except Exception:
            H = A = None

    time_field = elapsed if has_solution else TLIMIT
    sol_field = (
        pack_solution(H, A, n)
        if (has_solution and H is not None and A is not None)
        else []
    )

    out = {"time": time_field, "optimal": False, "obj": None, "sol": sol_field}
    log(
        f"[done] {used} | mode=dec | status={getattr(st,'name',st)} | time={time_field}s | optimal={out['optimal']}"
    )
    return used, out


def main():
    if len(sys.argv) != 2:
        print("Usage: python run_cp.py N")
        sys.exit(1)
    n = int(sys.argv[1])

    if n % 2 != 0:
        log("[guard] n must be even; the model is defined for even n.")
    if n == 4:
        log("[guard] n=4 is infeasible with the 'at most 2 per period' constraint.")

    os.makedirs(OUTDIR, exist_ok=True)
    model_dec = os.path.join(SRC_CP, "sts_decision.mzn")

    # --- Solver pipeline (Gecode temporarily disabled) ---
    solver_specs = [
        # ["gecode"],  # disabled for now
        ["chuffed"],
        ["cp-sat"],  # OR-Tools CP-SAT
        ["highs"],
    ]

    results = {}
    for spec in solver_specs:
        used_name, out = solve_dec(model_dec, n, spec)
        # normalize key for or-tools
        key = used_name if used_name else "|".join(spec)
        if key == "or-tools":
            key = "ortools"
        results[f"{key}_dec"] = out

    out_path = os.path.join(OUTDIR, f"{n}.json")
    with open(out_path, "w") as fh:
        json.dump(results, fh, indent=2)
    log(f"[write] {out_path}")


if __name__ == "__main__":
    main()

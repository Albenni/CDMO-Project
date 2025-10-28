#!/usr/bin/env python3
# CP runner (300s per solver). Select DEC and/or OPT via flags below.

import json, math, os, sys, time
from datetime import timedelta

# ======= RUN SWITCHES (set here) =========================================
RUN_DEC = False  # run decision model?
RUN_OPT = True  # run optimization model?
# =========================================================================

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
    from minizinc.error import MiniZincError
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
            s = Solver.lookup(name)
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


def _extract_objective(res):
    """Return objective value if present (as int), else None."""
    val = None
    # Prefer explicitly named variable
    try:
        val = res["obj"]
    except Exception:
        val = None
    # Fallback: driver-provided objective
    if val is None:
        try:
            val = res.objective
        except Exception:
            val = None
    # Normalize to int if possible
    if val is not None:
        try:
            return int(val)
        except Exception:
            try:
                return int(float(val))
            except Exception:
                return None
    return None


def run_instance(model_path, n, solver_names, mode):
    solver, used = pick_solver(solver_names)
    if solver is None:
        used = "/".join(solver_names)
        log(f"[skip] {used} | mode={mode} | solver not available (lookup failed)")
        return used, {
            "time": TLIMIT,
            "optimal": (mode == "opt" and False),
            "obj": None,
            "sol": [],
        }

    model = Model(model_path)
    try:
        inst = Instance(solver, model)
    except MiniZincError as e:
        log(f"[skip] {used} | analyze failed: {e}")
        return used, {
            "time": TLIMIT,
            "optimal": (mode == "opt" and False),
            "obj": None,
            "sol": [],
        }

    inst["n"] = n

    log(f"[run] {used} | mode={mode} | tlimit={TLIMIT}s")
    t0 = time.perf_counter()
    try:
        res = inst.solve(timeout=timedelta(seconds=TLIMIT), all_solutions=False)
        elapsed = math.floor(time.perf_counter() - t0)
    except Exception as e:
        log(f"[done] {used} | mode={mode} | ERROR: {e}")
        return used, {
            "time": TLIMIT,
            "optimal": (mode == "opt" and False),
            "obj": None,
            "sol": [],
        }

    name = getattr(res.status, "name", str(res.status))
    has_solution = name in {"SATISFIED", "ALL_SOLUTIONS", "OPTIMAL_SOLUTION"}

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

    if mode == "dec":
        out = {"time": time_field, "optimal": False, "obj": None, "sol": sol_field}
    else:
        obj_val = _extract_objective(res) if has_solution else None
        is_optimal = name == "OPTIMAL_SOLUTION"
        out = {
            "time": time_field,
            "optimal": is_optimal,
            "obj": obj_val,
            "sol": sol_field,
        }

    log(
        f"[done] {used} | mode={mode} | status={name} | time={time_field}s | optimal={out['optimal']}"
        + (f" | obj={out['obj']}" if mode == "opt" else "")
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
    model_opt = os.path.join(SRC_CP, "sts_opt.mzn")

    solver_specs = [
        # "gecode"],  # GeCode
        ["cp-sat"],  # OR-Tools CP-SAT
        ["chuffed"],
        # ["org.minizinc.mip.highs"],  # optional; skip if not available
    ]

    results = {}
    for spec in solver_specs:
        if RUN_DEC:
            used_name, out = run_instance(model_dec, n, spec, mode="dec")
            key = used_name if used_name else "|".join(spec)
            if key == "or-tools":
                key = "ortools"
            results[f"{key}_dec"] = out

        if RUN_OPT:
            used_name, out = run_instance(model_opt, n, spec, mode="opt")
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

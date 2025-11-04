#!/usr/bin/env python3
# CP runner (300s). Usage: python run_cp.py <dec|opt> <N>
# - Tries all solvers in SOLVERS
# - Caps JSON time to TLIMIT
# - Merges with existing res/CP/<N>.json if present (keeps other mode's results)

import json, os, sys, time
from datetime import timedelta
from minizinc import Model, Solver, Instance

TLIMIT = 300  # seconds
SOLVERS = ["cp-sat", "chuffed", "gecode"]

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
SRC_CP = os.path.join(ROOT, "source", "CP")
OUTDIR = os.path.join(ROOT, "res", "CP")


def log(msg: str):
    print(msg, file=sys.stderr, flush=True)


def pack_solution(H, A, n: int):
    """Return [[[h,a] for w in weeks] for p in periods]."""
    if H is None or A is None:
        return []
    periods, weeks = n // 2, n - 1
    out = []
    for p in range(periods):
        row = []
        for w in range(weeks):
            row.append([int(H[p][w]), int(A[p][w])])
        out.append(row)
    return out


def run_one(model_path: str, n: int, solver_name: str, mode: str):
    """Run one model/solver; always cap time in JSON to TLIMIT."""
    try:
        solver = Solver.lookup(solver_name)
    except Exception:
        log(f"[skip] {solver_name} | not available")
        return None

    inst = Instance(solver, Model(model_path))
    inst["n"] = n

    log(f"[run]  {solver_name} | mode={mode} | tlimit={TLIMIT}s")
    t0 = time.perf_counter()
    try:
        res = inst.solve(timeout=timedelta(seconds=TLIMIT), all_solutions=False)
    except Exception as e:
        log(f"[done] {solver_name} | mode={mode} | ERROR: {e}")
        return {
            "time": TLIMIT,
            "optimal": (mode == "opt" and False),
            "obj": None,
            "sol": [],
        }

    elapsed = int(time.perf_counter() - t0)
    time_cap = min(elapsed, TLIMIT)

    status = getattr(res.status, "name", str(res.status))
    has_solution = status in {"SATISFIED", "ALL_SOLUTIONS", "OPTIMAL_SOLUTION"}

    H = A = None
    if has_solution:
        try:
            H, A = res["H"], res["A"]
        except Exception:
            H = A = None
    sol = pack_solution(H, A, n) if (H is not None and A is not None) else []

    if mode == "dec":
        out = {"time": time_cap, "optimal": False, "obj": None, "sol": sol}
    else:
        # Try named objective; fallback to solver-provided objective
        obj_val = None
        if has_solution:
            try:
                obj_val = int(res["obj"])
            except Exception:
                try:
                    obj_val = int(res.objective) if res.objective is not None else None
                except Exception:
                    obj_val = None
        out = {
            "time": time_cap,
            "optimal": (status == "OPTIMAL_SOLUTION"),
            "obj": obj_val,
            "sol": sol,
        }

    log(
        f"[done] {solver_name} | mode={mode} | status={status} | time={out['time']}s | "
        f"optimal={out['optimal']}" + (f" | obj={out['obj']}" if mode == "opt" else "")
    )
    return out


def main():
    if len(sys.argv) != 3:
        print("Usage: python run_cp.py <dec|opt> <N>", file=sys.stderr)
        sys.exit(2)

    mode = sys.argv[1].lower()
    if mode not in {"dec", "opt"}:
        print("Mode must be 'dec' or 'opt'.", file=sys.stderr)
        sys.exit(2)
    n = int(sys.argv[2])

    os.makedirs(OUTDIR, exist_ok=True)

    # Resolve model path based on mode (supports both common layouts)
    model_dec_try = [
        os.path.join(SRC_CP, "source", "CP", "sts_decision.mzn"),
        os.path.join(SRC_CP, "sts_decision.mzn"),
    ]
    model_opt_try = [
        os.path.join(SRC_CP, "source", "CP", "sts_opt.mzn"),
        os.path.join(SRC_CP, "sts_opt.mzn"),
    ]
    model_path = None
    for cand in model_dec_try if mode == "dec" else model_opt_try:
        if os.path.exists(cand):
            model_path = cand
            break
    if model_path is None:
        print(f"Cannot find model for mode '{mode}'. Check paths.", file=sys.stderr)
        sys.exit(2)

    # Load existing JSON (to merge results of other mode/previous runs)
    out_path = os.path.join(OUTDIR, f"{n}.json")
    if os.path.exists(out_path):
        try:
            with open(out_path, "r") as fh:
                results = json.load(fh)
                if not isinstance(results, dict):
                    results = {}
        except Exception:
            results = {}
    else:
        results = {}

    # Run all solvers
    for solver_name in SOLVERS:
        out = run_one(model_path, n, solver_name, mode=mode)
        if out is not None:
            results[f"{solver_name}_{mode}"] = out

    # Write merged results (time capped)
    with open(out_path, "w") as fh:
        json.dump(results, fh, indent=2)
    log(f"[write] {out_path}")


if __name__ == "__main__":
    main()

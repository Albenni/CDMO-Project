#!/usr/bin/env python3
# CP runner (300s). Usage:
#   python run_cp.py <dec|opt> <N> [SOLVER] [noSB] [noImplied]
# - If SOLVER is omitted or 'all', tries all solvers in SOLVERS
# - Caps JSON time to TLIMIT
# - Merges with existing res/CP/<N>.json
# - Optional flags:
#     noSB       -> sets MiniZinc param SB=false and appends _noSB to JSON keys
#     noImplied  -> sets MiniZinc param IMPLIED=false and appends _noImplied to JSON keys

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


def build_suffix(sb_enabled: bool, implied_enabled: bool) -> str:
    parts = []
    if not sb_enabled:
        parts.append("noSB")
    if not implied_enabled:
        parts.append("noImplied")
    return "" if not parts else "_" + "_".join(parts)


def run_one(
    model_path: str,
    n: int,
    solver_name: str,
    mode: str,
    sb_enabled: bool,
    implied_enabled: bool,
    key_suffix: str,
):
    """Run one model/solver; always cap time in JSON to TLIMIT."""
    try:
        solver = Solver.lookup(solver_name)
    except Exception:
        log(f"[skip] {solver_name} | not available")
        return None

    inst = Instance(solver, Model(model_path))
    inst["n"] = n

    # Pass SB / IMPLIED (esistono nei modelli che mi hai mandato)
    try:
        inst["SB"] = sb_enabled
    except Exception:
        pass
    try:
        inst["IMPLIED"] = implied_enabled
    except Exception:
        pass

    log(
        f"[run]  {solver_name} | mode={mode} | SB={sb_enabled} | "
        f"IMPLIED={implied_enabled} | tlimit={TLIMIT}s"
    )
    t0 = time.perf_counter()
    try:
        res = inst.solve(timeout=timedelta(seconds=TLIMIT), all_solutions=False)
    except Exception as e:
        log(
            f"[done] {solver_name} | mode={mode} | SB={sb_enabled} | "
            f"IMPLIED={implied_enabled} | ERROR: {e}"
        )
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
        f"[done] {solver_name} | mode={mode}{key_suffix} | status={status} | "
        f"time={out['time']}s | optimal={out['optimal']}"
        + (f" | obj={out['obj']}" if mode == "opt" else "")
    )
    return out


def main():
    # Ora:
    #   python run_cp.py dec 8 cp-sat noImplied noSB
    # oppure (tutti i solver, compatibilità vecchia):
    #   python run_cp.py dec 8 noImplied noSB
    if len(sys.argv) < 3 or len(sys.argv) > 6:
        print(
            "Usage: python run_cp.py <dec|opt> <N> [SOLVER] [noSB] [noImplied]",
            file=sys.stderr,
        )
        sys.exit(2)

    mode = sys.argv[1].lower()
    if mode not in {"dec", "opt"}:
        print("Mode must be 'dec' or 'opt'.", file=sys.stderr)
        sys.exit(2)
    try:
        n = int(sys.argv[2])
    except Exception:
        print("N must be an integer.", file=sys.stderr)
        sys.exit(2)

    # Decidi se il terzo argomento è un solver o un flag
    solver_arg = None
    flag_args_start = 3
    if len(sys.argv) >= 4:
        third = sys.argv[3].lower()
        if third in {"nosb", "noimplied"}:
            # vecchio stile: nessun solver esplicito, solo flag
            solver_arg = None
            flag_args_start = 3
        else:
            # nuovo stile: solver esplicito
            solver_arg = sys.argv[3]
            flag_args_start = 4

    # Flags (da flag_args_start in poi)
    args = {a.lower() for a in sys.argv[flag_args_start:]}
    sb_enabled = "nosb" not in args
    implied_enabled = "noimplied" not in args

    key_suffix = build_suffix(sb_enabled, implied_enabled)

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

    # Carica eventuale JSON esistente
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

    # Decidi quali solver lanciare
    if solver_arg is None or solver_arg.lower() == "all":
        solvers_to_run = SOLVERS
    else:
        solvers_to_run = [solver_arg]

    # Run sui solver scelti
    for solver_name in solvers_to_run:
        out = run_one(
            model_path,
            n,
            solver_name,
            mode=mode,
            sb_enabled=sb_enabled,
            implied_enabled=implied_enabled,
            key_suffix=key_suffix,
        )
        if out is not None:
            results[f"{solver_name}_{mode}{key_suffix}"] = out

    # Scrivi JSON unificato
    with open(out_path, "w") as fh:
        json.dump(results, fh, indent=2)
    log(f"[write] {out_path}")


if __name__ == "__main__":
    main()

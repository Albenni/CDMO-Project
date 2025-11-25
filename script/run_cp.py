#!/usr/bin/env python3
# Usage:
#   python run_cp.py <dec|opt> <N> [noSB] [noIC|noImplied] [--solver <name1[,name2,...]>]
#
# Note:
# - Se non specifichi --solver, esegue sempre tutti i solver in SOLVERS.
# - Restituisce l'eventuale incumbent anche se lo status è UNKNOWN (sol -> H/A).
# - Merge non distruttivo in res/CP/<N>.json con chiavi diverse (es. cp-sat_opt_noSB).

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


def compute_key(solver_name: str, mode: str, SB: bool, IC: bool) -> str:
    tail = []
    if not SB:
        tail.append("noSB")
    if not IC:
        tail.append("noIC")
    suffix = "" if not tail else "_" + "_".join(tail)
    return f"{solver_name}_{mode}{suffix}"


def parse_solver_arg(argv_tail):
    """Legge --solver/-s <name1[,name2,...]> e restituisce la lista selezionata."""
    sel = []
    i = 0
    while i < len(argv_tail):
        tok = argv_tail[i]
        if tok in ("--solver", "-s") and i + 1 < len(argv_tail):
            sel.extend([x.strip() for x in argv_tail[i + 1].split(",") if x.strip()])
            i += 2
        else:
            i += 1
    return sel


def strip_solver_tokens(argv_tail):
    """Rimuove dall'elenco gli argomenti --solver/-s e il loro valore."""
    out = []
    i = 0
    while i < len(argv_tail):
        tok = argv_tail[i]
        if tok in ("--solver", "-s"):
            i += 2  # salta anche il valore
        else:
            out.append(tok)
            i += 1
    return out


def parse_flags(argv_tail):
    """Accetta 'noSB' e 'noIC|noImplied' (case-insensitive)."""
    SB = True
    IC = True
    for tok in argv_tail:
        t = tok.strip().lower()
        if t == "nosb":
            SB = False
        elif t in ("noic", "noimplied"):
            IC = False
        else:
            # argomento sconosciuto: ignora (tollerante)
            pass
    return SB, IC


def resolve_model_path(mode: str) -> str:
    # Supporta entrambe le strutture:
    #  - <repo>/source/CP/sts_*.mzn
    #  - <repo>/sts_*.mzn
    if mode == "dec":
        candidates = [
            os.path.join(SRC_CP, "source", "CP", "sts_decision.mzn"),
            os.path.join(SRC_CP, "sts_decision.mzn"),
        ]
    else:
        candidates = [
            os.path.join(SRC_CP, "source", "CP", "sts_opt.mzn"),
            os.path.join(SRC_CP, "sts_opt.mzn"),
        ]
    for cand in candidates:
        if os.path.exists(cand):
            return cand
    return ""


def run_one(model_path: str, n: int, solver_name: str, mode: str, SB: bool, IC: bool):
    """Esegue un modello/solver; accetta incumbents anche se status UNKNOWN; cap time in JSON."""
    try:
        solver = Solver.lookup(solver_name)
    except Exception:
        log(f"[skip] {solver_name} | not available")
        return None

    inst = Instance(solver, Model(model_path))
    inst["n"] = n
    # I modelli devono avere: bool: SB; bool: IMPLIED;
    inst["SB"] = SB
    inst["IMPLIED"] = IC

    log(f"[run]  {solver_name} | mode={mode} | SB={SB} | IC={IC} | tlimit={TLIMIT}s")
    t0 = time.perf_counter()
    try:
        res = inst.solve(timeout=timedelta(seconds=TLIMIT), all_solutions=False)
    except Exception as e:
        log(f"[done] {solver_name} | mode={mode} | ERROR: {e}")
        return {
            "time": TLIMIT,
            "status": "ERROR",
            "optimal": (mode == "opt" and False),
            "obj": None,
            "sol": [],
        }

    elapsed = int(time.perf_counter() - t0)
    time_cap = min(elapsed, TLIMIT)
    status = getattr(res.status, "name", str(res.status))

    # Estrai eventuale incumbent comunque
    H = A = None
    try:
        H, A = res["H"], res["A"]
    except Exception:
        H = A = None
    sol = pack_solution(H, A, n) if (H is not None and A is not None) else []

    obj_val = None
    if mode == "opt":
        try:
            obj_val = int(res["obj"])
        except Exception:
            try:
                obj_val = int(res.objective) if res.objective is not None else None
            except Exception:
                obj_val = None

    if mode == "dec":
        out = {
            "time": time_cap,
            "status": status,
            "optimal": False,
            "obj": None,
            "sol": sol,
        }
    else:
        out = {
            "time": time_cap,
            "status": status,
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
    if len(sys.argv) < 3:
        print(
            "Usage: python run_cp.py <dec|opt> <N> [noSB] [noIC|noImplied] [--solver <names>]",
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

    argv_tail = sys.argv[3:]
    selected_solvers = parse_solver_arg(argv_tail)
    tail_no_solver = strip_solver_tokens(argv_tail)
    SB, IC = parse_flags(tail_no_solver)
    solvers_to_run = selected_solvers if selected_solvers else SOLVERS

    os.makedirs(OUTDIR, exist_ok=True)
    model_path = resolve_model_path(mode)
    if not model_path:
        print(f"Cannot find model for mode '{mode}'. Check paths.", file=sys.stderr)
        sys.exit(2)

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

    for solver_name in solvers_to_run:
        out = run_one(model_path, n, solver_name, mode=mode, SB=SB, IC=IC)
        if out is not None:
            key = compute_key(solver_name, mode, SB, IC)
            results[key] = out

    with open(out_path, "w") as fh:
        json.dump(results, fh, indent=2)
    log(f"[write] {out_path}")


if __name__ == "__main__":
    main()

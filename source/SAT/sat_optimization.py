# sat_optimization.py
# "Optimization (fairness)" version for STS: minimize the max difference |home_i - away_i|.
# Implementation: incremental search on the bound d (0/1,2,...) with pseudo-Boolean constraints.
# CUMULATIVE JSON output: res/SAT/<n>.json with one entry per solver/approach.

import os
import sys
import json
import time

from pysat.card import CardEnc, EncType

from sat_solvers import (
    get_solver_kind,
    get_available_solvers_list,
    normalize_solver_name,
    solve_pysat_with_timeout,
)
from sts_sat_model import build_base_formula

TIME_LIMIT_SEC = 300  # 5 minutes

def _atmost_clauses(lits, bound, pool):
    """Use ladder for bound==1, seqcounter for bound>1 (robust)."""
    enc = EncType.ladder if bound == 1 else EncType.seqcounter
    return CardEnc.atmost(lits=lits, bound=bound, vpool=pool, encoding=enc).clauses

def _z3_add_cnf(s, clauses, pool):
    import z3
    # find the maximum variable index to create Bool vars
    try:
        max_var = pool.top
    except Exception:
        try:
            max_var = pool._next_id - 1
        except Exception:
            max_var = 0
            for c in clauses:
                for l in c:
                    if abs(l) > max_var:
                        max_var = abs(l)
    z3_vars = {i: z3.Bool(f"v{i}") for i in range(1, max_var + 1)}
    for c in clauses:
        s.add(z3.Or(*[(z3_vars[l] if l > 0 else z3.Not(z3_vars[-l])) for l in c]))
    return z3_vars


def build_solution_matrix_from_model_z3(model, pool, z3_vars, n):
    import z3
    sol = [[None for _ in range(n - 1)] for __ in range(n // 2)]
    for w in range(1, n):
        for p in range(1, n // 2 + 1):
            placed = False
            for i in range(1, n + 1):
                if placed:
                    break
                for j in range(1, n + 1):
                    if i == j:
                        continue
                    vid = pool.id(("X", i, j, w, p))
                    if model.evaluate(z3_vars[vid], model_completion=True):
                        sol[p - 1][w - 1] = [i, j]
                        placed = True
                        break
    return sol


def build_solution_matrix_from_model_pysat(model, pool, n):
    sol = [[None for _ in range(n - 1)] for __ in range(n // 2)]
    for lit in model:
        if lit > 0:
            key = pool.obj(lit)
            if key and key[0] == "X":
                _, i, j, w, p = key
                sol[p - 1][w - 1] = [i, j]
    return sol


def _add_fairness_constraints_pysat(solver, pool, home_vars_i, total_games, d):
    """Adds, for each team i:  ceil((T-d)/2) <= home_i <= floor((T+d)/2)  (with T = total_games)."""
    half_low = (total_games - d + 1) // 2  # ceil((T - d)/2)
    half_high = (total_games + d) // 2     # floor((T + d)/2)

    for _, lits in home_vars_i.items():
        # home_i <= half_high
        if half_high < total_games:
            for c in _atmost_clauses(lits, half_high, pool):
                solver.add_clause(c)
        # home_i >= half_low  <=>  at most (len-lower) FALSE among negative lits
        if half_low > 0:
            negs = [-v for v in lits]
            bound = len(negs) - half_low
            if bound < len(negs):
                for c in _atmost_clauses(negs, bound, pool):
                    solver.add_clause(c)


def _merge_and_dump(out_dir: str, n: int, key: str, entry: dict):
    """
    Read res/SAT/<n>.json if it exists, then add/update the <key> entry.
    If <key> is already present, create a unique key with suffix _2, _3, ...
    Write the updated JSON and return (final_key, full_data_dict).
    """
    os.makedirs(out_dir, exist_ok=True)
    path = os.path.join(out_dir, f"{n}.json")
    data = {}
    if os.path.exists(path):
        try:
            with open(path, "r") as f:
                loaded = json.load(f)
                if isinstance(loaded, dict):
                    data = loaded
        except Exception:
            data = {}

    final_key = key
    k = 2
    while final_key in data:
        final_key = f"{key}_{k}"
        k += 1

    data[final_key] = entry
    with open(path, "w") as f:
        json.dump(data, f)
    return final_key, data


def solve_optimization(n: int, solver_name: str):
    if n % 2 != 0 or n < 2:
        raise ValueError("n must be even and >= 2.")
    solver_name = normalize_solver_name(solver_name)

    base_clauses, home_vars, pool = build_base_formula(n)
    total_games = n - 1  # per team

    # solver list request?
    if solver_name in {"--list", "list", "--list-solvers"}:
        print("Available solvers:", ", ".join(get_available_solvers_list()))
        return None

    solver_kind = get_solver_kind(solver_name)
    t0 = time.time()
    best_sol = None
    best_obj = None
    solved = False
    json_solver_key = solver_name  # base key

    # starting point for d
    d_start = 0 if (total_games % 2 == 0) else 1
    d_end = total_games

    if solver_kind == "z3":
        import z3
        s = z3.Solver()
        s.set("timeout", TIME_LIMIT_SEC * 1000)
        z3_vars = _z3_add_cnf(s, base_clauses, pool)

        # incremental search on d with push/pop
        for d in range(d_start, d_end + 1):
            if time.time() - t0 >= TIME_LIMIT_SEC:
                break
            s.push()
            half_low = (total_games - d + 1) // 2
            half_high = (total_games + d) // 2
            # PB constraints for each team
            for _, lits in home_vars.items():
                if half_high < total_games:
                    s.add(z3.AtMost(*[z3_vars[v] for v in lits], half_high))
                if half_low > 0:
                    s.add(z3.AtLeast(*[z3_vars[v] for v in lits], half_low))
            res = s.check()
            if res == z3.sat:
                m = s.model()
                best_sol = build_solution_matrix_from_model_z3(m, pool, z3_vars, n)
                best_obj = d
                solved = True
                s.pop()
                break
            s.pop()

    else:
        # PySAT: rebuild a solver for each d (convenient incremental constraints)
        SolverClass = solver_kind
        for d in range(d_start, d_end + 1):
            if time.time() - t0 >= TIME_LIMIT_SEC:
                break
            solver = SolverClass(bootstrap_with=base_clauses)
            _add_fairness_constraints_pysat(solver, pool, home_vars, total_games, d)
            res = solve_pysat_with_timeout(solver, max(1, TIME_LIMIT_SEC - int(time.time() - t0)))
            if res is True:
                model = solver.get_model()
                best_sol = build_solution_matrix_from_model_pysat(model, pool, n)
                best_obj = d
                solved = True
                try:
                    solver.delete()
                except Exception:
                    pass
                break
            try:
                solver.delete()
            except Exception:
                pass

    elapsed = time.time() - t0
    runtime = int(elapsed // 1)
    if not solved and runtime < TIME_LIMIT_SEC:
        runtime = TIME_LIMIT_SEC
    if runtime > TIME_LIMIT_SEC:
        runtime = TIME_LIMIT_SEC

    entry = {
        "time": runtime,
        "optimal": bool(solved),
        "obj": int(best_obj) if best_obj is not None else None,
        "sol": best_sol
    }

    out_dir = os.path.join("res", "SAT")
    final_key, full_data = _merge_and_dump(out_dir, n, json_solver_key, entry)
    return {final_key: entry}


if __name__ == "__main__":
    if len(sys.argv) < 3:
        print("Usage: python sat_optimization.py <even_n> <solver_name>|--list")
        sys.exit(1)
    if sys.argv[2] in {"--list", "list", "--list-solvers"}:
        print("Available solvers:", ", ".join(get_available_solvers_list()))
        sys.exit(0)
    n = int(sys.argv[1])
    name = sys.argv[2]
    solve_optimization(n, name)

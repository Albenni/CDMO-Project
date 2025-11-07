# sat_optimization.py
# Optimization (fairness): minimize d = max_i |home_i - away_i|

import os
import sys
import time

from pysat.card import CardEnc, EncType

from sat_solvers import (
    get_solver_kind,
    get_available_solvers_list,
    normalize_solver_name,
    export_dimacs,
    run_dimacs_with_pysat_extra,
)
from sts_sat_model import build_base_formula
from utils import (
    merge_and_dump, 
    _max_var_from, 
    build_solution_matrix_from_model_z3,
    build_solution_matrix_from_model_pysat
)

TIME_LIMIT_SEC = 300  # 5 minutes

def _parse_sym_flag(argv):
    if len(argv) < 4:
        return True
    flag = (argv[3] or "").strip().lower()
    true_vals = {"--sym", "--with-sym", "--sym=1", "sym", "1", "true", "yes"}
    false_vals = {"--no-sym", "--sym=0", "nosym", "0", "false", "no"}
    if flag in true_vals:
        return True
    if flag in false_vals:
        return False
    return True

def _atmost_clauses(lits, bound, pool):
    """CNF clauses for AtMost: ladder when bound==1, otherwise seqcounter."""
    enc = EncType.ladder if bound == 1 else EncType.seqcounter
    return CardEnc.atmost(lits=lits, bound=bound, vpool=pool, encoding=enc).clauses

def _fairness_extra_clauses(pool, home_vars, total_games, d):
    """
    Returns CNF clauses for:
        ceil((T - d)/2) <= home_i <= floor((T + d)/2) for each team i.
    """
    cls = []
    half_low = (total_games - d + 1) // 2   # ceil((T - d)/2)
    half_high = (total_games + d) // 2      # floor((T + d)/2)

    for _, lits in home_vars.items():
        # home_i <= half_high
        if half_high < total_games:
            cls += _atmost_clauses(lits, half_high, pool)
        # home_i >= half_low  <=>  at most (len - half_low) false among the negatives
        if half_low > 0:
            negs = [-v for v in lits]
            bound = len(negs) - half_low
            if bound < len(negs):
                cls += _atmost_clauses(negs, bound, pool)
    return cls

# --- Main solver ----------------------------------------------------------------
def solve_optimization(n: int, solver_name: str, extra_symmetry: bool = True):
    if n % 2 != 0 or n < 2:
        raise ValueError("n must be even and >= 2.")
    solver_name = normalize_solver_name(solver_name)

    # -- Solver list request
    if solver_name in {"--list", "list", "--list-solvers"}:
        print("Available solvers:", ", ".join(get_available_solvers_list()))
        return None

    # Build the base CNF (decision part)
    base_clauses, home_vars, pool = build_base_formula(n, extra_symmetry=extra_symmetry)
    total_games = n - 1  # per team
    solver_kind = get_solver_kind(solver_name)

    # Incremental search over d
    d_start = 0 if (total_games % 2 == 0) else 1
    d_end = total_games

    result_sol_matrix = None
    best_obj = None
    solved = False

    suffix = "sym" if extra_symmetry else "nosym"
    json_solver_key = f"{solver_name}_{suffix}_opt"  # key distinta dal run decision
    total_start = time.time()
    gen_time = 0.0
    solve_time = 0.0

    if solver_kind == "z3":
        import z3
        s = z3.Solver()
        s.set("timeout", TIME_LIMIT_SEC * 1000)  # ms

        # Add base CNF as in sat_decision
        max_var = _max_var_from(pool, base_clauses)
        z3_vars = {i: z3.Bool(f"v{i}") for i in range(1, max_var + 1)}
        for c in base_clauses:
            s.add(z3.Or(*[(z3_vars[l] if l > 0 else z3.Not(z3_vars[-l])) for l in c]))

        # Incremental over d with push/pop
        t_s = time.time()
        for d in range(d_start, d_end + 1):
            if time.time() - total_start >= TIME_LIMIT_SEC:
                break
            s.push()
            half_low = (total_games - d + 1) // 2
            half_high = (total_games + d) // 2
            for _, lits in home_vars.items():
                if half_high < total_games:
                    s.add(z3.AtMost(*[z3_vars[v] for v in lits], half_high))
                if half_low > 0:
                    s.add(z3.AtLeast(*[z3_vars[v] for v in lits], half_low))
            res = s.check()
            if res == z3.sat:
                m = s.model()
                result_sol_matrix = build_solution_matrix_from_model_z3(m, pool, n)
                best_obj = d
                solved = True
                s.pop()
                break
            s.pop()
        solve_time = time.time() - t_s

    else:
        # === PySAT: export base DIMACS and then add fairness clauses for each d ===
        cnf_dir = os.path.join("res", "SAT", "dimacs")
        os.makedirs(cnf_dir, exist_ok=True)
        cnf_path = os.path.join(cnf_dir, f"{n}.cnf")

        t_g = time.time()
        max_var = _max_var_from(pool, base_clauses)
        export_dimacs(base_clauses, max_var, cnf_path)
        gen_time = time.time() - t_g

        t_s = time.time()
        for d in range(d_start, d_end + 1):
            # remaining time including generation
            remaining = max(1, int(TIME_LIMIT_SEC - gen_time - (time.time() - total_start)))
            if remaining <= 0:
                break
            extra = _fairness_extra_clauses(pool, home_vars, total_games, d)
            res, model = run_dimacs_with_pysat_extra(solver_name, cnf_path, extra, remaining)
            if res is True:
                result_sol_matrix = build_solution_matrix_from_model_pysat(model, pool, n)
                best_obj = d
                solved = True
                break
            elif res is False:
                # UNSAT for this d -> try d+1
                continue
            else:
                # timeout/interrupted
                break
        solve_time = time.time() - t_s

        print(f"[{solver_name}_{suffix}_opt] Generation (DIMACS): {gen_time:.2f}s, "
              f"Solving: {solve_time:.2f}s, Total: {gen_time + solve_time:.2f}s")

    # Total time and normalization as per spec
    elapsed = time.time() - total_start
    runtime = int(elapsed // 1)
    if not solved and runtime < TIME_LIMIT_SEC:
        runtime = TIME_LIMIT_SEC
    if runtime > TIME_LIMIT_SEC:
        runtime = TIME_LIMIT_SEC

    print("\tn =", n, "Solved:", solved, "Time (s):", runtime, f"(sym={extra_symmetry})")

    # JSON entry
    entry = {
        "time": runtime,
        "optimal": bool(solved),
        "obj": int(best_obj) if best_obj is not None else None,
        "sol": result_sol_matrix if solved else [],
    }

    out_dir = os.path.join("res", "SAT")
    final_key, full_data = merge_and_dump(out_dir, n, json_solver_key, entry, extra_symmetry)
    return {final_key: entry}


if __name__ == "__main__":
    if len(sys.argv) < 3:
        print("Usage: python sat_optimization.py <even_n> <solver_name>|--list [--sym|--no-sym]")
        sys.exit(1)
    if sys.argv[2] in {"--list", "list", "--list-solvers"}:
        print("Available solvers:", ", ".join(get_available_solvers_list()))
        sys.exit(0)
    n = int(sys.argv[1])
    name = sys.argv[2]
    extra_sym = _parse_sym_flag(sys.argv)
    solve_optimization(n, name, extra_symmetry=extra_sym)

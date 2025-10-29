# sat_decision.py
# STS decision solving in SAT, with DIMACS export for "standalone" solvers.
# CUMULATIVE JSON output: res/SAT/<n>.json with one entry per solver/approach.

import os
import sys
import time

from sat_solvers import (
    get_solver_kind,
    get_available_solvers_list,
    normalize_solver_name,
    export_dimacs,
    run_dimacs_with_pysat,
)
from sts_sat_model import build_base_formula
from json_output import merge_and_dump

TIME_LIMIT_SEC = 300


def _max_var_from(pool, clauses):
    """Derives the max variable index for consistency with the IDPool."""
    try:
        return pool.top
    except Exception:
        pass
    try:
        print("Using pool._next_id for max var derivation.")
        return pool._next_id - 1
    except Exception:
        pass
    mv = 0
    for c in clauses:
        for l in c:
            if abs(l) > mv:
                mv = abs(l)
    print("Max var derived manually:", mv)
    return mv


def build_solution_matrix_from_model_z3(model, pool, n):
    import z3
    # rebuild the matrix (n/2 x (n-1)) by reading the true X variables
    sol = [[None for _ in range(n - 1)] for __ in range(n // 2)]

    max_var = _max_var_from(pool, [])
    z3_vars = {i: z3.Bool(f"v{i}") for i in range(1, max_var + 1)}

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
    # model is a list of integers (positive literals = true)
    sol = [[None for _ in range(n - 1)] for __ in range(n // 2)]
    for lit in model:
        if lit > 0:
            key = pool.obj(lit)
            if not key:
                continue
            if key[0] == "X":
                _, i, j, w, p = key
                sol[p - 1][w - 1] = [i, j]
    return sol


def solve_decision(n: int, solver_name: str):
    if n % 2 != 0 or n < 2:
        raise ValueError("n must be even and >= 2.")
    solver_name = normalize_solver_name(solver_name)

    # Build base formula (pure SAT model)
    clauses, home_vars, pool = build_base_formula(n)

    # -- Solver list request
    if solver_name in {"--list", "list", "--list-solvers"}:
        avail = get_available_solvers_list()
        print("Available solvers:", ", ".join(avail))
        return None

    # Identify solver type
    solver_kind = get_solver_kind(solver_name)  # 'z3' or a PySAT class

    result_sol_matrix = None
    solved = False
    json_solver_key = solver_name  # base key in the JSON
    total_start = None
    gen_time = 0.0
    solve_time = 0.0

    if solver_kind == "z3":
        # === Z3: no file, send the propositional clauses directly ===
        import z3
        s = z3.Solver()
        s.set("timeout", TIME_LIMIT_SEC * 1000)  # in ms

        # Rebuild Z3 variables and add clauses
        max_var = _max_var_from(pool, clauses)
        z3_vars = {i: z3.Bool(f"v{i}") for i in range(1, max_var + 1)}
        for c in clauses:
            s.add(z3.Or(*[(z3_vars[l] if l > 0 else z3.Not(z3_vars[-l])) for l in c]))

        total_start = time.time()
        t_s = time.time()
        res = s.check()
        solve_time = time.time() - t_s

        if res == z3.sat:
            model = s.model()
            # print(model)
            result_sol_matrix = build_solution_matrix_from_model_z3(model, pool, n)
            solved = True
        else:
            solved = False
        # gen_time stays 0.0 (no file for Z3)
    else:
        # === PySAT: export DIMACS and then solve by reading the file ===
        cnf_dir = os.path.join("res", "SAT", "dimacs")
        os.makedirs(cnf_dir, exist_ok=True)
        cnf_path = os.path.join(cnf_dir, f"{n}.cnf")

        # print("Exporting DIMACS to", cnf_path)

        total_start = time.time()
        t_g = time.time()
        max_var = _max_var_from(pool, clauses)
        export_dimacs(clauses, max_var, cnf_path)
        gen_time = time.time() - t_g

        # remaining timeout for solving
        remaining = max(1, int(TIME_LIMIT_SEC - gen_time))
        t_s = time.time()
        res, model = run_dimacs_with_pysat(solver_name, cnf_path, remaining)
        solve_time = time.time() - t_s

        if res is True:
            result_sol_matrix = build_solution_matrix_from_model_pysat(model, pool, n)
            solved = True
        elif res is False:
            solved = False  # UNSAT
        else:
            solved = False  # timeout/interrupted
        
        print(f"[{solver_name}] Generation (DIMACS): {gen_time:.2f}s, "
          f"Solving: {solve_time:.2f}s, Total: {gen_time + solve_time:.2f}s")

    # Total time (from export DIMACS or from Z3 start)
    elapsed = time.time() - total_start
    runtime = int(elapsed // 1)
    if not solved and runtime < TIME_LIMIT_SEC:
        runtime = TIME_LIMIT_SEC
    if runtime > TIME_LIMIT_SEC:
        runtime = TIME_LIMIT_SEC
    

    # Entry for this run (decision problem: obj=None)
    entry = {
        "time": runtime,
        "optimal": bool(solved),
        "obj": None,
        "sol": result_sol_matrix
    }

    # CUMULATIVE JSON write
    out_dir = os.path.join("res", "SAT")
    final_key, full_data = merge_and_dump(out_dir, n, json_solver_key, entry)
    return {final_key: entry}


if __name__ == "__main__":
    if len(sys.argv) < 3:
        print("Usage: python sat_decision.py <even_n> <solver_name>|--list")
        sys.exit(1)
    if sys.argv[2] in {"--list", "list", "--list-solvers"}:
        print("Available solvers:", ", ".join(get_available_solvers_list()))
        sys.exit(0)
    n = int(sys.argv[1])
    name = sys.argv[2]
    solve_decision(n, name)

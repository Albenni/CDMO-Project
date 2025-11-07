# sat_decision.py

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
from utils import merge_and_dump, _max_var_from, build_solution_matrix_from_model_z3, build_solution_matrix_from_model_pysat

TIME_LIMIT_SEC = 300

def _parse_sym_flag(argv):
    """
    Restituisce (extra_symmetry: bool) in base a un eventuale terzo argomento.
    Default: True.
    """
    if len(argv) < 4:
        return True
    flag = (argv[3] or "").strip().lower()
    false_vals = {"--no-sym", "nosym"}
    if flag in false_vals:
        return False
    return True

def solve_decision(n: int, solver_name: str, extra_symmetry: bool = True):
    if n % 2 != 0 or n < 2:
        raise ValueError("n must be even and >= 2.")
    solver_name = normalize_solver_name(solver_name)

    # -- Solver list request
    if solver_name in {"--list", "list", "--list-solvers"}:
        avail = get_available_solvers_list()
        print("Available solvers:", ", ".join(avail))
        return None

    # Identify solver type
    solver_kind = get_solver_kind(solver_name)  # 'z3' or a PySAT class

    result_sol_matrix = None
    solved = False
    suffix = "sym" if extra_symmetry else "nosym"
    json_solver_key = f"{solver_name}_{suffix}"  # key nel JSON
    total_start = None
    gen_time = 0.0
    solve_time = 0.0

    if solver_kind == "z3":
        # === Z3: no file, send the propositional clauses directly ===
        import z3
        s = z3.Solver()
        s.set("timeout", TIME_LIMIT_SEC * 1000)  # in ms

        # Build SAT model
        clauses, _, pool = build_base_formula(n, extra_symmetry=extra_symmetry)

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
            result_sol_matrix = build_solution_matrix_from_model_z3(model, pool, n)
            solved = True
        else:
            solved = False
    else:
        # === PySAT: export DIMACS and then solve by reading the file ===
        cnf_dir = os.path.join("res", "SAT", "dimacs")
        os.makedirs(cnf_dir, exist_ok=True)
        cnf_path = os.path.join(cnf_dir, f"{n}.cnf")

        total_start = time.time()
        t_g = time.time()
        # Build SAT model
        clauses, _, pool = build_base_formula(n, extra_symmetry=extra_symmetry)
        max_var = _max_var_from(pool, clauses)
        export_dimacs(clauses, max_var, cnf_path)
        gen_time = time.time() - t_g

        # Remaining timeout for solving
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
    
    print("\tn =", n, "Solved:", solved, "Time (s):", runtime, f"(sym={extra_symmetry})")

    # Entry for this run (decision problem: obj=None)
    entry = {
        "time": runtime,
        "optimal": bool(solved),
        "obj": None,
        "sol": result_sol_matrix if solved else [],
    }

    # write on file and merge
    out_dir = os.path.join("res", "SAT")
    final_key, _ = merge_and_dump(out_dir, n, json_solver_key, entry, extra_symmetry)
    return {final_key: entry}


if __name__ == "__main__":
    if len(sys.argv) < 3:
        print("Usage: python sat_decision.py <even_n> <solver_name>|--list [--sym|--no-sym]")
        sys.exit(1)
    if sys.argv[2] in {"--list", "list", "--list-solvers"}:
        print("Available solvers:", ", ".join(get_available_solvers_list()))
        sys.exit(0)
    n = int(sys.argv[1])
    name = sys.argv[2]
    extra_sym = _parse_sym_flag(sys.argv)
    solve_decision(n, name, extra_symmetry=extra_sym)

# sat_decision.py
# Risoluzione decisionale del problema STS in SAT puro, con selezione solver dinamica.
# Output JSON ACCUMULATIVO: res/SAT/<n>.json con una voce per ciascun solver/approccio.

import os
import sys
import json
import time

from sat_solvers import (
    get_solver_kind,
    get_available_solvers_list,
    normalize_solver_name,
    solve_pysat_with_timeout,
)
from sts_sat_model import build_base_formula

TIME_LIMIT_SEC = 300  # 5 minuti come da specifiche progetto

def build_solution_matrix_from_model_z3(model, pool, n):
    import z3
    # ricostruiamo la matrice (n/2 x (n-1)) leggendo le X vere
    sol = [[None for _ in range(n - 1)] for __ in range(n // 2)]
    # tentiamo di capire il top id
    try:
        max_var = pool.top
    except Exception:
        try:
            max_var = pool._next_id - 1
        except Exception:
            max_var = 0
            
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
    # model è una lista di interi (literal positivi = veri)
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


def _merge_and_dump(out_dir: str, n: int, key: str, entry: dict):
    """
    Legge res/SAT/<n>.json se esiste, aggiunge/aggiorna la voce <key>.
    Se <key> è già presente, crea una chiave unica con suffisso _2, _3, ...
    Scrive il JSON aggiornato e ritorna (final_key, full_data_dict).
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
            # se non leggibile, ripartiamo da vuoto
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


def solve_decision(n: int, solver_name: str):
    if n % 2 != 0 or n < 2:
        raise ValueError("n deve essere pari e >= 2.")
    solver_name = normalize_solver_name(solver_name)

    # Costruzione formula base
    clauses, home_vars, pool = build_base_formula(n)

    # Se utente chiede elenco solver
    if solver_name in {"--list", "list", "--list-solvers"}:
        avail = get_available_solvers_list()
        print("Solver disponibili:", ", ".join(avail))
        return None

    solver_kind = get_solver_kind(solver_name)  # 'z3' oppure classe PySAT

    t0 = time.time()
    result_sol_matrix = None
    solved = False
    json_solver_key = solver_name  # chiave base per il JSON

    if solver_kind == "z3":
        import z3
        s = z3.Solver()
        s.set("timeout", TIME_LIMIT_SEC * 1000)  # ms
        # Ricostruzione variabili Z3 e aggiunta clausole
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
        res = s.check()
        if res == z3.sat:
            model = s.model()
            result_sol_matrix = build_solution_matrix_from_model_z3(model, pool, n)
            solved = True
        else:
            solved = False
    else:
        # PySAT
        SolverClass = solver_kind
        solver = SolverClass(bootstrap_with=clauses)

        # Proviamo a rispettare il TIME_LIMIT_SEC se possibile
        res = solve_pysat_with_timeout(solver, TIME_LIMIT_SEC)
        if res is True:
            model = solver.get_model()
            result_sol_matrix = build_solution_matrix_from_model_pysat(model, pool, n)
            solved = True
        elif res is False:
            solved = False  # UNSAT
        else:
            # Timeout (nessuna risposta definitiva)
            solved = False

        # Libera risorse nativamente
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

    # Entry per questo run
    entry = {
        "time": runtime,
        "optimal": bool(solved),
        "obj": None,          # nessun obiettivo nella versione decisionale
        "sol": result_sol_matrix
    }

    # Scrivi in modo ACCUMULATIVO
    out_dir = os.path.join("res", "SAT")
    final_key, full_data = _merge_and_dump(out_dir, n, json_solver_key, entry)
    return {final_key: entry}


if __name__ == "__main__":
    if len(sys.argv) < 3:
        print("Uso: python sat_decision.py <n_pari> <solver_name>|--list")
        sys.exit(1)
    if sys.argv[2] in {"--list", "list", "--list-solvers"}:
        print("Solver disponibili:", ", ".join(get_available_solvers_list()))
        sys.exit(0)
    n = int(sys.argv[1])
    name = sys.argv[2]
    solve_decision(n, name)

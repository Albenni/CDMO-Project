import os
import json

def _max_var_from(pool, clauses):
    """Derives the max variable index for consistency with the IDPool."""
    try:
        return pool.top
    except Exception:
        pass
    mv = 0
    for c in clauses:
        for l in c:
            if abs(l) > mv:
                mv = abs(l)
    return mv

def merge_and_dump(out_dir: str, n: int, key: str, entry: dict, extra_symmetry: bool = True):
    """Append in res/SAT/<n>.json an entry <key> with the result.
    If <key> already exists, generate suffixes _2, _3, ...
    Returns (final_key, full_data_dict).
    """
    os.makedirs(out_dir, exist_ok=True)
    path = os.path.join(out_dir, f"{n}.json")
    data = {}
    if os.path.exists(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                loaded = json.load(f)
                if isinstance(loaded, dict):
                    data = loaded
        except Exception:
            data = {}

    final_key = key
    k = 2
    while final_key in data:
        final_key = f"{key}_{k}_sym" if extra_symmetry else f"{key}_{k}_nosym"
        k += 1

    data[final_key] = entry
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False)
    return final_key, data

def build_solution_matrix_from_model_z3(model, pool, n):
    import z3
    # Rebuild the matrix (n/2 x (n-1)) by reading the true X variables
    sol = [[None for _ in range(n - 1)] for __ in range(n // 2)]

    max_var = _max_var_from(pool, [])
    z3_vars = {i: z3.Bool(f"v{i}") for i in range(1, max_var + 1)}

    for w in range(1, n): # weeks
        for p in range(1, n // 2 + 1): # periods
            placed = False
            for i in range(1, n + 1):
                if placed:
                    break
                for j in range(1, n + 1):
                    if i == j:
                        continue
                    vid = pool.id(("X", i, j, w, p))
                    # Find the true variable and place it in the solution
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
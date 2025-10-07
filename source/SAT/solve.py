# file: source/SAT/solve.py
from z3 import Solver, sat, unsat, unknown, set_param
import time
from encoder import make_vars, indices
from utils import model_to_matrix

def solve_instance(n, approach, timeout_s=300):
    # Configura timeout
    set_param("timeout", int(timeout_s * 1000))

    M = make_vars(n)
    s = Solver()

    try:
        constraints = approach.build_constraints(M, n)
        for c in constraints:
            s.add(c)
    except Exception as e:
        # schema ancora vuoto o incompleto
        start = time.time()
        end = start
        return "UNKNOWN", 0.0, []

    start = time.time()
    res = s.check()
    end = time.time()
    elapsed = end - start

    if res == sat:
        m = s.model()
        sol_matrix = model_to_matrix(m, M, n)
        return "SAT", elapsed, sol_matrix
    elif res == unsat:
        return "UNSAT", elapsed, []
    else:
        return "UNKNOWN", elapsed, []

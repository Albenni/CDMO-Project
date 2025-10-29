# sat_solvers.py
import os
import threading

# -----------------------------
# Model execution with different solvers; collect if available
# -----------------------------

_glucose3 = _minisat22 = None

try:
    from pysat.solvers import Glucose3 as _Glucose3
    _glucose3 = _Glucose3
except Exception:
    _glucose3 = None

try:
    from pysat.solvers import Minisat22 as _Minisat22
    _minisat22 = _Minisat22
except Exception:
    _minisat22 = None


# Working solvers
_AVAILABLE_PYSAT = {}
if _glucose3 is not None:
    _AVAILABLE_PYSAT["glucose3"] = _glucose3
if _minisat22 is not None:
    _AVAILABLE_PYSAT["minisat22"] = _minisat22


def normalize_solver_name(name: str) -> str:
    n = (name or "").strip().lower()
    if n in {"glucose", "glu"}:
        return "glucose3"
    if n in {"minisat", "mini"}:
        return "minisat22"
    return n


def get_available_solvers_list() -> list:
    """Get list of available working solver names (PySAT + z3)."""
    lst = sorted(list(_AVAILABLE_PYSAT.keys()))
    lst.append("z3")
    return lst


def get_solver_kind(name: str):
    n = normalize_solver_name(name)
    if n == "z3":
        return "z3"
    if n in _AVAILABLE_PYSAT:
        return _AVAILABLE_PYSAT[n]
    raise ValueError(
        f"Solver '{name}' not available. Available solvers: {', '.join(get_available_solvers_list())}"
    )

def solve_pysat_with_timeout(solver, timeout_sec: int):
    """
    Uses a PySAT solver to solve with a cooperative timeout.
    Return: True (SAT), False (UNSAT), None (timeout/interrupted).
    """
    # Needs a solver supporting solve_limited() and interrupt()
    if not hasattr(solver, "solve_limited"):
        print("This solver does not support solve_limited(); no cooperative timeout.")
        # Blocking fallback: either refuse or accept the risk of exceeding the limit
        return None

    if not hasattr(solver, "interrupt") or not hasattr(solver, "clear_interrupt"):
        print("This solver does not support interrupt(); no cooperative timeout.")
        return None

    stop = threading.Event()

    def killer():
        # Wait timeout_sec seconds, then interrupt solver if not stopped
        if not stop.wait(max(1, int(timeout_sec))):
            try:
                solver.interrupt()
            except Exception:
                pass

    t = threading.Thread(target=killer, daemon=True)
    t.start()

    try:
        # Interrupt stops the search after timeout_sec seconds
        res = solver.solve_limited(expect_interrupt=True)
    finally:
        # Prevent the thread from interrupting after we've finished
        stop.set()
        try:
            solver.clear_interrupt()
        except Exception:
            pass

    # res: True (SAT), False (UNSAT), None (interrupted/timeout)
    if res is None:
        return None
    return bool(res)


# -----------------------------
#  DIMACS export & run helpers
# -----------------------------
def export_dimacs(clauses, top_var: int, filepath: str) -> str:
    """
    Exports clauses to a DIMACS file at 'filepath'.
    'clauses' is a list of lists of integers.
    'top_var' is the highest variable index (or None to auto-detect).
    Returns the filepath.
    """
    from pysat.formula import CNF
    os.makedirs(os.path.dirname(filepath), exist_ok=True)
    cnf = CNF(from_clauses=clauses)
    if top_var is not None:
        cnf.nv = max(int(top_var), int(getattr(cnf, "nv", 0) or 0))

    # to_file already exports in DIMACS format
    cnf.to_file(filepath)

    return filepath


def run_dimacs_with_pysat(solver_name: str, cnf_path: str, timeout_sec: int):
    """
    Reads a DIMACS file from 'cnf_path' and solves it with the specified PySAT solver.
    'solver_name' is the name of the solver to use.
    'timeout_sec' is the timeout in seconds.
    Returns a tuple (result, model) where result is True (SAT), False (UNSAT), or None (timeout),
    and model is the satisfying assignment if result is True, otherwise None.
    """
    from pysat.formula import CNF
    SolverClass = get_solver_kind(solver_name)
    if SolverClass == "z3":
        raise ValueError("run_dimacs_with_pysat must be used only with PySAT solvers, not with z3.")
    cnf = CNF(from_file=cnf_path)
    solver = SolverClass(bootstrap_with=cnf.clauses)
    try:
        res = solve_pysat_with_timeout(solver, timeout_sec)
        model = solver.get_model() if res is True else None
        return res, model
    finally:
        try:
            solver.delete()
        except Exception:
            pass

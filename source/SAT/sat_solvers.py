# sat_solvers.py
# Utilità comuni: rilevamento solver disponibili, normalizzazione nomi, helper per PySAT e Z3.

import time, threading

# Proviamo a importare i solver PySAT uno per uno senza far fallire l'esecuzione.
_glucose3 = _minisat22 = _cadical = _lingeling = None
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

try:
    from pysat.solvers import Cadical as _Cadical
    _cadical = _Cadical
except Exception:
    _cadical = None

try:
    from pysat.solvers import Lingeling as _Lingeling
    _lingeling = _Lingeling
except Exception:
    _lingeling = None


def _z3_available():
    try:
        import z3  # noqa
        return True
    except Exception:
        return False


# Dizionario dei solver PySAT effettivamente disponibili
_AVAILABLE_PYSAT = {}
if _glucose3 is not None:
    _AVAILABLE_PYSAT["glucose3"] = _glucose3
if _minisat22 is not None:
    _AVAILABLE_PYSAT["minisat22"] = _minisat22
if _cadical is not None:
    _AVAILABLE_PYSAT["cadical"] = _cadical
if _lingeling is not None:
    _AVAILABLE_PYSAT["lingeling"] = _lingeling


def normalize_solver_name(name: str) -> str:
    """Normalizza il nome solver in minuscolo e con alias semplici."""
    n = (name or "").strip().lower()
    if n in {"glucose", "glu"}:
        return "glucose3"
    if n in {"minisat", "mini"}:
        return "minisat22"
    return n


def get_available_solvers_list() -> list:
    """Ritorna la lista dei solver disponibili (pysat + z3 se presente)."""
    lst = sorted(list(_AVAILABLE_PYSAT.keys()))
    if _z3_available():
        lst.append("z3")
    return lst


def get_solver_kind(name: str):
    """
    Ritorna:
      - stringa 'z3' se l'utente ha chiesto z3 ed è disponibile,
      - la classe PySAT del solver se disponibile,
      - altrimenti solleva ValueError con messaggio chiaro.
    """
    n = normalize_solver_name(name)
    if n == "z3":
        if _z3_available():
            return "z3"
        raise ValueError("Solver 'z3' non disponibile (modulo z3 non installato).")
    if n in _AVAILABLE_PYSAT:
        return _AVAILABLE_PYSAT[n]
    raise ValueError(
        f"Solver '{name}' non disponibile. Solver installati: {', '.join(get_available_solvers_list())}"
    )

def solve_pysat_with_timeout(solver, timeout_sec: int):
    """
    Timeout 'vero' con PySAT senza usare i budget:
    - Una solve_limited() illimitata
    - Un thread-timer che chiama solver.interrupt() allo scadere
    Ritorna: True (SAT), False (UNSAT), None (timeout).
    """
    # Serve solve_limited + interrupt + clear_interrupt
    if not hasattr(solver, "solve_limited"):
        print("Questo solver non supporta solve_limited(); niente timeout cooperativo.")
        # Fallback bloccante: decidi se rifiutare o accettare il rischio di sforare
        return bool(solver.solve())

    if not hasattr(solver, "interrupt") or not hasattr(solver, "clear_interrupt"):
        print("Questo solver non supporta interrupt(); niente timeout cooperativo.")
        return bool(solver.solve())

    stop = threading.Event()

    def killer():
        # aspetta fino a timeout_sec; se non è arrivato stop, interrompe il solver
        if not stop.wait(max(1, int(timeout_sec))):
            try:
                solver.interrupt()
            except Exception:
                pass

    t = threading.Thread(target=killer, daemon=True)
    t.start()

    try:
        # Interrupt a ferma la ricerca dopo 300 secondi
        res = solver.solve_limited(expect_interrupt=True)
    finally:
        # Evita che il thread interrompa *dopo* che abbiamo finito
        stop.set()
        try:
            solver.clear_interrupt()
        except Exception:
            pass

    # res: True (SAT), False (UNSAT), None (interrotto/timeout)
    if res is None:
        return None
    return bool(res)


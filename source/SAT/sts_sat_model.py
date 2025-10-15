# sts_sat_model.py
# Costruzione formula SAT (decisione) per STS.
# Variabili:
#   X(i,j,w,p) : True se nella settimana w, periodo p, gioca i (casa) vs j (trasferta)
#   Y(t,w,p)   : True se la squadra t gioca nella settimana w, periodo p (slot occupato da t)

from pysat.formula import IDPool
from pysat.card import CardEnc, EncType

def _atmost_clauses(lits, bound, pool):
    """
    Helper: genera clausole per vincolo 'at most bound' scegliendo un encoding appropriato.
      - bound == 1  -> EncType.ladder (lineare, compatto)
      - bound > 1   -> EncType.seqcounter (generale)
    """
    enc = EncType.ladder if bound == 1 else EncType.seqcounter
    return CardEnc.atmost(lits=lits, bound=bound, vpool=pool, encoding=enc).clauses

def build_base_formula(n: int, pool: IDPool | None = None):
    """
    Costruisce la formula base (decisionale) per STS.
    Ritorna (clauses, home_vars, pool), dove:
      - clauses: lista di clausole CNF (lista di liste di int)
      - home_vars: dict team -> lista di var-ID che significano "team gioca in casa"
      - pool: l'IDPool usato
    """
    assert n % 2 == 0 and n >= 2, "n deve essere pari e >= 2"
    if pool is None:
        pool = IDPool(start_from=1)

    clauses: list[list[int]] = []
    home_vars = {i: [] for i in range(1, n + 1)}
    slot_vars = {}   # (w,p) -> lista di X(i,j,w,p) e X(j,i,w,p)
    pair_vars = {}   # (i,j) con i<j -> lista di X(i,j,*,*) e X(j,i,*,*)

    weeks = range(1, n)                 # 1..n-1
    periods = range(1, n // 2 + 1)      # 1..n/2
    teams = range(1, n + 1)

    # Crea variabili X e raggruppamenti utili
    for i in range(1, n):
        for j in range(i + 1, n + 1):
            for w in weeks:
                for p in periods:
                    x_ij = pool.id(("X", i, j, w, p))
                    x_ji = pool.id(("X", j, i, w, p))
                    home_vars[i].append(x_ij)
                    home_vars[j].append(x_ji)
                    pair_vars.setdefault((i, j), []).extend([x_ij, x_ji])
                    slot_vars.setdefault((w, p), []).extend([x_ij, x_ji])

    # Crea variabili Y(t,w,p)
    for t in teams:
        for w in weeks:
            for p in periods:
                _ = pool.id(("Y", t, w, p))

    # (1) Ogni coppia (i,j) gioca esattamente una volta (in una sola settimana/periodo, con un solo orientamento)
    for (i, j), lits in pair_vars.items():
        if len(lits) > 1:
            clauses.extend(_atmost_clauses(lits, 1, pool))   # at most 1
        # almeno una partita fra i e j
        clauses.append(lits[:])

    # (2) Ogni slot (w,p) contiene al più una partita
    for (w, p), lits in slot_vars.items():
        if len(lits) > 1:
            clauses.extend(_atmost_clauses(lits, 1, pool))   # at most 1

    # (3) Ogni squadra gioca esattamente una volta a settimana (esattamente un periodo per w)
    for t in teams:
        for w in weeks:
            y_list = [pool.id(("Y", t, w, p)) for p in periods]
            if len(y_list) > 1:
                clauses.extend(_atmost_clauses(y_list, 1, pool))  # at most 1
            clauses.append(y_list[:])  # almeno uno

    # (4) Collegamenti X↔Y su ciascuno slot
    for t in teams:
        for w in weeks:
            for p in periods:
                y_id = pool.id(("Y", t, w, p))
                x_slot_t = []
                for j in teams:
                    if j == t:
                        continue
                    x_tj = pool.id(("X", t, j, w, p))
                    x_jt = pool.id(("X", j, t, w, p))
                    # X ⇒ Y
                    clauses.append([-x_tj, y_id])
                    clauses.append([-x_jt, y_id])
                    x_slot_t.extend([x_tj, x_jt])
                # Y ⇒ OR(X)
                clauses.append([-y_id] + x_slot_t)

    # (5) Ogni squadra gioca al massimo 2 volte nello stesso periodo lungo tutto il torneo
    for t in teams:
        for p in periods:
            y_tp = [pool.id(("Y", t, w, p)) for w in weeks]
            if len(y_tp) > 2:
                clauses.extend(_atmost_clauses(y_tp, 2, pool))  # at most 2 (usa seqcounter)

    return clauses, home_vars, pool

# sts_sat_model.py — modello SAT "puro" compatibile col decoder (nessuna modifica al resto)
# API invariata: build_base_formula(n) -> (clauses, home_vars, pool)

from typing import Dict, List, Tuple
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType

# -----------------------------
#  Encodings di cardinalità
# -----------------------------
def _has_enc(name: str) -> bool:
    try:
        getattr(EncType, name)
        return True
    except Exception:
        return False

def _enc_for_atmost(m: int, k: int) -> 'EncType':
    if k == 1:
        if m <= 8:
            return EncType.pairwise
        return EncType.heule if _has_enc('heule') else EncType.ladder
    if _has_enc('cardnetwrk') and m >= 24:
        return EncType.cardnetwrk
    return EncType.seqcounter

def _atmost(lits: List[int], k: int, pool: IDPool) -> List[List[int]]:
    if len(lits) <= k:
        return []
    return CardEnc.atmost(lits=lits, bound=k, vpool=pool, encoding=_enc_for_atmost(len(lits), k)).clauses

def _exactly_one(lits: List[int], pool: IDPool) -> List[List[int]]:
    if not lits:
        return []
    cls = [list(lits)]  # AtLeast1
    cls += _atmost(lits, 1, pool)  # AtMost1
    return cls

# -----------------------------
#  Symmetry: round-robin "circle"
# -----------------------------
def _circle_pairs_by_week(n: int) -> List[List[Tuple[int, int]]]:
    """Restituisce per ogni settimana (1..n-1) la lista di n/2 coppie (u<v)."""
    arr = list(range(1, n + 1))
    weeks_pairs: List[List[Tuple[int, int]]] = []
    for _ in range(n - 1):
        pairs = []
        for i in range(n // 2):
            u, v = arr[i], arr[-(i + 1)]
            if u > v:
                u, v = v, u
            pairs.append((u, v))
        weeks_pairs.append(pairs)
        # rotazione: fissa arr[0], ruota gli altri a destra
        arr = [arr[0]] + [arr[-1]] + arr[1:-1]
    return weeks_pairs

def _fix_week1_periods(n: int, pool: IDPool, clauses: List[List[int]]):
    """Week 1: (i, n+1-i) gioca nel periodo i (orientamento libero) + fissa (1,n) in casa in p=1."""
    w = 1
    for i in range(1, n // 2 + 1):
        j, p = n + 1 - i, i
        x_ij = pool.id(("X", i, j, w, p))
        x_ji = pool.id(("X", j, i, w, p))
        # deve accadere nel periodo i
        clauses.append([x_ij, x_ji])
        # vieta altri periodi della week 1 per quella coppia
        for pp in range(1, n // 2 + 1):
            if pp != p:
                clauses.append([-pool.id(("X", i, j, w, pp))])
                clauses.append([-pool.id(("X", j, i, w, pp))])
    if n >= 2:
        clauses.append([pool.id(("X", 1, n, 1, 1))])  # orientamento (1,n) in p=1

# -----------------------------
#  Modello principale
# -----------------------------
def build_base_formula(n: int):
    assert n % 2 == 0 and n >= 2, "n deve essere pari e ≥ 2"

    pool = IDPool()
    clauses: List[List[int]] = []

    weeks = list(range(1, n))                 # 1..n-1
    periods = list(range(1, n // 2 + 1))      # 1..n/2
    teams = list(range(1, n + 1))             # 1..n

    # Per compatibilità con il resto: X dove la squadra è "in casa"
    home_vars: Dict[int, List[int]] = {t: [] for t in teams}

    # ---- Symmetry forte: settimana assegnata per ciascuna coppia (circle) ----
    weeks_pairs = _circle_pairs_by_week(n)  # idx 0 -> week 1
    week_of_pair: Dict[Tuple[int, int], int] = {}
    opp_of_team_week: Dict[Tuple[int, int], int] = {}  # (t,w) -> opp

    for w_idx, w in enumerate(weeks):
        for (u, v) in weeks_pairs[w_idx]:
            week_of_pair[(u, v)] = w
            opp_of_team_week[(u, w)] = v
            opp_of_team_week[(v, w)] = u

    # -----------------------------
    #  PRE-REGISTRAZIONE di TUTTE le X e Y (per evitare nuovi ID nel decoder)
    # -----------------------------
    for w in weeks:
        for p in periods:
            for i in teams:
                for j in teams:
                    if i == j:
                        continue
                    pool.id(("X", i, j, w, p))
            for t in teams:
                pool.id(("Y", t, w, p))

    # -----------------------------
    #  (1) Forbici: per ogni coppia (u,v) vieta TUTTE le settimane ≠ w*
    #      (unit negative) e crea ExactlyOne solo sulla settimana w* (periodi + orientamenti)
    # -----------------------------
    for u in teams:
        for v in teams:
            if u >= v:
                continue
            w_star = week_of_pair[(u, v)]
            # vieta tutte le altre settimane (unit)
            for w in weeks:
                if w == w_star:
                    continue
                for p in periods:
                    clauses.append([-pool.id(("X", u, v, w, p))])
                    clauses.append([-pool.id(("X", v, u, w, p))])
            # ExactlyOne nella settimana assegnata, sui 2*|periods| letterali
            lits = []
            for p in periods:
                x_uv = pool.id(("X", u, v, w_star, p))
                x_vu = pool.id(("X", v, u, w_star, p))
                lits.extend([x_uv, x_vu])
                # traccia home
                home_vars[u].append(x_uv)
                home_vars[v].append(x_vu)
            clauses += _exactly_one(lits, pool)

    # -----------------------------
    #  (2) Canalizzazione locale e Y⇒OR(X) corto (2 letterali)
    # -----------------------------
    for w in weeks:
        for p in periods:
            for t in teams:
                y = pool.id(("Y", t, w, p))
                opp = opp_of_team_week[(t, w)]  # unico avversario in settimana w
                x_home = pool.id(("X", t, opp, w, p))
                x_away = pool.id(("X", opp, t, w, p))
                # X ⇒ Y (solo per la coppia della settimana; le altre X sono già false)
                clauses.append([-x_home, y])
                clauses.append([-x_away, y])
                # Y ⇒ (X_home ∨ X_away)
                clauses.append([-y, x_home, x_away])

    # -----------------------------
    #  (3) Ogni squadra sceglie esattamente un periodo per settimana
    # -----------------------------
    for t in teams:
        for w in weeks:
            y_tw = [pool.id(("Y", t, w, p)) for p in periods]
            clauses += _exactly_one(y_tw, pool)

    # -----------------------------
    #  (4) Ogni slot (w,p) ha ESATTAMENTE due squadre presenti (AtMost2 + AtLeast2)
    # -----------------------------
    for w in weeks:
        for p in periods:
            y_wpl = [pool.id(("Y", t, w, p)) for t in teams]
            clauses += _atmost(y_wpl, 2, pool)                    # ≤2
            clauses += _atmost([-y for y in y_wpl], len(y_wpl)-2, pool)  # ≥2

    # -----------------------------
    #  (5) Stesso periodo, al massimo 2 volte per squadra sull’intero torneo
    # -----------------------------
    for t in teams:
        for p in periods:
            y_tp = [pool.id(("Y", t, w, p)) for w in weeks]
            clauses += _atmost(y_tp, 2, pool)

    # -----------------------------
    #  (6) Symmetry extra: fissa i periodi della week 1
    # -----------------------------
    _fix_week1_periods(n, pool, clauses)

    return clauses, home_vars, pool

# sts_sat_model.py — pure SAT model

from typing import Dict, List, Tuple
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType

# -----------------------------
#  Cardinality encodings
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
    """Returns for each week (1..n-1) the list of n/2 pairs (u<v)."""
    arr = list(range(1, n + 1))
    weeks_pairs: List[List[Tuple[int, int]]] = []
    for _ in range(n - 1):
        pairs = []
        for i in range(n // 2):
            u, v = arr[i], arr[-(i + 1)]  # First and last elements towards center
            if u > v:  # Ensure canonical order e.g. (1,2) not (2,1)
                u, v = v, u
            pairs.append((u, v))
        weeks_pairs.append(pairs)
        # rotate array for next week: arr[0] stays, others rotate right
        arr = [arr[0]] + [arr[-1]] + arr[1:-1]  # Rotate right except first element
    return weeks_pairs

def _fix_week1_periods(n: int, pool: IDPool, clauses: List[List[int]]):
    """Week 1: (i, n+1-i) plays in period i (free orientation) + fix (1,n) at home in p=1."""
    w = 1
    for i in range(1, n // 2 + 1):
        j, p = n + 1 - i, i
        x_ij = pool.id(("X", i, j, w, p))
        x_ji = pool.id(("X", j, i, w, p))
        # needs to play in that period (one of the two orientations)
        clauses.append([x_ij, x_ji])
        # forbids playing in that period in the other orientation
        for pp in range(1, n // 2 + 1):
            if pp != p:
                clauses.append([-pool.id(("X", i, j, w, pp))])
                clauses.append([-pool.id(("X", j, i, w, pp))])
    if n >= 2:
        clauses.append([pool.id(("X", 1, n, 1, 1))])  # orientation (1,n) at home in p=1

# -----------------------------
#  Main model builder
# -----------------------------
def build_base_formula(n: int):
    assert n % 2 == 0 and n >= 2, "n needs to be even and ≥ 2"

    pool = IDPool()
    clauses: List[List[int]] = []

    weeks = list(range(1, n))                 # 1..n-1
    periods = list(range(1, n // 2 + 1))      # 1..n/2
    teams = list(range(1, n + 1))             # 1..n

    # For compatibility with the rest: X where the team is "home"
    home_vars: Dict[int, List[int]] = {t: [] for t in teams}

    # ---- Symmetry breaking: assign a week to each pair with the circle method ----
    weeks_pairs = _circle_pairs_by_week(n)  # idx 0 -> week 1
    week_of_pair: Dict[Tuple[int, int], int] = {}
    opp_of_team_week: Dict[Tuple[int, int], int] = {}  # (t,w) -> opponent

    for w_idx, w in enumerate(weeks):
        for (u, v) in weeks_pairs[w_idx]:
            week_of_pair[(u, v)] = w
            opp_of_team_week[(u, w)] = v
            opp_of_team_week[(v, w)] = u

    # -----------------------------
    #  PRE-REGISTRATION of ALL X and Y (to avoid new IDs in the decoder)
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
    #  (1) Pruning: for each pair (u,v) forbid ALL weeks ≠ w* 
    #      (unit negatives) and create ExactlyOne only in week w* (periods + orientations)
    # -----------------------------
    for u in teams:
        for v in teams:
            if u >= v:
                continue
            w_star = week_of_pair[(u, v)]
            # forbid all other weeks (unit)
            for w in weeks:
                if w == w_star:
                    continue
                for p in periods:
                    clauses.append([-pool.id(("X", u, v, w, p))])
                    clauses.append([-pool.id(("X", v, u, w, p))])
            # ExactlyOne in the assigned week, over the 2*|periods| literals
            lits = []
            for p in periods:
                x_uv = pool.id(("X", u, v, w_star, p))
                x_vu = pool.id(("X", v, u, w_star, p))
                lits.extend([x_uv, x_vu])
                # track home
                home_vars[u].append(x_uv)
                home_vars[v].append(x_vu)
            clauses += _exactly_one(lits, pool)

    # -----------------------------
    #  (2) Local channeling and short Y⇒OR(X) (2 literals)
    # -----------------------------
    for w in weeks:
        for p in periods:
            for t in teams:
                y = pool.id(("Y", t, w, p))
                opp = opp_of_team_week[(t, w)]  # unique opponent in week w
                x_home = pool.id(("X", t, opp, w, p))
                x_away = pool.id(("X", opp, t, w, p))
                # X ⇒ Y (only for that week's pair; the other X are already false)
                clauses.append([-x_home, y])
                clauses.append([-x_away, y])
                # Y ⇒ (X_home ∨ X_away)
                clauses.append([-y, x_home, x_away])

    # -----------------------------
    #  (3) Each team chooses exactly one period per week
    # -----------------------------
    for t in teams:
        for w in weeks:
            y_tw = [pool.id(("Y", t, w, p)) for p in periods]
            clauses += _exactly_one(y_tw, pool)

    # -----------------------------
    #  (4) Each slot (w,p) has EXACTLY two teams present (AtMost2 + AtLeast2)
    # -----------------------------
    for w in weeks:
        for p in periods:
            y_wpl = [pool.id(("Y", t, w, p)) for t in teams]
            clauses += _atmost(y_wpl, 2, pool)                    # ≤2
            clauses += _atmost([-y for y in y_wpl], len(y_wpl)-2, pool)  # ≥2

    # -----------------------------
    #  (5) Same period, at most 2 times per team over the whole tournament
    # -----------------------------
    for t in teams:
        for p in periods:
            y_tp = [pool.id(("Y", t, w, p)) for w in weeks]
            clauses += _atmost(y_tp, 2, pool)

    # -----------------------------
    #  (6) Extra symmetry: fix the periods of week 1
    # -----------------------------
    _fix_week1_periods(n, pool, clauses)

    return clauses, home_vars, pool

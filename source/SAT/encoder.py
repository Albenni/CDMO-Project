# file: source/SAT/encoder.py
from z3 import Bool, If, Sum, PbEq, PbLe, PbGe

def indices(n):
    assert n % 2 == 0 and n >= 2
    weeks = n - 1
    periods = n // 2
    teams = list(range(1, n+1))
    return periods, weeks, teams

def make_vars(n, z3ctx=None):
    """Crea variabili booleane M[p][w][i][j] (i != j):
        M[p,w,i,j] = True  <=> in periodo p, settimana w gioca (i in casa) vs (j in trasferta)
    Restituisce: dict chiave (p,w,i,j) -> BoolVar
    """
    periods, weeks, teams = indices(n)
    M = {}
    for p in range(periods):
        for w in range(weeks):
            for i in teams:
                for j in teams:
                    if i == j:
                        continue
                    name = f"M_p{p}_w{w}_{i}v{j}"
                    M[(p,w,i,j)] = Bool(name) if z3ctx is None else Bool(name, z3ctx)
    return M

# def exactly_one(bools):
#     # Somma booleana == 1
#     return Sum([If(b,1,0) for b in bools]) == 1

# def at_most_k(bools, k):
#     return Sum([If(b,1,0) for b in bools]) <= k

def exactly_one(bools):
    # Σ b == 1
    return PbEq([(b, 1) for b in bools], 1)

def at_most_k(bools, k):
    # Σ b ≤ k
    return PbLe([(b, 1) for b in bools], k)

def at_least_k(bools, k):
    return PbGe([(b, 1) for b in bools], k)

def occurs_team_in_week(M, n, i, w):
    periods, weeks, teams = indices(n)
    lits = []
    for p in range(periods):
        for j in teams:
            if i == j:
                continue
            lits.append(M[(p,w,i,j)])   # i in casa
            lits.append(M[(p,w,j,i)])   # i in trasferta
    return lits

def occurs_pair_anywhere(M, n, i, j):
    periods, weeks, teams = indices(n)
    lits = []
    for p in range(periods):
        for w in range(weeks):
            lits.append(M[(p,w,i,j)])
            lits.append(M[(p,w,j,i)])
    return lits

def plays_in_period(M, n, i, p):
    periods, weeks, teams = indices(n)
    lits = []
    for w in range(weeks):
        for j in teams:
            if i == j:
                continue
            lits.append(M[(p,w,i,j)])   # i in casa
            lits.append(M[(p,w,j,i)])   # i in trasferta
    return lits

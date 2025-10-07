# file: source/SAT/approaches/basic.py
# Encoding di base per STS (decision)
# TODO: completare i vincoli secondo specifica del progetto
from encoder import indices, exactly_one, occurs_team_in_week, occurs_pair_anywhere, plays_in_period
from z3 import Sum, If, Or

def build_constraints(M, n):
    periods, weeks, teams = indices(n)
    C = []

    # 1) In ogni (p,w) esattamente una partita (i vs j, con i != j)
    for p in range(periods):
        for w in range(weeks):
            lits = []
            for i in teams:
                for j in teams:
                    if i == j:
                        continue
                    lits.append(M[(p,w,i,j)])
            C.append(exactly_one(lits))

    # 2) Ogni team gioca esattamente una volta a settimana
    for w in range(weeks):
        for i in teams:
            C.append(exactly_one(occurs_team_in_week(M, n, i, w)))

    # 3) Ogni coppia {i,j} gioca esattamente una volta nell'intero torneo
    for idx_i, i in enumerate(teams):
        for j in teams[idx_i+1:]:
            C.append(exactly_one(occurs_pair_anywhere(M, n, i, j)))

    # 4) Ogni team gioca al più due volte nello stesso periodo (su tutte le settimane)
    from encoder import at_most_k
    for p in range(periods):
        for i in teams:
            C.append(at_most_k(plays_in_period(M, n, i, p), 2))

    # 5) Con i tuoi vincoli, ogni squadra gioca n−1 volte e per periodo può comparire ≤2. Ne segue che deve comparire ≥1 in ogni periodo.
    for p in range(periods):
        for i in teams:
            C.append(Or(*plays_in_period(M, n, i, p)))

    return C

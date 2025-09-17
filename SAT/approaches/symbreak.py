# file: source/SAT/approaches/symbreak.py
# Varianti di symmetry breaking
# TODO: aggiungere ulteriori vincoli di simmetria (es: fissare schema della prima settimana)
from z3 import Or
from encoder import indices, exactly_one
from approaches.basic import build_constraints as basic_constraints

def rotation_pairs(n):
    teams = list(range(1, n+1))
    weeks = n - 1
    sched = []
    for _ in range(weeks):
        pairs = [(teams[i], teams[-1-i]) for i in range(n//2)]
        sched.append(pairs)
        teams = [teams[0]] + [teams[-1]] + teams[1:-1]  # rotate except first
    return sched

def week_of_pair(sched, i, j):
    target = {i, j}
    for w, pairs in enumerate(sched):
        for a, b in pairs:
            if {a, b} == target:
                return w
    raise RuntimeError("Pair not found in rotation schedule")

def build_constraints(M, n):
    C = basic_constraints(M, n)
    periods, weeks, teams = indices(n)

    # (a) fissiamo le coppie di ogni settimana (rotation)
    sched = rotation_pairs(n)
    for w, pairs in enumerate(sched):
        for (i, j) in pairs:
            # la coppia {i,j} deve comparire in quella settimana, in un solo periodo
            C.append(exactly_one([Or(M[(p,w,i,j)], M[(p,w,j,i)]) for p in range(periods)]))

    # (b) orienta (1,2) nella SUA settimana w12 (periodo libero)
    w12 = week_of_pair(sched, 1, 2)
    C.append(Or(*[M[(p, w12, 1, 2)] for p in range(periods)]))

    # (c) opzionale: rompi la simmetria dei periodi nella settimana 0
    # assegna a ogni periodo una coppia fissa (senza orientamento)
    for p, (i, j) in enumerate(sched[0]):
        C.append(Or(M[(p,0,i,j)], M[(p,0,j,i)]))

    return C

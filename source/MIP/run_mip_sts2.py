#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import argparse
import json
import math
import os
import sys
import time as _time

from pyomo.environ import (
    ConcreteModel, Set, Var, Binary, NonNegativeReals, RangeSet, Constraint,
    Objective, minimize, value, Param, SolverFactory, Suffix
)
from pyomo.opt import TerminationCondition


# ==============================
# Round-robin (1-factorization)
# ==============================

def round_robin_pairs(n):
    assert n % 2 == 0 and n >= 2
    arr = list(range(1, n + 1))
    weeks = []
    for _ in range(n - 1):
        pairs = []
        for k in range(n // 2):
            a = arr[k]
            b = arr[-(k + 1)]
            i, j = (a, b) if a < b else (b, a)
            pairs.append((i, j))
        weeks.append(pairs)
        # rotate keeping arr[0] fixed: [a0,a1,...,a_{n-2},a_{n-1}] -> [a0,a_{n-1},a1,...,a_{n-2}]
        arr = [arr[0]] + [arr[-1]] + arr[1:-1]
    # normalize
    norm_weeks = []
    for w in weeks:
        seen, out = set(), []
        for (i, j) in w:
            key = (min(i, j), max(i, j))
            if key not in seen:
                seen.add(key)
                out.append(key)
        norm_weeks.append(out)
    return norm_weeks  # list length n-1, each list length n/2

# =========================================
# Hungarian algorithm (square assignment)
# =========================================

def hungarian(cost):
    """
    Classic Hungarian algorithm for square matrix assignment (min cost).
    Input: cost is a list of lists, size P x P.
    Returns: assignment list 'assign' of length P where assign[row] = col.
    """
    P = len(cost)
    u = [0]*(P+1)
    v = [0]*(P+1)
    p = [0]*(P+1)
    way = [0]*(P+1)
    for i in range(1, P+1):
        p[0] = i
        j0 = 0
        minv = [float('inf')]*(P+1)
        used = [False]*(P+1)
        while True:
            used[j0] = True
            i0 = p[j0]
            delta = float('inf')
            j1 = 0
            for j in range(1, P+1):
                if not used[j]:
                    cur = cost[i0-1][j-1] - u[i0] - v[j]
                    if cur < minv[j]:
                        minv[j] = cur
                        way[j] = j0
                    if minv[j] < delta:
                        delta = minv[j]
                        j1 = j
            for j in range(0, P+1):
                if used[j]:
                    u[p[j]] += delta
                    v[j] -= delta
                else:
                    minv[j] -= delta
            j0 = j1
            if p[j0] == 0:
                break
        while True:
            j1 = way[j0]
            p[j0] = p[j1]
            j0 = j1
            if j0 == 0:
                break
    assign = [0]*P
    for j in range(1, P+1):
        assign[p[j]-1] = j-1
    return assign

# =========================================
# Warm-start via Hungarian (per settimana)
# =========================================

def warmstart_hungarian(weeks_pairs, n):
    """
    Costruisce un warm-start x0 COMPLETO usando Hungarian per ogni settimana.
    Penalizza i periodi prossimi al cap (<=2 per team/period) con costi alti.
    Ritorna: dict chiavi ((i,j), w, p) -> 0/1
    """
    W = len(weeks_pairs)     # n-1
    P = n // 2
    CAP = 2
    BIG = 10**6

    # counts[(team, p)] = quanto ha giocato la squadra 'team' nel periodo 'p' finora
    counts = {(i, p): 0 for i in range(1, n + 1) for p in range(1, P + 1)}
    x0 = {}

    for w_idx, pairs in enumerate(weeks_pairs, start=1):
        # cost matrix P x P: righe = partite della settimana (nell'ordine 'pairs'), col = periodi 1..P
        cost = [[0 for _ in range(P)] for _ in range(P)]
        for r, (i, j) in enumerate(pairs):
            for p in range(1, P + 1):
                # Se mettere (i,j) nel periodo p sforza il cap per uno dei due → grande penalità
                if counts[(i, p)] >= CAP or counts[(j, p)] >= CAP:
                    c = BIG
                else:
                    # preferisci periodi "scarichi" per entrambi
                    c = counts[(i, p)] + counts[(j, p)]
                cost[r][p-1] = c

        assign = hungarian(cost)  # col per ciascuna riga r
        # applichiamo l'assegnamento
        used_p = set()
        for r, (i, j) in enumerate(pairs):
            p = assign[r] + 1
            # se Hungarian ha scelto una colonna con BIG (impossibile pratica),
            # proviamo a deviare al primo periodo libero non cap-violating
            if cost[r][p-1] >= BIG or p in used_p:
                placed = False
                for alt in range(1, P + 1):
                    if alt in used_p:
                        continue
                    if counts[(i, alt)] >= CAP or counts[(j, alt)] >= CAP:
                        continue
                    p = alt
                    placed = True
                    break
                if not placed:
                    # ultima spiaggia: prendi un periodo libero anche se a costo alto,
                    # il solver sistemerà (rarissimo)
                    for alt in range(1, P + 1):
                        if alt not in used_p:
                            p = alt
                            break
            used_p.add(p)
            x0[((i, j), w_idx, p)] = 1
            counts[(i, p)] += 1
            counts[(j, p)] += 1

    return x0

# ==========================
# Stage A: Feasible (x only)
# ==========================

def build_stageA_model(n, weeks_pairs, use_symmetry_breaking=True, set_priorities=True):
    m = ConcreteModel(name=f"STS_MIP_StageA_n{n}")

    m.N = Param(initialize=n)
    m.Wn = Param(initialize=n - 1)
    m.Pn = Param(initialize=n // 2)

    m.W = RangeSet(1, n - 1)
    m.P = RangeSet(1, n // 2)
    m.T = RangeSet(1, n)

    # (i,j,w) SOLO per le coppie della settimana w (i<j)
    E_weeks = []
    for w_idx, pairs in enumerate(weeks_pairs, start=1):
        for (i, j) in pairs:
            E_weeks.append((i, j, w_idx))
    m.EW = Set(dimen=3, initialize=E_weeks, ordered=True)

    # x[(i,j,w), p] binarie
    m.x = Var(m.EW, m.P, within=Binary)

    # 1) ogni match (i,j) in week w va in esattamente un periodo
    def one_period_per_match(m, i, j, w):
        return sum(m.x[(i, j, w), p] for p in m.P) == 1
    m.OnePeriodPerMatch = Constraint(m.EW, rule=one_period_per_match)

    # 2) uno e un solo match per (w,p)
    def one_match_per_slot(m, w, p):
        return sum(m.x[(i, j, ww), p] for (i, j, ww) in m.EW if ww == w) == 1
    m.OneMatchPerSlot = Constraint(m.W, m.P, rule=one_match_per_slot)

    # 3) cap periodo: ogni team in ciascun periodo ≤ 2 volte nell'intero torneo
    def period_cap(m, i, p):
        return sum(m.x[(a, b, w), p] for (a, b, w) in m.EW if (a == i or b == i)) <= 2
    m.PeriodCap = Constraint(m.T, m.P, rule=period_cap)

    # 4) team-week = 1 (implicito, ma irrigidisce l'LP)
    def team_week_exactly_one(m, i, w):
        return sum(m.x[(a, b, ww), p]
                   for (a, b, ww) in m.EW if ww == w and (a == i or b == i)
                   for p in m.P) == 1
    m.TeamWeek = Constraint(m.T, m.W, rule=team_week_exactly_one)

    # Symmetry breaking: fissa week-1 come generata (match k -> period k)
    if use_symmetry_breaking:
        week1_pairs = weeks_pairs[0]
        for idx, (i, j) in enumerate(week1_pairs, start=1):
            m.add_component(f"SB_w1_p{idx}",
                            Constraint(expr=m.x[(i, j, 1), idx] == 1))


    # Branching priority (solo se solver le supporta: Gurobi/CPLEX)
    if set_priorities:
        m.priority = Suffix(direction=Suffix.EXPORT, datatype=Suffix.INT)
        for (i, j, w) in m.EW:
            for p in m.P:
                # priorità decrescente con la settimana (prima settimane piccole)
                pr = 1000 - w
                m.priority[m.x[(i, j, w), p]] = pr

    return m

# ===============================================
# Stage B: Orientation (s) + balancing deviations
# ===============================================

def build_stageB_model(n, weeks_pairs, use_symmetry_breaking=True):
    m = ConcreteModel(name=f"STS_MIP_StageB_n{n}")

    m.N = Param(initialize=n)
    m.Wn = Param(initialize=n - 1)
    m.Pn = Param(initialize=n // 2)

    m.W = RangeSet(1, n - 1)
    m.T = RangeSet(1, n)

    E_weeks = []
    for w_idx, pairs in enumerate(weeks_pairs, start=1):
        for (i, j) in pairs:
            E_weeks.append((i, j, w_idx))
    m.EW = Set(dimen=3, initialize=E_weeks, ordered=True)

    # s[(i,j,w)] binaria: s=1 => i (min) è in casa contro j in w
    m.s = Var(m.EW, within=Binary)

    # dev[i] ≥ |H_i - target|
    m.dev = Var(m.T, within=NonNegativeReals)
    target = (n - 1) / 2.0
    m.target = Param(initialize=target)

    def dev_lower(m, i):
        home_i = 0
        for (a, b, w) in m.EW:
            if a == i:
                home_i += m.s[(a, b, w)]
            elif b == i:
                home_i += (1 - m.s[(a, b, w)])
        return home_i - m.target <= m.dev[i]

    def dev_upper(m, i):
        home_i = 0
        for (a, b, w) in m.EW:
            if a == i:
                home_i += m.s[(a, b, w)]
            elif b == i:
                home_i += (1 - m.s[(a, b, w)])
        return m.target - home_i <= m.dev[i]

    m.DevLower = Constraint(m.T, rule=dev_lower)
    m.DevUpper = Constraint(m.T, rule=dev_upper)
    m.Obj = Objective(expr=sum(m.dev[i] for i in m.T), sense=minimize)

    # SB: orientamento fissato per la prima coppia della week-1
    if use_symmetry_breaking and weeks_pairs[0]:
        e0 = weeks_pairs[0][0]
        m.SB_orient = Constraint(expr=m.s[(e0[0], e0[1], 1)] == 1)

    return m

# =================
# Solver helpers
# =================

def apply_timelimit(solver, solver_name, seconds, mip_gap=None):
    lname = solver_name.lower()
    if lname in ("cbc", "coin-or", "coin", "coin-or-cbc"):
        solver.options["seconds"] = int(seconds)
    elif lname in ("gurobi", "gurobi_persistent"):
        solver.options["TimeLimit"] = float(seconds)
        if mip_gap is not None:
            solver.options["MIPGap"] = float(mip_gap)
    elif lname in ("cplex", "cplex_persistent"):
        solver.options["timelimit"] = float(seconds)
        if mip_gap is not None:
            solver.options["mipgap"] = float(mip_gap)
    elif lname in ("highs", "highs_persistent"):
        solver.options["time_limit"] = float(seconds)
        if mip_gap is not None:
            solver.options["mip_rel_gap"] = float(mip_gap)

def term_flags(results):
    tc = results.solver.termination_condition
    optimal = (tc == TerminationCondition.optimal)
    feasible = tc in (
        TerminationCondition.optimal,
        TerminationCondition.feasible,
        TerminationCondition.locallyOptimal,
        TerminationCondition.maxTimeLimit
    )
    return feasible, optimal, tc

# =================
# Extractors
# =================

def extract_x_solution(model, n, weeks_pairs):
    P = n // 2
    xsol = {}
    def sval(v):
        try:
            return value(v)
        except:
            return None
    for w_idx, pairs in enumerate(weeks_pairs, start=1):
        for (i, j) in pairs:
            for p in range(1, P + 1):
                v = sval(model.x[(i, j, w_idx), p])
                xsol[((i, j), w_idx, p)] = 1 if (v is not None and v >= 0.5) else 0
    return xsol

def extract_solution_matrix(n, weeks_pairs, xsol, ssol):
    """
    Ritorna matrice (n/2) x (n-1) con [home, away].
    xsol: ((i,j),w,p)->0/1 , ssol: (i,j,w)->0/1 (1= i in casa).
    """
    W = n - 1
    P = n // 2
    mat = [[None for _ in range(W)] for _ in range(P)]

    s_map = {(i, j, w): v for (i, j, w), v in ssol.items()}

    for w in range(1, W + 1):
        for (i, j) in weeks_pairs[w - 1]:
            # period chosen
            p_chosen = None
            for p in range(1, P + 1):
                if xsol.get(((i, j), w, p), 0) == 1:
                    p_chosen = p
                    break
            if p_chosen is None:
                continue
            s = s_map.get((i, j, w), 1)
            home, away = (i, j) if s >= 0.5 else (j, i)
            mat[p_chosen - 1][w - 1] = [home, away]

    for p in range(P):
        for w in range(W):
            if mat[p][w] is None:
                mat[p][w] = [None, None]
    return mat

# =================
# Main run
# =================

def run(n: int,
        solver_name: str = "highs",
        total_timelimit: int = 300,
        split_A: float = 0.85,
        use_symmetry_breaking: bool = True,
        use_priorities: bool = True,
        no_objective: bool = False):

    if n % 2 != 0 or n < 2:
        raise ValueError("n must be an even integer >= 2.")
    opt = SolverFactory(solver_name)
    if opt is None or not opt.available():
        raise RuntimeError(f"Solver '{solver_name}' non disponibile o non installato.")

    weeks_pairs = round_robin_pairs(n)

    # Budget di tempo
    budget_A = max(1, int(total_timelimit * split_A))
    budget_B = max(1, int(total_timelimit - budget_A))

    # ----- Stage A -----
    mA = build_stageA_model(
        n, weeks_pairs,
        use_symmetry_breaking=use_symmetry_breaking,
        set_priorities=use_priorities and (solver_name.lower() in ("gurobi", "cplex", "cplex_persistent", "gurobi_persistent"))
    )

    # Warm-start: Hungarian per ogni settimana
    x0 = warmstart_hungarian(weeks_pairs, n)
    for ((i, j), w, p), val in x0.items():
        key = ((i, j, w), p)
        if key in mA.x:
            mA.x[key].value = int(val)

    apply_timelimit(opt, solver_name, budget_A, mip_gap=0.0)

    t0 = _time.time()
    resA = opt.solve(mA, tee=False)
    tA = _time.time() - t0
    feasA, optA, _ = term_flags(resA)
    reported_time_A = int(math.floor(tA)) if optA else 300

    xsol = extract_x_solution(mA, n, weeks_pairs)

    # Output Stage A (feasible): orientamento fittizio (min in casa) solo per formattare la matrice
    s_dummy = {(i, j, w): 1 for w in range(1, n) for (i, j) in weeks_pairs[w - 1]}
    sol_matrix_feas = extract_solution_matrix(n, weeks_pairs, xsol, s_dummy)

    approaches = {}
    name_feas = f"mip_{solver_name}_feas_{'sym' if use_symmetry_breaking else 'nosym'}"
    approaches[name_feas] = {
        "time": reported_time_A,
        "optimal": bool(optA),
        "obj": None,
        "sol": sol_matrix_feas
    }

    if no_objective:
        _write_json(n, approaches)
        print(f"[{name_feas}] n={n} | time={reported_time_A}s | optimal={optA}")
        print(f"-> JSON: res/MIP/{n}.json")
        return

    # ----- Stage B -----
    mB = build_stageB_model(n, weeks_pairs, use_symmetry_breaking=use_symmetry_breaking)
    optB = SolverFactory(solver_name)
    apply_timelimit(optB, solver_name, budget_B, mip_gap=0.0)

    t0 = _time.time()
    resB = optB.solve(mB, tee=False)
    tB = _time.time() - t0
    feasB, optB_flag, _ = term_flags(resB)
    reported_time_B = int(math.floor(tB)) if optB_flag else 300

    # Estrai s
    ssol = {}
    def sval(v):
        try:
            return value(v)
        except:
            return None
    for (i, j, w) in mB.EW.data():
        v = sval(mB.s[(i, j, w)])
        ssol[(i, j, w)] = 1 if (v is not None and v >= 0.5) else 0

    sol_matrix_obj = extract_solution_matrix(n, weeks_pairs, xsol, ssol)
    try:
        obj_val = float(value(mB.Obj))
        obj_out = int(round(obj_val))
    except:
        obj_out = None

    name_obj = f"mip_{solver_name}_obj_{'sym' if use_symmetry_breaking else 'nosym'}"
    approaches[name_obj] = {
        "time": reported_time_B,
        "optimal": bool(optB_flag),
        "obj": obj_out,
        "sol": sol_matrix_obj
    }

    _write_json(n, approaches)

    print(f"[{name_feas}] n={n} | time={reported_time_A}s | optimal={optA}")
    print(f"[{name_obj}]  n={n} | time={reported_time_B}s | optimal={optB_flag} | obj={obj_out}")
    print(f"-> JSON: res/MIP/{n}.json")


def _write_json(n, data_dict):
    os.makedirs("res/MIP", exist_ok=True)
    out_path = f"res/MIP/{n}.json"
    if os.path.exists(out_path):
        with open(out_path, "r", encoding="utf-8") as f:
            data = json.load(f)
    else:
        data = {}
    data.update(data_dict)
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2)

# ==========
# CLI
# ==========

def main():
    ap = argparse.ArgumentParser(description="STS MIP (Pyomo) – round-robin + Hungarian warm-start + 2-stage ≤300s")
    ap.add_argument("--n", type=int, required=True, help="numero squadre (pari)")
    ap.add_argument("--solver", type=str, default="highs", help="highs | cbc | gurobi | cplex ...")
    ap.add_argument("--timelimit", type=int, default=300, help="budget totale (sec)")
    ap.add_argument("--splitA", type=float, default=0.9, help="quota tempo Stage A (0<split≤1)")
    ap.add_argument("--no_symbreak", action="store_true", help="disabilita symmetry breaking")
    ap.add_argument("--no_priority", action="store_true", help="disabilita branching priorities (Gurobi/CPLEX)")
    ap.add_argument("--no_objective", action="store_true", help="salta Stage B (solo feasible)")
    args = ap.parse_args()

    try:
        run(
            n=args.n,
            solver_name=args.solver,
            total_timelimit=args.timelimit,
            split_A=args.splitA,
            use_symmetry_breaking=not args.no_symbreak,
            use_priorities=not args.no_priority,
            no_objective=args.no_objective
        )
    except Exception as e:
        print(f"Errore: {e}", file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    main()

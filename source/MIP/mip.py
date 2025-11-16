import argparse
import json
import math
import os
import sys
import time as _time

from pyomo.environ import (
    ConcreteModel, Set, Var, Binary, NonNegativeReals, RangeSet, Constraint,
    Objective, minimize, value, Param, SolverFactory
)
from pyomo.opt import TerminationCondition

# --------------------------
# Utils: round-robin schedule
# --------------------------

def round_robin_pairs(n):
    assert n % 2 == 0 and n >= 2
    arr = list(range(1, n + 1))  # 1..n
    weeks = []
    for _ in range(n - 1):
        pairs = []
        for k in range(n // 2):
            a = arr[k]
            b = arr[-(k + 1)]
            i, j = (a, b) if a < b else (b, a)
            pairs.append((i, j))
        weeks.append(pairs)
        # rotate keeping arr[0] fixed: [a0, a1, ..., a_{n-2}, a_{n-1}] -> [a0, a_{n-1}, a1, ..., a_{n-2}]
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
    return norm_weeks

# --------------------------
# Warm-start greedy for Stage A
# --------------------------

def greedy_period_assignment(weeks_pairs, n):
    W = len(weeks_pairs)
    P = n // 2
    counts = {(i, p): 0 for i in range(1, n + 1) for p in range(1, P + 1)}
    occupied = {(w + 1, p): False for w in range(W) for p in range(1, P + 1)}
    x0 = {}
    for w_idx, pairs in enumerate(weeks_pairs, start=1):
        def score_pair(e):
            i, j = e
            mi = max(counts[(i, p)] for p in range(1, P + 1))
            mj = max(counts[(j, p)] for p in range(1, P + 1))
            return max(mi, mj)
        pairs_sorted = sorted(pairs, key=score_pair, reverse=True)
        for e in pairs_sorted:
            i, j = e
            period_order = sorted(range(1, P + 1), key=lambda p: counts[(i, p)] + counts[(j, p)])
            for p in period_order:
                if occupied[(w_idx, p)]: 
                    continue
                if counts[(i, p)] >= 2 or counts[(j, p)] >= 2:
                    continue
                x0[((i, j), w_idx, p)] = 1
                occupied[(w_idx, p)] = True
                counts[(i, p)] += 1
                counts[(j, p)] += 1
                break
    return x0

# --------------------------
# Stage A: Feasible (x only)
# --------------------------

def build_stageA_model(n, weeks_pairs, use_symmetry_breaking=True):
    m = ConcreteModel(name=f"STS_MIP_StageA_n{n}")

    m.N = Param(initialize=n)
    m.Wn = Param(initialize=n - 1)
    m.Pn = Param(initialize=n // 2)

    m.W = RangeSet(1, n - 1)
    m.P = RangeSet(1, n // 2)
    m.T = RangeSet(1, n)

    # (i,j,w) ONLY for pairs scheduled in week w (i<j)
    E_weeks = []
    for w_idx, pairs in enumerate(weeks_pairs, start=1):
        for e in pairs:
            E_weeks.append((e[0], e[1], w_idx))
    m.EW = Set(dimen=3, initialize=E_weeks, ordered=True)   # (i,j,w) with i<j

    # x[(i,j,w), p] binary
    m.x = Var(m.EW, m.P, within=Binary)

    # 1) each match (i,j) in week w goes to exactly one period
    def one_period_per_match(m, i, j, w):
        return sum(m.x[(i, j, w), p] for p in m.P) == 1
    m.OnePeriodPerMatch = Constraint(m.EW, rule=one_period_per_match)

    # 2) one match per slot (w,p)
    def one_match_per_slot(m, w, p):
        return sum(m.x[(i, j, ww), p] for (i, j, ww) in m.EW if ww == w) == 1
    m.OneMatchPerSlot = Constraint(m.W, m.P, rule=one_match_per_slot)

    # 3) period cap: each team appears in the same period at most twice over the tournament
    def period_cap(m, i, p):
        return sum(m.x[(a, b, w), p] for (a, b, w) in m.EW if (a == i or b == i)) <= 2
    m.PeriodCap = Constraint(m.T, m.P, rule=period_cap)

    # (implied) team-week participation =1
    def team_week_exactly_one(m, i, w):
        return sum(m.x[(a, b, ww), p]
                   for (a, b, ww) in m.EW if ww == w and (a == i or b == i)
                   for p in m.P) == 1
    m.TeamWeek = Constraint(m.T, m.W, rule=team_week_exactly_one)

    # Symmetry breaking: fix week-1 matching to period indices
    if use_symmetry_breaking:
        week1_pairs = weeks_pairs[0]
        for idx, e in enumerate(week1_pairs, start=1):
            m.add_component(f"SB_w1_p{idx}",
                            Constraint(expr=m.x[(e[0], e[1], 1), idx] == 1))

    return m

# --------------------------
# Stage B: Objective (s, dev), with x fixed
# --------------------------

def build_stageB_model(n, weeks_pairs, fixed_x, use_symmetry_breaking=True):
    m = ConcreteModel(name=f"STS_MIP_StageB_n{n}")

    m.N = Param(initialize=n)
    m.Wn = Param(initialize=n - 1)
    m.Pn = Param(initialize=n // 2)

    m.W = RangeSet(1, n - 1)
    m.P = RangeSet(1, n // 2)
    m.T = RangeSet(1, n)

    E_weeks = []
    for w_idx, pairs in enumerate(weeks_pairs, start=1):
        for e in pairs:
            E_weeks.append((e[0], e[1], w_idx))
    m.EW = Set(dimen=3, initialize=E_weeks, ordered=True)

    # s[(i,j,w)] in {0,1}: s=1 -> i (min) is HOME vs j
    m.s = Var(m.EW, within=Binary)

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

    if use_symmetry_breaking and weeks_pairs[0]:
        e0 = weeks_pairs[0][0]
        m.SB_orient = Constraint(expr=m.s[(e0[0], e0[1], 1)] == 1)

    return m

# --------------------------
# Solve helpers
# --------------------------

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

# --------------------------
# Extractors
# --------------------------

def extract_x_solution(model, n, weeks_pairs):
    P = n // 2
    xsol = {}
    def sval(v):
        try:
            return value(v)
        except:
            return None
    for w_idx, pairs in enumerate(weeks_pairs, start=1):
        for e in pairs:
            for p in range(1, P + 1):
                v = sval(model.x[(e[0], e[1], w_idx), p])
                xsol[((e[0], e[1], w_idx), p)] = 1 if (v is not None and v >= 0.5) else 0
    return xsol

def extract_solution_matrix(n, weeks_pairs, xsol, ssol):
    W = n - 1
    P = n // 2
    mat = [[None for _ in range(W)] for _ in range(P)]
    s_map = {(i, j, w): v for (i, j, w), v in ssol.items()}
    for w in range(1, W + 1):
        for e in weeks_pairs[w - 1]:
            p_chosen = None
            for p in range(1, P + 1):
                if xsol.get(((e[0], e[1], w), p), 0) == 1:
                    p_chosen = p
                    break
            if p_chosen is None:
                continue
            s = s_map.get((e[0], e[1], w), 1)
            home, away = (e[0], e[1]) if s >= 0.5 else (e[1], e[0])
            mat[p_chosen - 1][w - 1] = [home, away]
    for p in range(P):
        for w in range(W):
            if mat[p][w] is None:
                mat[p][w] = [None, None]
    return mat

# --------------------------
# Main run
# --------------------------

def run(n: int,
        solver_name: str = "cbc",
        total_timelimit: int = 300,
        split_A: float = 0.8,
        use_symmetry_breaking: bool = True,
        disable_warmstart: bool = False,
        no_objective: bool = False):

    if n % 2 != 0 or n < 2:
        raise ValueError("n must be an even integer >= 2.")   
    
    if solver_name == 'cplex':
        print('using cplex')
        # opt = SolverFactory('cplex', executable='/home/filippo/CPLEX_Studio2211/cplex/bin/x86-64_linux/cplex')
        # opt = SolverFactory('cplex', executable='/home/filippo/CPLEX-old-version/cplex/bin/x86-64_linux/cplex')
        opt = SolverFactory('cplex', executable='/home/filippo/CPLEX/cplex/bin/x86-64_linux/cplex')
    else:
        opt = SolverFactory(solver_name)

    if opt is None or not opt.available():
        raise RuntimeError(f"Solver '{solver_name}' non disponibile o non installato.")

    weeks_pairs = round_robin_pairs(n)
    budget_A = max(1, int(total_timelimit * split_A))
    budget_B = max(1, int(total_timelimit - budget_A))

    # ----- Stage A -----
    mA = build_stageA_model(n, weeks_pairs, use_symmetry_breaking=use_symmetry_breaking)

    if not disable_warmstart:
        x0 = greedy_period_assignment(weeks_pairs, n)
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

    # build Stage A output matrix (orientation dummy = home=min)
    sol_matrix_feas = extract_solution_matrix(
        n, weeks_pairs, xsol,
        {(i, j, w): 1 for w in range(1, n) for (i, j) in weeks_pairs[w - 1]}
    )

    approach_entries = {}
    warm_label = "warm" if not disable_warmstart else "nowarm"
    approach_name_feas = (
        f"mip_{solver_name}_feas_{'sym' if use_symmetry_breaking else 'nosym'}_{warm_label}"
    )
    approach_entries[approach_name_feas] = {
        "time": reported_time_A,
        "optimal": bool(optA),
        "obj": None,
        "sol": sol_matrix_feas
    }

    if no_objective:
        _write_json(n, approach_entries)
        print(f"[{approach_name_feas}] n={n} | time={reported_time_A}s | optimal={optA}")
        print(f"-> JSON: res/MIP/{n}.json")
        return

    # ----- Stage B -----
    mB = build_stageB_model(n, weeks_pairs, xsol, use_symmetry_breaking=use_symmetry_breaking)
    if solver_name == 'cplex':
        print('using cplex')
        # optB = SolverFactory('cplex', executable='/home/filippo/CPLEX_Studio2211/cplex/bin/x86-64_linux/cplex')
        # optB = SolverFactory('cplex', executable='/home/filippo/CPLEX-old-version/cplex/bin/x86-64_linux/cplex')
        optB = SolverFactory('cplex', executable='/home/filippo/CPLEX/cplex/bin/x86-64_linux/cplex')
    else:
        optB = SolverFactory(solver_name)
    apply_timelimit(optB, solver_name, budget_B, mip_gap=0.0)

    t0 = _time.time()
    resB = optB.solve(mB, tee=False)
    tB = _time.time() - t0
    feasB, optB_flag, _ = term_flags(resB)
    reported_time_B = int(math.floor(tB)) if optB_flag else 300

    # extract s
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

    approach_name_obj = (
        f"mip_{solver_name}_obj_{'sym' if use_symmetry_breaking else 'nosym'}_{warm_label}"
    )
    approach_entries[approach_name_obj] = {
        "time": reported_time_B,
        "optimal": bool(optB_flag),
        "obj": obj_out,
        "sol": sol_matrix_obj
    }

    _write_json(n, approach_entries)

    print(f"[{approach_name_feas}] n={n} | time={reported_time_A}s | optimal={optA}")
    print(f"[{approach_name_obj}]  n={n} | time={reported_time_B}s | optimal={optB_flag} | obj={obj_out}")
    print(f"-> JSON: res/MIP/{n}.json")


def _write_json(n, entries_dict):
    os.makedirs("res/MIP", exist_ok=True)
    out_path = f"res/MIP/{n}.json"
    if os.path.exists(out_path):
        with open(out_path, "r", encoding="utf-8") as f:
            data = json.load(f)
    else:
        data = {}
    data.update(entries_dict)
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2)

# --------------------------
# CLI
# --------------------------

def main():
    ap = argparse.ArgumentParser(description="STS with MIP (Pyomo) – 2-stage in ≤300s (single run)")
    ap.add_argument("--n", type=int, required=True, help="numero squadre (pari)")
    ap.add_argument("--solver", type=str, default="highs", help="highs | cbc | gurobi | cplex ...")
    ap.add_argument("--timelimit", type=int, default=300, help="budget totale in secondi (default 300)")
    ap.add_argument("--splitA", type=float, default=0.95, help="quota tempo Stage A (0<split≤1), default 0.9")
    ap.add_argument("--no_symbreak", action="store_true", help="disabilita symmetry breaking")
    ap.add_argument("--no_warmstart", action="store_true", help="disabilita warm-start greedy")
    ap.add_argument("--no_objective", action="store_true", help="salta Stage B (solo feasible)")
    args = ap.parse_args()

    try:
        run(
            n=args.n,
            solver_name=args.solver,
            total_timelimit=args.timelimit,
            split_A=args.splitA,
            use_symmetry_breaking=not args.no_symbreak,
            disable_warmstart=args.no_warmstart,
            no_objective=args.no_objective
        )
    except Exception as e:
        print(f"Errore: {e}", file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    main()

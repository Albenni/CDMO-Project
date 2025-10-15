#!/usr/bin/env bash
# bash script/run_sat_dec.sh
set -e
N=14  # number of states
# echo "Current working directory: $(pwd)"
echo "Running SAT with N=$N on Z3"
python source/SAT/sat_decision.py $N z3

S='minisat22'
# S='glucose3'
# S='lingeling'
echo "Running SAT with N=$N on $S"
python source/SAT/sat_decision.py $N $S

# python3 source/SAT/run_sat.py --n 6 --backend pysat --solver cadical
echo "Result at: res/SAT/${N}.json"

python3 script/solution_checker.py res/SAT

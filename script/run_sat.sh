#!/usr/bin/env bash
# bash script/run_sat_dec.sh
set -Eeuo pipefail

# Decide N:
# - if we're interactive and no argument was passed -> prompt
# - otherwise use $1 or default 18
if [ -t 0 ] && [ "${1-}" = "" ]; then
  # avoid set -e causing a failure on read in case of EOF
  read -rp "Enter N [default 18]: " N_IN || true
  N="${N_IN:-18}"
else
  N="${1:-18}"
fi

# Validate that it's a positive integer
if ! [[ "$N" =~ ^[0-9]+$ ]]; then
  echo "Error: N must be a positive integer." >&2
  exit 1
fi

# Define solvers array
solvers=("z3" "glucose3" "minisat22")

# Cycle through solvers
for S in "${solvers[@]}"; do
  echo "[SAT Decision] Running SAT with N=$N on $S"
  # Run solvers and handle potential failures
  python -u source/SAT/sat_decision.py "$N" "$S" || \
    echo "[SAT Decision] Warning: solver $S not available or failed."

  echo "[SAT Optimization] Running SAT with N=$N on $S"
  python -u source/SAT/sat_optimization.py "$N" "$S" || \
    echo "[SAT Optimization] Warning: solver $S not available or failed."

  echo "[SAT Decision no SB] Running SAT with N=$N on $S without SB"
  # Run solvers with no symmetry and handle potential failures
  python -u source/SAT/sat_decision.py "$N" "$S" --no-sym|| \
    echo "[SAT Decision no SB] Warning: solver $S not available or failed."

  echo "[SAT Optimization] Running SAT with N=$N on $S without SB"
  python -u source/SAT/sat_optimization.py "$N" "$S" --no-sym|| \
    echo "[SAT Optimization] Warning: solver $S not available or failed."
done

echo "[SAT] Result at: res/SAT/${N}.json"
python -u script/solution_checker.py res/SAT || \
  echo "[SAT] solution_checker: warning (check path/output)."

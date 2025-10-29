#!/usr/bin/env bash
# bash script/run_sat_dec.sh
set -Eeuo pipefail

# Decide N:
# - if we're interactive (TTY) and no argument was passed -> prompt
# - otherwise use $1 or default 16
if [ -t 0 ] && [ "${1-}" = "" ]; then
  # avoid set -e causing a failure on read in case of EOF
  read -rp "Enter N [default 16]: " N_IN || true
  N="${N_IN:-16}"
else
  N="${1:-16}"
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
  echo "[run_sat_dec] Running SAT with N=$N on $S"
  # Run solver and handle potential failures
  python -u source/SAT/sat_decision.py "$N" "$S" || \
    echo "[run_sat_dec] Warning: solver $S not available or failed."
done

echo "[run_sat_dec] Result at: res/SAT/${N}.json"
python -u script/solution_checker.py res/SAT || \
  echo "[run_sat_dec] solution_checker: warning (check path/output)."

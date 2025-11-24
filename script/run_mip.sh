#!/usr/bin/env bash
# Run all MIP combinations with/without symmetry breaking and warm-start
# for: cbc, cplex, highs

set -e

# --- Parameter N ---
if [ -z "$1" ]; then
  echo "No n specified. Using n=16 (default)."
  N=16
else
  N="$1"
fi

SOLVERS=("cbc" "highs") # "cplex"

echo "Running with n = $N"

for solver in "${SOLVERS[@]}"; do
  echo
  echo "==========================================="
  echo ">>> Solver: $solver  (n = $N)"
  echo "==========================================="

  echo
  echo "→ [1/4] no_symbreak + no_warmstart"
  python source/MIP/mip.py --n "$N" --solver "$solver" --no_symbreak --no_warmstart
  echo "-----------------------------------------------------------"

  echo
  echo "→ [2/4] symbreak + no_warmstart"
  python source/MIP/mip.py --n "$N" --solver "$solver" --no_warmstart
  echo "-----------------------------------------------------------"

  echo
  echo "→ [3/4] no_symbreak + warmstart"
  python source/MIP/mip.py --n "$N" --solver "$solver" --no_symbreak
  echo "-----------------------------------------------------------"

  echo
  echo "→ [4/4] symbreak + warmstart (default)"
  python source/MIP/mip.py --n "$N" --solver "$solver"
  echo "-----------------------------------------------------------"

  echo
  echo "solver completed: $solver"
  echo
done

echo "All tests completed!"

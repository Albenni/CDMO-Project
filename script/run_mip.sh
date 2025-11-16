#!/usr/bin/env bash
# Esegue tutte le combinazioni MIP con/without symmetry breaking e warm-start
# per i solver: cbc, cplex, highs
# Tutto l'output va al terminale

set -e  # interrompe in caso di errore

N=18
SOLVERS=("cplex" "highs")

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
  echo "Completato solver: $solver"
  echo
done

echo "🎯 Tutti i test completati con successo!"

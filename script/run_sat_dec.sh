#!/usr/bin/env bash
# bash script/run_sat_dec.sh
set -Eeuo pipefail

# Chiedi N da tastiera; se premi solo Invio usa 16
read -rp "Inserisci N [16]: " N
N=${N:-16}

# Valida che sia un intero positivo
if ! [[ "$N" =~ ^[0-9]+$ ]]; then
  echo "Errore: N deve essere un intero positivo." >&2
  exit 1
fi

echo "Running SAT with N=$N on Z3"
python source/SAT/sat_decision.py "$N" z3

# S='minisat22'
S='glucose3'
echo "Running SAT with N=$N on $S"
# python source/SAT/sat_decision.py "$N" "$S"

echo "Result at: res/SAT/${N}.json"
python3 script/solution_checker.py res/SAT

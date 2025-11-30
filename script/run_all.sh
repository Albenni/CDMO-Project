#!/usr/bin/env bash
# run_all.sh — runs CP, MIP and SAT (plus solution checker) for a given N
# Usage: ./script/run_all.sh <N>

set -Eeuo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

RUN_CP="$SCRIPT_DIR/run_cp.sh"
RUN_MIP="$SCRIPT_DIR/run_mip.sh"
RUN_SAT="$SCRIPT_DIR/run_sat.sh"
CHECKER="$ROOT_DIR/script/solution_checker.py"

# --- read parameter N ---
if [ "${1-}" = "" ]; then
  echo "Usage: $0 <N>" >&6
  exit 2
fi
N="$1"

# minimal check on N
if ! [[ "$N" =~ ^[0-9]+$ ]]; then
  echo "Error: N must be a positive integer." >&6
  exit 1
fi

ts() { date +"%Y-%m-%d %H:%M:%S"; }

echo "[$(ts)] === Running all models for N=$N ==="

# --- CP ---
if [ -f "$RUN_CP" ]; then
  echo "[$(ts)] >>> CP: $RUN_CP $N"
  bash "$RUN_CP" "$N" || echo "[$(ts)] [WARN] CP pipeline failed"
else
  echo "[$(ts)] [WARN] CP runner not found at $RUN_CP"
fi

# --- MIP ---
if [ -f "$RUN_MIP" ]; then
  echo "[$(ts)] >>> MIP: $RUN_MIP $N"
  bash "$RUN_MIP" "$N" || echo "[$(ts)] [WARN] MIP pipeline failed"
else
  echo "[$(ts)] [WARN] MIP runner not found at $RUN_MIP"
fi

# --- SAT ---
if [ -f "$RUN_SAT" ]; then
  echo "[$(ts)] >>> SAT: $RUN_SAT $N"
  bash "$RUN_SAT" "$N" || echo "[$(ts)] [WARN] SAT pipeline failed"
else
  echo "[$(ts)] [WARN] SAT runner not found at $RUN_SAT"
fi

echo "[$(ts)] === Checking solutions with solution_checker.py ==="

if [ -f "$CHECKER" ]; then
  # CP
  if [ -d "$ROOT_DIR/res/CP" ]; then
    echo "[$(ts)] -> Checking CP results in res/CP"
    python -u "$CHECKER" "$ROOT_DIR/res/CP" || \
      echo "[$(ts)] [WARN] CP solution check failed"
  fi

  # MIP
  if [ -d "$ROOT_DIR/res/MIP" ]; then
    echo "[$(ts)] -> Checking MIP results in res/MIP"
    python -u "$CHECKER" "$ROOT_DIR/res/MIP" || \
      echo "[$(ts)] [WARN] MIP solution check failed"
  fi
else
  echo "[$(ts)] [WARN] solution_checker.py not found at $CHECKER"
fi

echo "[$(ts)] === Done ==="

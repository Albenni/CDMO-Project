#!/usr/bin/env bash
# run_cp.sh — run all combinations (dec/opt × SB/IC) for a single N
# Usage: ./script/run_cp.sh <N>
# Notes:
#   - Uses run_cp.py in the same folder.
#   - No --solver is passed: the runner will use its default SOLVERS list.

set -u -o pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RUNNER="$SCRIPT_DIR/run_cp.py"

# Modes and variants ("" = baseline: SB on, IC on)
MODES=("dec" "opt")
VARIANTS=(
  ""            # baseline: SB on,  IC on
  "noSB"        # SB off,   IC on
  "noIC"        # SB on,    IC off
  "noSB noIC"   # SB off,   IC off
)

ts() { date +"%Y-%m-%d %H:%M:%S"; }

# --- args ---
if [[ $# -ne 1 ]]; then
  echo "Usage: $0 <N>" >&2
  exit 2
fi
N="$1"

# Light sanity checks (do not exit)
if ! [[ "$N" =~ ^[0-9]+$ ]]; then
  echo "WARN: N must be an integer (got: '$N')." >&2
fi
if (( N % 2 != 0 )); then
  echo "WARN: N should be even for STS (got: $N)." >&2
fi
if (( N == 4 )); then
  echo "WARN: N=4 is excluded by the period-usage requirement." >&2
fi

# --- runs ---
for mode in "${MODES[@]}"; do
  for variant in "${VARIANTS[@]}"; do
    if [[ -z "$variant" ]]; then
      echo "[$(ts)] >>> python $RUNNER $mode $N"
      python "$RUNNER" "$mode" "$N" || echo "[$(ts)] WARN: run failed for mode=$mode n=$N (baseline)"
    else
      # Intentional word-splitting to pass multiple flags (e.g., "noSB noIC")
      echo "[$(ts)] >>> python $RUNNER $mode $N $variant"
      python "$RUNNER" "$mode" "$N" $variant || echo "[$(ts)] WARN: run failed for mode=$mode n=$N ($variant)"
    fi
  done
done

echo "[$(ts)] Done."

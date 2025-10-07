set -euo pipefail

# Esegue alcune istanze con i due approcci
ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
pushd "$ROOT_DIR/SAT" >/dev/null

for n in 6 8 10 12 14; do
  for a in basic symbreak; do
    echo -e "== Running n=$n approach=$a ==="
    echo
    python run_sat.py --n "$n" --approach "$a"
    echo
  done
done

python ../scripts/solution_checker.py ../res/SAT

#!/bin/sh
# Usage: tools/cosim/run.sh [N] [SEED] [GENERATORS]   (e.g. gen_fp,gen_simd2)
# Runs N random single-instruction tests on this machine's CPU and compares
# every result with the Lean model.
set -e
N=${1:-5000}
SEED=${2:-1}
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
OUT=${COSIM_OUT:-$(mktemp -d)}
mkdir -p "$OUT"
python3 "$HERE/gen.py" -n "$N" --seed "$SEED" --out "$OUT" ${3:+--only "$3"}
clang -O1 -o "$OUT/harness" "$HERE/harness.c" "$HERE/harness_asm.s" "$OUT/tests.s"
"$OUT/harness" "$OUT/inputs.bin" > "$OUT/hw.txt"
(cd "$ROOT" && lake build m1 >/dev/null && .lake/build/bin/m1 cosim "$OUT/hw.txt")

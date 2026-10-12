#!/usr/bin/env bash
# Runs every check behind the paper:
#   1. regenerates the Lean certificate and compares it with the committed files;
#   2. builds the Lean project (kernel check of all 4,022 certificate units) and
#      prints the axioms of the main theorems;
#   3. runs the exhaustive search at q = 1389 in C, C++, Julia and Python
#      (expected: canonical=0) and the C control at q = 1383, which must find
#      the canonical P(674,461,195,35,18).
# Usage: bash scripts/run_all.sh               (all steps)
#        SKIP_LEAN=1 bash scripts/run_all.sh   (searches only)
# Tools: gcc with OpenMP, g++ (C++17), julia, python3 with numpy, elan/lake.
# Outputs go to results/ (or $OUT); THREADS sets the number of threads.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT="${OUT:-$ROOT/results}"
THREADS="${THREADS:-$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 4)}"
mkdir -p "$OUT"
BIN="$(mktemp -d)"
trap 'rm -rf "$BIN"' EXIT
need() { command -v "$1" >/dev/null || { echo "missing tool: $1" >&2; exit 2; }; }
expect() { grep -q -- "$2" "$1" || { echo "FAILED: $1 lacks '$2'" >&2; exit 1; }; echo "ok: $(tail -n 1 "$1")"; }

if [ -z "${SKIP_LEAN:-}" ]; then
  need lake
  bash "$ROOT/lean/generate/regenerate.sh"
  (cd "$ROOT/lean" && { lake exe cache get || echo "no Mathlib cache; building Mathlib from source"; })
  (cd "$ROOT/lean" && lake build)
  (cd "$ROOT/lean" && lake env lean Axioms.lean) | tee "$OUT/axioms.txt"
  # Every printed theorem uses at most propext, Classical.choice and Quot.sound.
  if grep "depends on axioms" "$OUT/axioms.txt" | sed 's/.*\[\(.*\)\]/\1/' | tr ',' '\n' \
       | sed 's/ //g' | grep -v -x -E "propext|Classical.choice|Quot.sound" | grep -q .; then
    echo "FAILED: nonstandard axiom" >&2; exit 1
  fi
  for t in LiuIndex.not_mem_Iwps4 LiuIndex.exists_age_four LiuIndex.not_kasprzykCanonical; do
    grep -q "'$t' depends on axioms: \[propext, Classical.choice, Quot.sound\]" "$OUT/axioms.txt" \
      || { echo "FAILED: axioms of $t" >&2; exit 1; }
  done
  echo "ok: Lean build and axioms"
fi

need gcc; need g++; need julia; need python3
gcc -O2 -fopenmp -o "$BIN/wps_c" "$ROOT/code/c/wps_search.c"
g++ -O2 -std=c++17 -pthread -o "$BIN/wps_cpp" "$ROOT/code/cpp/wps_search.cpp"
OMP_NUM_THREADS="$THREADS" "$BIN/wps_c" 1389 > "$OUT/full_c.out"
expect "$OUT/full_c.out" "q=1389 tuples=1301769806 wellformed=874763737 canonical=0"
"$BIN/wps_cpp" 1389 "$THREADS" > "$OUT/full_cpp.out"
expect "$OUT/full_cpp.out" "q=1389 tuples=1301769806 wellformed=874763737 canonical=0"
julia -t "$THREADS" "$ROOT/code/julia/wps_search.jl" 1389 > "$OUT/full_jl.out"
expect "$OUT/full_jl.out" "q=1389 tuples=1301769806 wellformed=874763737 canonical=0"
python3 -B "$ROOT/code/python/wps_search.py" 1389 "$THREADS" > "$OUT/full_py.out"
expect "$OUT/full_py.out" "q=1389 tuples=1301769806 wellformed=874763737 canonical=0"
OMP_NUM_THREADS="$THREADS" "$BIN/wps_c" 1383 > "$OUT/control_q1383_c.out"
expect "$OUT/control_q1383_c.out" "canonical 674 461 195 35 18"
echo "all checks passed"

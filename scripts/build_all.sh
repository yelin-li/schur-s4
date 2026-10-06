#!/usr/bin/env bash
# Builds the whole development, including the three exhaustive branches.
#
# The three branches are independent, so they are verified concurrently.
#
# Usage:  bash scripts/build_all.sh

set -euo pipefail
cd "$(dirname "$0")/.."

echo "== kernel-checked core =="
lake build Schur Symmetry RuleB

echo "== exhaustive branches (parallel) =="
pids=()
for mod in BranchB0 BranchB1 BranchB2; do
  ( start=$(date +%s)
    lake env lean -o ".lake/build/lib/lean/${mod}.olean" "${mod}.lean"
    end=$(date +%s)
    echo "${mod} $((end - start))s" ) &
  pids+=($!)
done
for pid in "${pids[@]}"; do wait "$pid"; done

echo "== assembly =="
lake env lean -o ".lake/build/lib/lean/S4.olean" "S4.lean"
lake env lean "Verify.lean"

echo
echo "Done. The main results are:"
echo "  Schur.no_good_four_45  : no 4-colouring of {1,...,45} is sum-free"
echo "  Schur.four_colors_exact: S(4) = 44"

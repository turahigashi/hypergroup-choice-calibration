#!/usr/bin/env bash
# Rebuild the development and check that the recorded axiom audit is reproduced exactly.
#
#   ./scripts/verify.sh
#
# Requires elan/lake and a Mathlib build (see README).  Exits non-zero on any Lean error
# or any difference from logs/axioms.txt.
set -uo pipefail
cd "$(dirname "$0")/.."
out=$(mktemp)
lake env lean HypergroupCalibration.lean > "$out" 2>&1
status=$?
if grep -q "error" "$out"; then
  echo "FAIL: Lean reported errors"; grep "error" "$out" | head; exit 1
fi
grep -E "^'[^']+'( does not depend on any axioms| depends on axioms:)" "$out" > "$out.ax"
if diff -u logs/axioms.txt "$out.ax"; then
  echo "OK: $(wc -l < "$out.ax") axiom measurements reproduced exactly"
else
  echo "FAIL: the axiom audit differs from logs/axioms.txt"; exit 1
fi
exit $status

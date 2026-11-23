#!/bin/sh
# The stripped-hash line is the intake's contract with this workflow: exactly ONE line of the
# workflow may write a line that begins with its word, and it writes only a hash this run
# computed (red team, 2026-11-23). Run: sh .github/scripts/strip-line.test.sh
set -eu
W="$(dirname "$0")/../workflows/authoritative.yml"
n=$(grep -c 'JUDGED-STRIPPED' "$W" || true)
[ "$n" = 1 ] || { echo "FAIL: $n lines of the workflow name JUDGED-STRIPPED, exactly one may"; exit 1; }
grep -q 'then echo "JUDGED-STRIPPED sha256:$fsha"; else fsha=""; fi' "$W" || { echo "FAIL: the stripped-hash line is not the one form allowed"; exit 1; }
grep -q 'outside-strip.py" "$W/in/proof.lean" "$W/in/proof.stripped"' "$W" || { echo "FAIL: the workflow does not strip the downloaded file"; exit 1; }
echo "strip line: one writer, one form"

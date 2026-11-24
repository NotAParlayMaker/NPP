#!/bin/bash
# usage: run_one.sh GRAPHNAME K TIMELIMIT_SECONDS [extra args]
# Runs the CEGAR SAT search for a circuit of size <= K; logs to logs/NAME_kK.log.
cd "$(dirname "$0")"
name=$1; k=$2; tl=$3; shift 3
tag=${name}_k${k}$(echo "$@" | tr -d ' -')
start=$(date +%s.%N)
timeout --signal=KILL "$tl" python3 cegar_synth.py graphs/$name.json $k --out circuits/$tag.json "$@" > logs/$tag.log 2>&1
rc=$?
end=$(date +%s.%N)
if grep -q "RESULT SAT" logs/$tag.log; then st=SAT; elif grep -q "RESULT UNSAT" logs/$tag.log; then st=UNSAT; elif [ $rc -eq 137 ]; then st=TIMEOUT; else st=ERROR$rc; fi
printf "%s\t%s\t%s\t%s\t%.1f\n" "$name" "$k" "$*" "$st" "$(echo "$end - $start" | bc)" >> "${RESULTS:-results.tsv}"

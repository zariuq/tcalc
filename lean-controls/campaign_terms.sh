#!/bin/sh
# Run mutate_terms.sh over a list of exports in N parallel workers.
# usage: campaign_terms.sh LEAN_TCALC ORACLE OUT_DIR WORKERS STRIDE MAX_PER_FILE FILE...
# Each worker writes OUT_DIR/worker-K.log and keeps its disagreeing mutants in OUT_DIR/wK/.
set -u
BIN=$1; ORACLE=$2; OUT=$3; N=$4; STRIDE=$5; MAXF=$6; shift 6
HERE=$(dirname "$0")
mkdir -p "$OUT"
k=0
while [ "$k" -lt "$N" ]; do : > "$OUT/files-$k.txt"; mkdir -p "$OUT/w$k"; k=$((k+1)); done
i=0
for f in "$@"; do echo "$f" >> "$OUT/files-$((i % N)).txt"; i=$((i+1)); done
k=0
while [ "$k" -lt "$N" ]; do
  ( STRIDE=$STRIDE MAX_PER_FILE=$MAXF sh "$HERE/mutate_terms.sh" "$BIN" "$ORACLE" "$OUT/w$k" $(cat "$OUT/files-$k.txt") > "$OUT/worker-$k.log" 2>&1 ) &
  k=$((k+1))
done
wait
cat "$OUT"/worker-*.log | grep '^SUMMARY' | awk '{for(i=2;i<=NF;i++){split($i,a,"="); s[a[1]]+=a[2]}} END {printf "TOTAL"; for(k in s) printf " %s=%d", k, s[k]; printf "\n"}'

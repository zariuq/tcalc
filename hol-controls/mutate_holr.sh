#!/bin/sh
# Reference-mutation differential for a HOLRPLY1 replay checker against CeTTa's replay.
#
# usage: mutate_holr.sh HOL_TCALC CETTA MUTATE_HOLR WORKDIR STREAM.holr
#
# Mutants change one reference in one record (operand ARG of every STRIDE-th record from
# OFFSET, by DELTA, default -1) and carry a recomputed checksum.  Both checkers replay each
# mutant under the standard axiom policy.
#   ACCEPT-BAD   the checker accepts a mutant the reference refuses
#   REJECT-GOOD  the checker refuses a mutant the reference accepts
#   EMIT-DIFF    both accept and print different theorems
set -u
BIN=$1; CETTA=$2; MUT=$3; WORK=$4; STREAM=$5
STRIDE=${STRIDE:-997}; OFFSET=${OFFSET:-0}; ARG=${ARG:-0}; DELTA=${DELTA:--1}; MAXM=${MAX_MUTANTS:-400}
ulimit -c 0
nrec=$("$MUT" "$STREAM" --count)
total=0; agree_rej=0; agree_acc=0; acc_bad=0; rej_good=0; emit_diff=0; other=0
r=$OFFSET
while [ "$r" -lt "$nrec" ] && [ "$total" -lt "$MAXM" ]; do
  "$MUT" "$STREAM" "$WORK/mutant.holr" "$r" "$ARG" "$DELTA"; mrc=$?
  if [ "$mrc" -eq 0 ]; then
    ( timeout 120 "$BIN" --print-emits "$WORK/mutant.holr" > "$WORK/t.out" 2>/dev/null ); rc=$?
    ( timeout 300 "$CETTA" --lang hol "$WORK/mutant.holr" > "$WORK/c.out" 2>/dev/null ); orc=$?
    total=$((total+1))
    if [ "$rc" -eq 0 ] && [ "$orc" -eq 0 ]; then
      grep '^(thm\|	(thm' "$WORK/t.out" | sed 's/^[^	]*	//' > "$WORK/t.thms"
      grep '^(thm' "$WORK/c.out" > "$WORK/c.thms"
      if cmp -s "$WORK/t.thms" "$WORK/c.thms"; then agree_acc=$((agree_acc+1)); else emit_diff=$((emit_diff+1)); echo "EMIT-DIFF record=$r arg=$ARG"; fi
    elif [ "$rc" -eq 1 ] && [ "$orc" -ne 0 ]; then agree_rej=$((agree_rej+1))
    elif [ "$rc" -eq 0 ]; then acc_bad=$((acc_bad+1)); echo "ACCEPT-BAD record=$r arg=$ARG reference_rc=$orc"
    elif [ "$rc" -eq 1 ]; then rej_good=$((rej_good+1)); echo "REJECT-GOOD record=$r arg=$ARG"
    else other=$((other+1)); echo "OTHER rc=$rc reference_rc=$orc record=$r arg=$ARG"
    fi
  fi
  r=$((r + STRIDE))
done
rm -f "$WORK/mutant.holr" "$WORK/t.out" "$WORK/c.out" "$WORK/t.thms" "$WORK/c.thms"
echo "SUMMARY stream=$(basename "$STREAM") arg=$ARG delta=$DELTA mutants=$total both-reject=$agree_rej both-accept-same-theorems=$agree_acc accept-bad=$acc_bad reject-good=$rej_good emit-diff=$emit_diff other=$other"

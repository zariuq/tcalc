#!/bin/sh
# Single-byte mutation differential for an .mmb verifier against mm0-c.
# usage: fuzz_mmb.sh MMB_TCALC MM0_C MUTATE_BYTE FILE.mmb SPEC.mm0 WORKDIR [STRIDE] [MASK]
# For every STRIDE-th offset the byte is xor-ed with MASK; both verifiers run on the
# mutant with the same specification.  A mutant the checker accepts and mm0-c refuses
# is printed as ACCEPT-BAD; the reverse as REJECT-GOOD.  Crashes and timeouts are OTHER.
set -u
BIN=$1; ORACLE=$2; MUT=$3; MMB=$4; SPEC=$5; WORK=$6
STRIDE=${7:-17}; MASK=${8:-0x01}
size=$(wc -c < "$MMB")
off=0; n=0; same_acc=0; same_rej=0; acc_bad=0; rej_good=0; other=0
ulimit -c 0
while [ "$off" -lt "$size" ]; do
  "$MUT" "$MMB" "$WORK/mutant.mmb" "$off" "$MASK" || exit 2
  ( timeout 20 "$BIN" "$WORK/mutant.mmb" "$SPEC" >/dev/null 2>&1 ); rc=$?
  ( timeout 20 "$ORACLE" "$WORK/mutant.mmb" < "$SPEC" >/dev/null 2>&1 ); orc=$?
  n=$((n+1))
  if [ "$rc" -eq 0 ] && [ "$orc" -eq 0 ]; then same_acc=$((same_acc+1))
  elif [ "$rc" -eq 1 ] && [ "$orc" -ne 0 ]; then same_rej=$((same_rej+1))
  elif [ "$rc" -eq 0 ]; then acc_bad=$((acc_bad+1)); echo "ACCEPT-BAD offset=$off mask=$MASK oracle_rc=$orc"
  elif [ "$rc" -eq 1 ]; then rej_good=$((rej_good+1)); echo "REJECT-GOOD offset=$off mask=$MASK"
  else other=$((other+1)); echo "OTHER offset=$off mask=$MASK rc=$rc oracle_rc=$orc"
  fi
  off=$((off+STRIDE))
done
rm -f "$WORK/mutant.mmb"
echo "SUMMARY file=$(basename "$MMB") mutants=$n both-accept=$same_acc both-reject=$same_rej accept-bad=$acc_bad reject-good=$rej_good other=$other"

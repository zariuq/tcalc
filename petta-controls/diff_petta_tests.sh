#!/bin/sh
# PeTTa evaluator on tcalc against the reference PeTTa runtime, judged by the examples' own
# `!(test GOT WANT)` directives.
#
# usage: diff_petta_tests.sh DRIVER REFERENCE_CMD WORKDIR FILE.metta ...
#
# The reference prints one line with a check mark for every test directive that holds.  The
# driver prints TEST-PASS or TEST-FAIL for every answer of the form (test GOT WANT).
# One line per file:
#   ALL-PASS    the evaluator finished and passes exactly as many tests as the reference, none failed
#   SOME        the evaluator finished or stopped; it passes fewer tests than the reference
#   NONE        the evaluator passes no test of the file
#   NO-TESTS    the reference passes no test in this file (not counted)
#   NO-REF      the reference did not finish cleanly (not counted)
# The second field says how the evaluator ended: ok, fault, budget, crash.
set -u
DRV=$1; REF=$2; W=$3; shift 3
ulimit -c 0
all=0; some=0; none=0; notests=0; noref=0; total=0; tref=0; tpass=0; tfail=0
e_ok=0; e_fault=0; e_budget=0; e_crash=0
cd "$W" || exit 2
for f in "$@"; do
  total=$((total + 1)); b=$(basename "$f")
  ( timeout 30 $REF "$f" > ref.out 2> ref.err ); rrc=$?
  if [ "$rrc" -ne 0 ]; then noref=$((noref + 1)); echo "NO-REF - $b (reference rc=$rrc)"; continue; fi
  nref=$(grep -c '✅' ref.out)
  if [ "$nref" -eq 0 ]; then notests=$((notests + 1)); echo "NO-TESTS - $b"; continue; fi
  ( timeout 30 "$DRV" "$f" > drv.out 2> drv.err ); drc=$?
  case "$drc" in 0) end=ok; e_ok=$((e_ok + 1)) ;; 1) end=fault; e_fault=$((e_fault + 1)) ;; 2) end=budget; e_budget=$((e_budget + 1)) ;; *) end=crash; e_crash=$((e_crash + 1)) ;; esac
  np=$(grep -c '^TEST-PASS' drv.out); nf=$(grep -c '^TEST-FAIL' drv.out)
  tref=$((tref + nref)); tpass=$((tpass + np)); tfail=$((tfail + nf))
  if [ "$end" = ok ] && [ "$np" -eq "$nref" ] && [ "$nf" -eq 0 ]; then all=$((all + 1)); echo "ALL-PASS $end $b tests=$nref"
  elif [ "$np" -gt 0 ]; then some=$((some + 1)); echo "SOME $end $b reference=$nref pass=$np fail=$nf"
  else none=$((none + 1)); echo "NONE $end $b reference=$nref pass=0 fail=$nf"
  fi
done
rm -f ref.out ref.err drv.out drv.err
echo "SUMMARY files=$total all-pass=$all some=$some none=$none no-tests=$notests no-reference=$noref | evaluator ended ok=$e_ok fault=$e_fault budget=$e_budget crash=$e_crash | tests passed by the reference=$tref, by the evaluator=$tpass, failed by the evaluator=$tfail"

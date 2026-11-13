#!/usr/bin/env bash
# check.sh -- a plan leaf, end to end.
#
#   check.sh LEAF WORKDIR [SEED] [RANDOM]
#
# LEAF is a directory name here (pack, unpack, eqw, row_word, live,
# append_row, put_word, hyps_find, hyps_union). Into WORKDIR (never into the
# source tree):
#  1. the p1 tools, built from tcalc/native/p1 into WORKDIR/p1build;
#  2. the program's text and notes from LEAF/LEAF.metta, which must equal
#     LEAF/LEAF_prog.txt, the text that is proved;
#  3. the tests (LEAF/LEAF_tests.c: every run's expectations from an
#     independent model of the leaf's specification, pl_LEAF_spec in
#     tcalc/native/hol/plans_leaves.ml), run by the p1 reference evaluator
#     and the native code (p1run), with default and with hoisted emission:
#     every run must agree between the two, region bytes included, and meet
#     its expectations;
#  4. the image record, which must equal LEAF/LEAF.hol, the record whose x86
#     bytes are proved;
#  5. the instruction gate (tcalc/native/census, census:gate-exit) on
#     LEAF/LEAF.hol: every instruction in a form s2n-bignum's decoder takes.
# Exit status 0 iff every step passes.
set -u
here=$(cd "$(dirname "$0")" && pwd)
p1=$here/../p1
census=$here/../census/x86_census.metta
leaf=${1:?usage: check.sh LEAF WORKDIR [SEED] [RANDOM]}
work=${2:?usage: check.sh LEAF WORKDIR [SEED] [RANDOM]}
seed=${3:-7} nrandom=${4:-}
src=$here/$leaf
[ -f "$src/$leaf.metta" ] || { echo "check.sh: no leaf $leaf"; exit 2; }
mkdir -p "$work"; work=$(cd "$work" && pwd)
fail=0
step() { echo "== $leaf: $*"; }
check() { if "$@"; then :; else echo "FAILED: $*"; fail=1; fi; }

step "build the p1 tools"
make -s -C "$p1" BUILD="$work/p1build" "$work/p1build/p1run" || exit 2
p1run=$work/p1build/p1run

step "the program from MeTTa"
rm -f "$work/$leaf.txt" "$work/$leaf.notes"
check cetta --no-results "$src/$leaf.metta" "$work/$leaf.txt" "$work/$leaf.notes"
check cmp "$work/$leaf.txt" "$src/${leaf}_prog.txt" &&
  echo "$leaf.metta prints ${leaf}_prog.txt byte for byte"

step "tests, with the specification model's expectations"
gcc -O2 -Wall -Wextra -Werror "$src/${leaf}_tests.c" -o "$work/${leaf}_tests" ||
  { echo "cannot build ${leaf}_tests"; exit 2; }
"$work/${leaf}_tests" "$work/$leaf.p1t" "$seed" $nrandom || { echo "${leaf}_tests failed"; exit 2; }
for opt in "" --hoist; do
  out=$("$p1run" --quiet $opt "$src/${leaf}_prog.txt" "$work/$leaf.p1t"); st=$?
  echo "$out" | grep -v "^p1run" | head -20
  echo "$out" | grep "^p1run" | tail -1 | sed "s/^p1run:/p1run ${opt:-default}:/"
  [ $st = 0 ] && echo "$out" | tail -1 | grep -q " 0 DIFF;.* 0 missed$" || { echo "FAILED: p1run $opt $leaf"; fail=1; }
done

step "the image record"
check "$p1run" --image "$work/$leaf.hol" "$leaf" "$src/${leaf}_prog.txt" > /dev/null
check cmp "$work/$leaf.hol" "$src/$leaf.hol" && echo "$leaf.hol rebuilt from ${leaf}_prog.txt byte for byte"

step "the instruction gate"
mkdir -p "$work/gate"
printf '!(import! &self "%s")\n!(census:gate-exit "%s")\n' "$census" "$src/$leaf.hol" > "$work/gate/gate.metta"
TMPDIR="$work/gate" cetta "$work/gate/gate.metta" > "$work/gate/gate.out" 2>&1; gst=$?
grep "^gate " "$work/gate/gate.out"
grep -q "^gate pass $src/$leaf.hol:" "$work/gate/gate.out" && [ "$gst" -eq 0 ] ||
  { echo "FAILED: the instruction gate on $leaf.hol"; fail=1; }

[ "$fail" = 0 ] && echo "check.sh $leaf: all passed" || echo "check.sh $leaf: FAILURES"
exit $fail

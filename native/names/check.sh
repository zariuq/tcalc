#!/usr/bin/env bash
# check.sh -- intern_name, end to end.
#
#   check.sh WORKDIR [SEED] [RANDOM]
#
# Into WORKDIR (never into this directory):
#  1. the program's text and notes from intern_name.metta, which must equal
#     intern_name_prog.txt, the text that is proved;
#  2. the tests (intern_name_tests.c: expectations from a model of the
#     specification), run by the p1 reference evaluator and the native code
#     (p1run), with default and with hoisted emission: every run must agree
#     between the two, region bytes included, and meet its expectation;
#  3. the image record, which must equal intern_name.hol, the record whose
#     x86 bytes are proved.
# Exit status 0 iff every step passes.
set -u
here=$(cd "$(dirname "$0")" && pwd)
p1=$here/../p1
work=${1:?usage: check.sh WORKDIR [SEED] [RANDOM]}
seed=${2:-7} nrandom=${3:-}
mkdir -p "$work"; work=$(cd "$work" && pwd)
fail=0
step() { echo "== $*"; }
check() { if "$@"; then :; else echo "FAILED: $*"; fail=1; fi; }

step "build the p1 tools"
make -s -C "$p1" || exit 2

step "the program from MeTTa"
rm -f "$work/intern_name.txt" "$work/intern_name.notes"
check cetta --no-results "$here/intern_name.metta" "$work/intern_name.txt" "$work/intern_name.notes"
check cmp "$work/intern_name.txt" "$here/intern_name_prog.txt" &&
  echo "intern_name.metta prints intern_name_prog.txt byte for byte"

step "tests, with the specification's expectations"
gcc -O2 -Wall -Wextra -Werror "$here/intern_name_tests.c" -o "$work/intern_name_tests" ||
  { echo "cannot build intern_name_tests"; exit 2; }
"$work/intern_name_tests" "$work/names_diff.p1t" "$work/names_chain.p1t" "$seed" $nrandom ||
  { echo "intern_name_tests failed"; exit 2; }
for t in names_diff names_chain; do
  for opt in "" --hoist; do
    out=$("$p1/build/p1run" --quiet $opt "$here/intern_name_prog.txt" "$work/$t.p1t"); st=$?
    echo "$out" | grep -v "^p1run" | head -20
    echo "$out" | grep "^p1run" | tail -1 | sed "s/^p1run:/p1run $t ${opt:-default}:/"
    [ $st = 0 ] && echo "$out" | tail -1 | grep -q " 0 DIFF;.* 0 missed$" || { echo "FAILED: p1run $opt $t"; fail=1; }
  done
done

step "the image record"
check "$p1/build/p1run" --image "$work/intern_name.hol" intern_name "$here/intern_name_prog.txt" > /dev/null
check cmp "$work/intern_name.hol" "$here/intern_name.hol" &&
  echo "intern_name.hol rebuilt from intern_name_prog.txt byte for byte"

[ "$fail" = 0 ] && echo "check.sh: all passed" || echo "check.sh: FAILURES"
exit $fail

#!/usr/bin/env bash
# check.sh -- bind_walk, end to end.
#
#   check.sh WORKDIR [SEED] [RANDOM]
#
# Into WORKDIR (never into this directory):
#  1. the program's text and notes from bind_walk.metta, which must equal
#     bind_walk_prog.txt, the text that is proved;
#  2. the tests (bind_walk_tests.c: expectations from a model of the
#     algorithm, every model run checked against the specification), run by
#     the p1 reference evaluator and the native code (p1run), with default
#     and with hoisted emission: every run must agree between the two, region
#     bytes included, and meet its expectation;
#  3. the image record, which must equal bind_walk.hol, the record whose x86
#     bytes are proved.
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
rm -f "$work/bind_walk.txt" "$work/bind_walk.notes"
check cetta --no-results "$here/bind_walk.metta" "$work/bind_walk.txt" "$work/bind_walk.notes"
check cmp "$work/bind_walk.txt" "$here/bind_walk_prog.txt" &&
  echo "bind_walk.metta prints bind_walk_prog.txt byte for byte"

step "tests, with the algorithm's expectations and the specification's checks"
gcc -O2 -Wall -Wextra -Werror "$here/bind_walk_tests.c" -o "$work/bind_walk_tests" ||
  { echo "cannot build bind_walk_tests"; exit 2; }
"$work/bind_walk_tests" "$work/walk_diff.p1t" "$work/walk_chain.p1t" "$seed" $nrandom ||
  { echo "bind_walk_tests failed"; exit 2; }
for t in walk_diff walk_chain; do
  for opt in "" --hoist; do
    out=$("$p1/build/p1run" --quiet $opt "$here/bind_walk_prog.txt" "$work/$t.p1t"); st=$?
    echo "$out" | grep -v "^p1run" | head -20
    echo "$out" | grep "^p1run" | tail -1 | sed "s/^p1run:/p1run $t ${opt:-default}:/"
    [ $st = 0 ] && echo "$out" | tail -1 | grep -q " 0 DIFF;.* 0 missed$" || { echo "FAILED: p1run $opt $t"; fail=1; }
  done
done

step "the image record"
check "$p1/build/p1run" --image "$work/bind_walk.hol" bind_walk "$here/bind_walk_prog.txt" > /dev/null
check cmp "$work/bind_walk.hol" "$here/bind_walk.hol" &&
  echo "bind_walk.hol rebuilt from bind_walk_prog.txt byte for byte"

[ "$fail" = 0 ] && echo "check.sh: all passed" || echo "check.sh: FAILURES"
exit $fail

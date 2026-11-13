#!/usr/bin/env bash
# check.sh -- the checker slice, end to end.
#
#   check.sh WORKDIR [SEED] [RANDOM] [FLIPS]
#
# Writes the slice's program text and notes from slice.metta, generates the
# test streams with CeTTa's verdict on each (slice_tests.py), and runs every
# stream through the p1 reference evaluator and the native code (p1run), with
# default and with hoisted emission: each run must agree between the two,
# byte for byte, and end with CeTTa's verdict (or the checker's UNSUPPORTED
# where a stream leaves the slice first). Exit status 0 iff all pass.
set -u
here=$(cd "$(dirname "$0")" && pwd)
p1=$here/../p1
work=${1:?usage: check.sh WORKDIR [SEED] [RANDOM] [FLIPS]}
seed=${2:-7} nrandom=${3:-400} nflips=${4:-3000}
mkdir -p "$work"; work=$(cd "$work" && pwd)
make -s -C "$p1" || exit 2
rm -f "$work/slice.txt" "$work/slice.notes"
cetta --no-results "$here/slice.metta" "$work/slice.txt" "$work/slice.notes" || { echo "slice.metta failed"; exit 2; }
rm -rf "$work/streams-$seed"
python3 -I "$here/slice_tests.py" "$work/streams-$seed" "$seed" "$nrandom" "$nflips" || exit 2
fail=0
for opt in "" --hoist; do
  out=$("$p1/build/p1run" --quiet $opt "$work/slice.txt" "$work/streams-$seed/slice.p1t")
  echo "$out" | grep -v "^p1run" | head -20
  echo "$out" | tail -2
  echo "$out" | tail -1 | grep -q " 0 DIFF;.* 0 missed$" || fail=1
done
[ "$fail" = 0 ] && echo "check.sh: all passed" || echo "check.sh: FAILURES"
exit $fail

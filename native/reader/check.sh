#!/usr/bin/env bash
# check.sh -- the reader's primitives leb128 and fnv, end to end.
#
#   check.sh WORKDIR [SEED] [RANDOM]
#
# Into WORKDIR (never into this directory):
#  1. the programs' texts and notes from leb128.metta and fnv.metta, which
#     must equal leb128_prog.txt and fnv_prog.txt, the texts that are proved;
#  2. the oracle: CeTTa's cur_uv (hol_stream.c) and hk_fnv1a (hol_core.c),
#     extracted as text into cetta_oracle.h;
#  3. the tests (leb128_tests.c, fnv_tests.c), each run with CeTTa's verdict,
#     run by the p1 reference evaluator and the native code (p1run), with
#     default and with hoisted emission: every run must agree between the two
#     and meet its expectation;
#  4. the image records, which must equal leb128.hol and fnv.hol, the records
#     whose x86 bytes are proved.
# Exit status 0 iff every step passes.
set -u
here=$(cd "$(dirname "$0")" && pwd)
p1=$here/../p1
cetta=${CETTA_SRC:?set CETTA_SRC to a CeTTa source checkout}
work=${1:?usage: check.sh WORKDIR [SEED] [RANDOM]}
seed=${2:-7} nrandom=${3:-}
mkdir -p "$work"; work=$(cd "$work" && pwd)
fail=0
step() { echo "== $*"; }
check() { if "$@"; then :; else echo "FAILED: $*"; fail=1; fi; }

step "build the p1 tools"
make -s -C "$p1" || exit 2

step "programs from MeTTa"
for r in leb128 fnv; do
  rm -f "$work/$r.txt" "$work/$r.notes"
  check cetta --no-results "$here/$r.metta" "$work/$r.txt" "$work/$r.notes"
  check cmp "$work/$r.txt" "$here/${r}_prog.txt" && echo "$r.metta prints ${r}_prog.txt byte for byte"
done

step "the oracle: CeTTa's cur_uv and hk_fnv1a, as text"
hs=$cetta/native/hol_light/hol_stream.c hc=$cetta/native/hol_light/hol_core.c
{
  echo "/* Extracted by check.sh from $(basename "$hs") and $(basename "$hc"); do not edit. */"
  echo '#include "hol_kernel.h"'
  echo '#include <stdbool.h>'
  echo '#include <stdint.h>'
  echo '#include <stddef.h>'
  awk '/^typedef struct \{$/ { buf = $0; getline; if ($0 ~ /const uint8_t \*p, \*end;/) { print buf; on = 1 } }
       on { print } /^\} Cur;$/ { on = 0 }' "$hs"
  for f in 'static void cur_bad(' 'static void cur_short(' '#define HOLR_UV_LIMIT' 'static uint64_t cur_uv('; do
    awk -v f="$f" 'index($0, f) == 1 { on = 1 } on { print } on && (/^}$/ || f ~ /^#define/) { on = 0 }' "$hs"
  done
  awk 'index($0, "uint64_t hk_fnv1a(") == 1 { on = 1 } on { print } on && /^}$/ { on = 0 }' "$hc"
  echo '#define HOL_FNV_OFFSET 0xcbf29ce484222325ULL'
} > "$work/cetta_oracle.h"
for f in "typedef struct" "} Cur;" "static void cur_bad(" "static void cur_short(" "HOLR_UV_LIMIT" \
         "static uint64_t cur_uv(" "uint64_t hk_fnv1a("; do
  grep -qF "$f" "$work/cetta_oracle.h" || { echo "the oracle lacks: $f"; exit 2; }
done
grep -n "cur_uv\|hk_fnv1a" "$work/cetta_oracle.h" | head -3

step "tests, with CeTTa's verdicts"
for r in leb128 fnv; do
  gcc -O2 -Wall -Wextra -Werror -Wno-unused-function -I "$work" -I "$cetta/native/hol_light" "$here/${r}_tests.c" -o "$work/${r}_tests" ||
    { echo "cannot build ${r}_tests"; exit 2; }
  "$work/${r}_tests" "$work/$r.p1t" "$seed" $nrandom || { echo "${r}_tests failed"; fail=1; continue; }
  for opt in "" --hoist; do
    out=$("$p1/build/p1run" --quiet $opt "$here/${r}_prog.txt" "$work/$r.p1t"); st=$?
    echo "$out" | grep -v "^p1run" | head -20
    echo "$out" | grep "^p1run"
    [ $st = 0 ] && echo "$out" | tail -1 | grep -q " 0 DIFF;.* 0 missed$" || { echo "FAILED: p1run $opt $r"; fail=1; }
  done
done

step "image records"
for r in leb128 fnv; do
  check "$p1/build/p1run" --image "$work/$r.hol" "$r" "$here/${r}_prog.txt" > /dev/null
  check cmp "$work/$r.hol" "$here/$r.hol" && echo "$r.hol rebuilt from ${r}_prog.txt byte for byte"
done

[ "$fail" = 0 ] && echo "check.sh: all passed" || echo "check.sh: FAILURES"
exit $fail

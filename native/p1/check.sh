#!/usr/bin/env bash
# check.sh -- the p1 text tools, end to end.
#
#   check.sh WORKDIR
#
# Builds the tools, then into WORKDIR (never into tcalc/tisa):
#  1. t-ISA's own corpora: test_tisa (the 15 consumer programs, through
#     TISA_EXPORT_SEXPR) and test_tisa_ref's exports (random programs as
#     S-expressions, HOL checks, image records, hoisted image records);
#  2. the loader: its refusals, and the round trip of every corpus program
#     and of intern16b_prog.txt;
#  3. the harness: intern_p1.c's 24,000-run differential and its interning
#     check, for intern16 loaded from intern16b_prog.txt;
#  4. the MeTTa library: intern16 re-authored prints intern16b_prog.txt byte
#     for byte and passes the same tests; the library's printer and resolver
#     against tisa_print.c on the corpora; its refusals.
# Exit status 0 iff every step passes.
set -u
here=$(cd "$(dirname "$0")" && pwd)
tcalc=$(cd "$here/../.." && pwd)
work=${1:?usage: check.sh WORKDIR}
mkdir -p "$work/bin" "$work/corpus/run/tisa/manifests" "$work/tests" "$work/metta"
work=$(cd "$work" && pwd)
fail=0
step() { echo "== $*"; }
check() { if "$@"; then :; else echo "FAILED: $*"; fail=1; fi; }

step build
make -s -C "$here" || exit 2
(cd "$tcalc" &&
 gcc -O3 -march=native -fno-tree-vectorize -fno-tree-loop-distribute-patterns -flto -Wall -Wextra -Werror \
     tcalc.c tisa/tisa_core.c tisa/tisa_emit_x86.c tisa/tisa_specialize.c tisa/tisa_ref.c tisa/tisa_x86.c \
     tisa/tisa_print.c tisa/test_tisa.c tisa/native_alu.S compiled/ordinary_flat_cesta_runtime.o \
     -o "$work/bin/test_tisa" 2>/dev/null &&
 F="-std=gnu11 -O1 -g -Wall -Wextra -Werror -Itisa" &&
 gcc $F -DTISA_REF_P0_COMPAT -Dtisa_admit=tisa_admit_p0compat -Dtisa_run=tisa_run_p0compat \
     -Dtisa_entry_valid=tisa_entry_valid_p0compat -c tisa/tisa_ref.c -o "$work/bin/p0compat.o" &&
 gcc $F -DTISA_REF_CHECK_TYPES -Dtisa_admit=tisa_admit_checked -Dtisa_run=tisa_run_checked \
     -Dtisa_entry_valid=tisa_entry_valid_checked -c tisa/tisa_ref.c -o "$work/bin/checked.o" &&
 gcc $F tcalc.c tisa/tisa_core.c tisa/tisa_ref.c tisa/tisa_x86.c tisa/tisa_print.c "$work/bin/p0compat.o" \
     "$work/bin/checked.o" tisa/test_tisa_ref.c tisa/native_alu.S compiled/ordinary_flat_cesta_runtime.o \
     -o "$work/bin/test_tisa_ref") ||
  { echo "cannot build t-ISA's tests"; exit 2; }
rm -f "$work/bin/p0compat.o" "$work/bin/checked.o"

step "t-ISA corpora"
c=$work/corpus
cp "$tcalc"/tisa/manifests/*.json "$c/run/tisa/manifests/"
(cd "$c/run" && TISA_EXPORT_SEXPR="$c/consumers.sexpr" "$work/bin/test_tisa" > test_tisa.out) || { echo "test_tisa failed"; fail=1; }
tail -1 "$c/run/test_tisa.out"
(cd "$c/run" &&
 "$work/bin/test_tisa_ref" --export-sexpr "$c/random.sexpr" 4000 7 > /dev/null &&
 "$work/bin/test_tisa_ref" --export-hol "$c/random_check.hol" 2000 11 > /dev/null &&
 "$work/bin/test_tisa_ref" --export-images "$c/random_images.hol" 1000 13 > /dev/null &&
 "$work/bin/test_tisa_ref" --export-images "$c/hoist_images.hol" 300 17 --hoist > /dev/null) || { echo "test_tisa_ref exports failed"; fail=1; }

step "loader: refusals and round trip"
check "$here/build/p1_load_refusals"
check "$here/build/p1_roundtrip" "$tcalc/native/intern/intern16b_prog.txt" "$c/consumers.sexpr" "$c/consumers.sexpr.hol" \
      "$c/random.sexpr" "$c/random_check.hol" "$c/random_images.hol" "$c/hoist_images.hol"

step "harness: intern16 from its text"
gcc -O2 -Wall -Wextra -Werror "$here/tests/intern16_tests.c" -o "$work/bin/intern16_tests" &&
  "$work/bin/intern16_tests" "$work/tests/intern16_diff.p1t" "$work/tests/intern16_intern.p1t"
prog=$tcalc/native/intern/intern16b_prog.txt
check "$here/build/p1run" --quiet "$prog" "$work/tests/intern16_diff.p1t"
check "$here/build/p1run" --quiet --hoist "$prog" "$work/tests/intern16_diff.p1t"
check "$here/build/p1run" --quiet "$prog" "$work/tests/intern16_intern.p1t"
check "$here/build/p1run" --image "$work/tests/intern16.hol" intern16 "$prog" > /dev/null
check cmp "$work/tests/intern16.hol" "$tcalc/native/intern/intern16b.hol"

step "MeTTa: intern16 re-authored"
rm -f "$work/metta/intern16.txt" "$work/metta/intern16.notes"
check cetta --no-results "$here/intern16.metta" "$work/metta/intern16.txt" "$work/metta/intern16.notes"
check cmp "$work/metta/intern16.txt" "$prog" && echo "intern16.metta prints intern16b_prog.txt byte for byte"
check "$here/build/p1run" --quiet "$work/metta/intern16.txt" "$work/tests/intern16_diff.p1t"
check "$here/build/p1run" --quiet "$work/metta/intern16.txt" "$work/tests/intern16_intern.p1t"

step "MeTTa: printer and resolver against tisa_print.c"
for n in consumers random; do
  "$here/build/p1_text" --hol "$c/$n.sexpr" > "$c/$n.hol.lines"
  "$here/build/p1_text" --sexpr "$c/$n.sexpr" > "$c/$n.sexpr.lines"
  out=$(cetta --no-results "$here/tests/test_p1_text.metta" "$c/$n.sexpr.lines" "$c/$n.hol.lines")
  echo "$n: $(echo "$out" | tail -1)"
  echo "$out" | grep -q "different=0" || { echo "$out" | grep MISMATCH | head; fail=1; }
done

step "MeTTa: refusals"
check "$here/tests/test_p1_rejects.sh" "$work/rejects"

[ "$fail" = 0 ] && echo "check.sh: all passed" || echo "check.sh: FAILURES"
exit $fail

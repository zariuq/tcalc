#!/bin/bash
# run_driver_evidence.sh OUTDIR
#
# In a fresh HOL Light process (s2n-bignum's x86 model): the t-ISA prelude,
# the leaves' images (intern16b.hol, fnv.hol, leb128.hol, intern_name.hol)
# and their functional proofs, the driver proofs (driver_leaf.ml, driver.ml),
# the receipt bound (driver_fuel.ml), the record loop (records.ml), the
# intern16 and reader plans (drive_intern16.ml, drive_reader.ml) and the
# audit (driver_audit.ml). Then the differential harnesses, with the ISA
# features the harness binaries declare and the CET state of the run.
# OUTDIR must not exist; it receives input hashes, a copy of every source
# loaded (sources/), the HOL log, result.txt and harness.txt.
#
# Supported profile: user-mode shadow stacks (CET SHSTK) disabled. The
# driver and the record loop enter their callees with `call enter; enter:
# push r15; ret`, which faults under SHSTK; the x86 model has no shadow stack.
set -euo pipefail
out=$1
here=$(cd "$(dirname "$0")" && pwd)
export TCALC_DIR=$(cd "$here/../.." && pwd)
tisa=$(cd "$here/../../tisa/hol" && pwd)
nhol=$(cd "$here/../hol" && pwd)
intern=$(cd "$here/../intern" && pwd)
reader=$(cd "$here/../reader" && pwd)
names=$(cd "$here/../names" && pwd)
hol=${HOLDIR:?set HOLDIR to a HOL Light checkout}
s2n=${S2N:?set S2N to an s2n-bignum checkout}
[ -e "$out" ] && { echo "refusing to overwrite $out" >&2; exit 2; }
make -C "$here" all >/dev/null
files=("$tisa"/*.ml "$intern/intern16b.hol" "$intern/intern16_join.ml"
       "$nhol/intern16.ml" "$nhol/tisa_symex.ml" "$nhol/tisa_wp.ml" "$nhol/intern16_complete.ml"
       "$nhol/reader_common.ml" "$nhol/holr_bytes.ml" "$nhol/holr_leb.ml"
       "$nhol/reader_fnv.ml" "$nhol/reader_leb128.ml" "$nhol/intern_name.ml"
       "$reader/fnv.hol" "$reader/fnv_join.ml" "$reader/leb128.hol" "$reader/leb128_join.ml"
       "$names/intern_name.hol" "$names/intern_name_join.ml"
       "$here/driver_leaf.ml" "$here/driver.ml" "$here/driver_fuel.ml" "$here/records.ml"
       "$here/drive_intern16.ml" "$here/drive_reader.ml" "$here/driver_audit.ml"
       "$here/driver.S" "$here/build/driver.o" "$here/records.S" "$here/build/records.o"
       "$here/test_driver.c" "$here/test_records.c" "$here/cet_profile.h")
mkdir -p "$out/sources"; out=$(realpath "$out")
{
  sha256sum "${files[@]}"
  echo "hol-light $(git -C "$hol" rev-parse HEAD)"; echo "s2n-bignum $(git -C "$s2n" rev-parse HEAD)"
} > "$out/inputs.sha256"
cp "${files[@]}" "$out/sources/"
start=$(date +%s)
: > "$out/hol.log"; inode=$(stat -c %i "$out/hol.log")
cd "$s2n"
{
  for f in "$tisa/tisa_x86_evidence.ml" "$intern/intern16b.hol" "$intern/intern16_join.ml" \
           "$nhol/intern16_complete.ml" "$reader/fnv.hol" "$reader/fnv_join.ml" \
           "$reader/leb128.hol" "$reader/leb128_join.ml" "$names/intern_name.hol" \
           "$names/intern_name_join.ml" "$here/driver_leaf.ml" "$here/driver.ml" \
           "$here/driver_fuel.ml" "$here/records.ml" "$here/drive_intern16.ml" \
           "$here/drive_reader.ml" "$here/driver_audit.ml"; do
    printf 'loadt "%s";;\n' "$TCALC_DIR/native/hol/roots.ml"
    printf 'loadt "%s";;\n' "$f"
  done
} | LINE_EDITOR=env "$hol/hol.sh" > "$out/hol.log" 2>&1 || true
{
  grep -a -o 'IMAGE [A-Za-z_0-9]*: .*\|CALL [A-Za-z_0-9]*: .*\|ENTRY [A-Za-z_0-9]*: .*' "$out/hol.log" || true
  grep -a -o 'JOIN [A-Z_0-9]*: .*' "$out/hol.log" || true
  grep -a -o 'HYPS .*' "$out/hol.log" || true
  grep -a -A3 -o 'DRIVER AXIOMS .*' "$out/hol.log" | head -4 || true
  grep -a -o 'DRIVER AUDIT .*' "$out/hol.log" || true
  echo "load errors: $(grep -a -c 'Error in included file\|Exception: \|Sys_error' "$out/hol.log" || true)"
  echo "new_axiom, mk_thm or CHEAT_TAC in the driver's sources: $(cat "$here/driver_leaf.ml" "$here/driver.ml" "$here/driver_fuel.ml" "$here/records.ml" "$here/drive_intern16.ml" "$here/drive_reader.ml" | grep -c 'new_axiom\|mk_thm\|CHEAT_TAC' || true)"
  echo "seconds: $(( $(date +%s) - start ))"
  echo "log: inode $( [ "$(stat -c %i "$out/hol.log")" = "$inode" ] && echo unchanged || echo REPLACED), $(stat -c %s "$out/hol.log") bytes"
} > "$out/result.txt"
sha256sum "$out/hol.log" >> "$out/result.txt"
{
  echo "== supported profile: user-mode shadow stacks (CET SHSTK) disabled"
  for b in test_driver test_records; do
    echo "== $b: ISA properties it declares (readelf -n)"
    readelf -n "$here/build/$b" | grep -i 'x86 feature\|x86 ISA\|Properties' || echo "   (none)"
  done
  echo "== test_driver, 20000 plans, default seed"
  "$here/build/test_driver" "$intern/intern16b_prog.txt" "$here/build/driver.bin" || echo "EXIT $?"
  echo "== test_driver, 100000 plans, seed 0xC0FFEE"
  "$here/build/test_driver" "$intern/intern16b_prog.txt" "$here/build/driver.bin" 100000 0xC0FFEE | tail -3 || echo "EXIT $?"
  echo "== test_records, 20000 programs, default seed"
  "$here/build/test_records" "$intern/intern16b_prog.txt" "$reader/fnv_prog.txt" "$reader/leb128_prog.txt" \
    "$names/intern_name_prog.txt" "$here/build/driver.bin" "$here/build/records.bin" || echo "EXIT $?"
  echo "== test_records, 100000 programs, seed 0xC0FFEE"
  "$here/build/test_records" "$intern/intern16b_prog.txt" "$reader/fnv_prog.txt" "$reader/leb128_prog.txt" \
    "$names/intern_name_prog.txt" "$here/build/driver.bin" "$here/build/records.bin" 100000 0xC0FFEE | tail -4 || echo "EXIT $?"
} > "$out/harness.txt" 2>&1
cat "$out/result.txt"
grep -a 'cet:\|feature\|ISA\|random\|checks\|EXIT' "$out/harness.txt"

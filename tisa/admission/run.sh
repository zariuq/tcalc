#!/bin/sh
# Admission controls: sealed guards over spaces and protected value facts, in the tcalc kernel
# (admission_kernel) and in the hosted t-ISA (admission_tisa); tc_init's table reuse (tc_init_reuse,
# built with -DTC_INIT_VERIFY: an uncleared table aborts it); and the proved native producers
# (admission_native, and admission_native_patched with one byte of add64's .text copy changed), with
# the build check tisa/native_alu/check.sh, which must accept the real images and reject a wrong .bin
# and the patched binary. `make admission-check` builds them and runs this script; it prints every
# control that does not hold and one count line per program. Exit status: 0 all hold, 1 a control is
# violated, 2 a scene could not be set up or a program is missing.
here=$(cd "$(dirname "$0")" && pwd)
tree=$(cd "$here/../.." && pwd)
st=0
for p in admission_kernel admission_tisa tc_init_reuse admission_native admission_native_patched; do
  [ -x "$here/$p" ] || { echo "missing $here/$p (make admission-check builds it)"; exit 2; }
  out=$(cd "$tree" && "$here/$p" 2>&1); rc=$?
  printf '%s\n' "$out" | grep -E '^  (VIOLATED|NO SCENE)|not cleared' || true
  held=$(printf '%s\n' "$out" | grep -c '^  holds')
  case $rc in
    0) echo "$p: $held controls hold" ;;
    1|134) echo "$p: VIOLATED ($held hold)"; st=1 ;;
    *) echo "$p: no verdict (exit $rc, $held hold)"; [ $st -eq 0 ] && st=2 ;;
  esac
done
# the build check: the real images and a linked program pass; a wrong .bin and the patched program fail
check=$tree/tisa/native_alu/check.sh
held=0
if sh "$check" "$here/admission_native" > /dev/null; then held=$((held + 1)); else echo "  VIOLATED  check.sh refuses the real images or admission_native"; st=1; fi
if sh "$check" "$here/admission_native_patched" > /dev/null; then echo "  VIOLATED  check.sh accepts the patched add64 in admission_native_patched"; st=1; else held=$((held + 1)); fi
t=$(mktemp -d) || exit 2
cp "$tree"/tisa/native_alu/*.bin "$tree"/tisa/native_alu/SHA256SUMS "$check" "$t"/
printf '\001' | dd of="$t/sub64.bin" bs=1 seek=19 conv=notrunc 2> /dev/null   # sub64's opcode byte 29 (SUB) becomes 01 (ADD)
if sh "$t/check.sh" > /dev/null; then echo "  VIOLATED  check.sh accepts a sub64.bin whose SUB became ADD"; st=1; else held=$((held + 1)); fi
rm -rf "$t"
echo "native_alu build check: $held controls hold"
exit $st

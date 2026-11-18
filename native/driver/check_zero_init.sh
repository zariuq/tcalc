#!/usr/bin/env bash
# Native initialization-plan checks; proof qualification is a separate run
# of native/hol/check_file.py on zero_init_join.ml.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
work=${1:?usage: check_zero_init.sh WORKDIR}
mkdir -p "$work"
work=$(cd "$work" && pwd)
cc=${CC:-gcc}

"$cc" -c "$here/driver.S" -o "$work/driver.o"
objcopy -O binary --only-section=.text "$work/driver.o" "$work/driver.bin"
"$here/gen_image.sh" "$root/native/leaves/zero_words/zero_words.hol" tisa_leaf_zero_init > "$work/zero_image.S"
python3 - "$here/driver.ml" "$root/native/leaves/zero_words/zero_words.hol" "$work" <<'PY'
from pathlib import Path
import re,sys
driver,record,work = map(Path,sys.argv[1:])
source = re.search(r'let drv_mc = define_assert_from_elf.*?\[(.*?)\];;',driver.read_text(),re.S)[1]
source = re.sub(r'\(\*.*?\*\)','',source,flags=re.S)
expected = bytes(int(byte,16) for byte in re.findall(r'0x([0-9a-fA-F]{2})',source))
assert len(expected) == 522
assert (work/'driver.bin').read_bytes() == expected, 'driver bytes differ from drv_mc'
zero = bytes.fromhex(re.search(r'"([0-9a-f]{80,})"',record.read_text())[1])
assert len(zero) == 310
(work/'zero.bin').write_bytes(zero)
print('Driver bytes match drv_mc; initializer bytes extracted from its proof record.')
PY
"$cc" -std=gnu11 -O2 -g -D_GNU_SOURCE -Wall -Wextra -Werror \
  "$here/test_zero_init.c" "$work/driver.o" "$work/zero_image.S" -o "$work/test_zero_init"
"$work/test_zero_init" "$work/driver.bin" "$work/zero.bin" > "$work/positive.log" 2>&1
cat "$work/positive.log"
for mutation in --mutate-binding --shorten-range; do
  if "$work/test_zero_init" "$work/driver.bin" "$work/zero.bin" "$mutation" > "$work/$mutation.log" 2>&1; then
    echo "undetected mutation: $mutation" >&2
    exit 1
  else
    status=$?
    [ "$status" -eq 1 ] || { cat "$work/$mutation.log"; exit "$status"; }
  fi
  echo "detected $mutation"
done
# The alias mutation violates the theorem's read-only separation premise.
# It checks that the harness detects corruption, rather than testing a
# runtime layout validator.
for mode in --boot-views --boot-minimal --boot-unsupported --entry-views --entry-unsupported; do
  label=${mode#--}
  "$work/test_zero_init" "$work/driver.bin" "$work/zero.bin" "$mode" > "$work/$label.log" 2>&1
  cat "$work/$label.log"
  for mutation in --mutate-binding --shorten-range --alias-boot-constant; do
    if "$work/test_zero_init" "$work/driver.bin" "$work/zero.bin" "$mode" "$mutation" > "$work/$label$mutation.log" 2>&1; then
      echo "undetected $label mutation: $mutation" >&2
      exit 1
    else
      status=$?
      [ "$status" -eq 1 ] || { cat "$work/$label$mutation.log"; exit "$status"; }
    fi
    echo "detected $label $mutation"
  done
  case "$mode" in
    --entry-*)
      for mutation in --omit-hash-clear --omit-flags-clear; do
        if "$work/test_zero_init" "$work/driver.bin" "$work/zero.bin" "$mode" "$mutation" > "$work/$label$mutation.log" 2>&1; then
          echo "undetected $label mutation: $mutation" >&2
          exit 1
        else
          status=$?
          [ "$status" -eq 1 ] || { cat "$work/$label$mutation.log"; exit "$status"; }
        fi
        echo "detected $label $mutation"
      done
      ;;
  esac
done
echo "check_zero_init.sh: all passed"

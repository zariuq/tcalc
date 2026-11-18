#!/usr/bin/env bash
# Header plan data is exported from HEADER_PLAN_FIELDS by header_plan_export.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
work=${1:?usage: check_header.sh WORKDIR EXPORTED_FIELDS}
fields=${2:?usage: check_header.sh WORKDIR EXPORTED_FIELDS}
mkdir -p "$work"
work=$(cd "$work" && pwd)
fields=$(cd "$fields" && pwd)
cc=${CC:-gcc}

"$cc" -c "$here/driver.S" -o "$work/driver.o"
objcopy -O binary --only-section=.text "$work/driver.o" "$work/driver.bin"
for item in eqw:eqw pol_max:pol leb_next:leb const_next:const cur:cur inc:inc; do
  name=${item%%:*}; symbol=${item#*:}
  "$here/gen_image.sh" "$root/native/leaves/$name/$name.hol" "hdr_$symbol" > "$work/$name.S"
done
python3 - "$here/driver.ml" "$root/native/leaves" "$work" "$fields" <<'PY'
from pathlib import Path
import re,sys
driver,leaves,work,fields=map(Path,sys.argv[1:])
source=re.search(r'let drv_mc = define_assert_from_elf.*?\[(.*?)\];;',driver.read_text(),re.S)[1]
source=re.sub(r'\(\*.*?\*\)','',source,flags=re.S)
expected=bytes(int(byte,16) for byte in re.findall(r'0x([0-9a-fA-F]{2})',source))
assert len(expected)==522 and (work/'driver.bin').read_bytes()==expected
for name in ['eqw','pol_max','leb_next','const_next','cur','inc']:
    data=bytes.fromhex(re.search(r'"([0-9a-f]{80,})"',(leaves/name/(name+'.hol')).read_text())[1])
    (work/(name+'.bin')).write_bytes(data)
    print(name,len(data),'proof-image bytes')
rows=[list(map(int,line.split())) for line in (fields/'plan.words').read_text().splitlines()]
assert len(rows)==12 and all(len(row)==18 for row in rows)
assert all(row[0] in [3,20,26,31] and max(row[1:10])<=62 and max(row[10:])<32 for row in rows)
assert len((fields/'header.bytes').read_text().split())==39
print('Header exports:12 steps,39 constant bytes.')
PY
"$cc" -std=gnu11 -O2 -g -D_GNU_SOURCE -Wall -Wextra -Werror \
  -I"$root/tisa" -I"$root/native/p1" \
  "$here/test_header.c" "$root/native/p1/p1_load.c" "$root/tisa/tisa_ref.c" \
  "$root/tisa/tisa_x86.c" "$root/tisa/tisa_print.c" \
  "$work/driver.o" "$work/eqw.S" "$work/pol_max.S" "$work/leb_next.S" "$work/const_next.S" \
  "$work/cur.S" "$work/inc.S" \
  -o "$work/test_header"
"$work/test_header" "$work" "$fields/plan.words" "$fields/header.bytes" "$root/native/leaves" \
  > "$work/positive.log" 2>&1
cat "$work/positive.log"
for mutation in --early-policy --skip-publication --bypass-policy-guard; do
  if "$work/test_header" "$work" "$fields/plan.words" "$fields/header.bytes" "$root/native/leaves" \
       "$mutation" > "$work/$mutation.log" 2>&1; then
    echo "undetected mutation: $mutation" >&2
    exit 1
  else
    status=$?
    [ "$status" -eq 1 ] || { cat "$work/$mutation.log"; exit "$status"; }
  fi
  echo "detected $mutation"
done
grep -Eq 'failed-policy-changes [1-9][0-9]*' "$work/--early-policy.log"
echo "check_header.sh: all passed"

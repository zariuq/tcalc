#!/usr/bin/env bash
# Run the proved-image policy plan and check publication on every prefix.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
work=${1:?usage: check_policy.sh WORKDIR}
mkdir -p "$work"
work=$(cd "$work" && pwd)
cc=${CC:-gcc}

"$cc" -c "$here/driver.S" -o "$work/driver.o"
objcopy -O binary --only-section=.text "$work/driver.o" "$work/driver.bin"
"$here/gen_image.sh" "$root/native/leaves/pol_max/pol_max.hol" tisa_leaf_policy > "$work/policy.S"
"$here/gen_image.sh" "$root/native/leaves/eqw/eqw.hol" tisa_leaf_policy_copy > "$work/copy.S"
python3 - "$here/driver.ml" "$root/native/hol/policy_plan.ml" "$root/native/leaves" "$work" <<'PY'
from pathlib import Path
import ast,re,struct,sys
driver,policy,leaves,work=map(Path,sys.argv[1:])
source=re.search(r'let drv_mc = define_assert_from_elf.*?\[(.*?)\];;',driver.read_text(),re.S)[1]
source=re.sub(r'\(\*.*?\*\)','',source,flags=re.S)
expected=bytes(int(byte,16) for byte in re.findall(r'0x([0-9a-fA-F]{2})',source))
assert len(expected)==522 and (work/'driver.bin').read_bytes()==expected, 'driver bytes differ from drv_mc'
for name,target in [('pol_max','policy'),('eqw','copy')]:
    data=bytes.fromhex(re.search(r'"([0-9a-f]{80,})"',(leaves/name/(name+'.hol')).read_text())[1])
    (work/(target+'.bin')).write_bytes(data)
    print(target, len(data), 'proof-image bytes')
literal=re.search(r'MAP \(MAP val\) pl_plan_policy\s*=\s*(\[\[.*?\]\])',policy.read_text(),re.S)[1]
rows=ast.literal_eval(literal.replace(';',','))
assert len(rows)==2 and all(len(row)==18 for row in rows)
assert all(row[1:10]==[56]*9 and all(0<=value<32 for value in row[10:]) for row in rows)
(work/'plan.bin').write_bytes(b''.join(struct.pack('<Q',value) for row in rows for value in row))
print('Plan words extracted from POLICY_PLAN_FIELDS; formal qualification is a separate HOL run.')
PY
"$cc" -std=gnu11 -O2 -g -Wall -Wextra -Werror "$here/test_policy.c" \
  "$work/driver.o" "$work/policy.S" "$work/copy.S" -o "$work/test_policy"
"$work/test_policy" "$work/driver.bin" "$work/policy.bin" "$work/copy.bin" "$work/plan.bin" \
  > "$work/positive.log" 2>&1
cat "$work/positive.log"
for mutation in --early-commit --omit-publication --bypass-guard; do
  if "$work/test_policy" "$work/driver.bin" "$work/policy.bin" "$work/copy.bin" "$work/plan.bin" \
       "$mutation" > "$work/$mutation.log" 2>&1; then
    echo "undetected mutation: $mutation" >&2
    exit 1
  else
    status=$?
    [ "$status" -eq 1 ] || { cat "$work/$mutation.log"; exit "$status"; }
  fi
  echo "detected $mutation"
done
echo "check_policy.sh: all passed"

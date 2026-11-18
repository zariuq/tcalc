#!/usr/bin/env bash
# Native composition controls; HOL qualification loads control_init_driver_join.ml.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
work=${1:?usage: check_control_init.sh WORKDIR}
mkdir -p "$work"
work=$(cd "$work" && pwd)
cc=${CC:-gcc}
"$cc" -c "$here/driver.S" -o "$work/driver.o"
objcopy -O binary --only-section=.text "$work/driver.o" "$work/driver.bin"
"$here/gen_image.sh" "$root/native/leaves/control_init/control_init.hol" tisa_leaf_control_init > "$work/init.S"
"$here/gen_image.sh" "$root/native/leaves/zero_words/zero_words.hol" tisa_leaf_control_zero > "$work/zero.S"
python3 - "$here" "$root" "$work" <<'PY'
from pathlib import Path
import re,sys
here,root,work = map(Path,sys.argv[1:])
source = re.search(r'let drv_mc = define_assert_from_elf.*?\[(.*?)\];;', (here/'driver.ml').read_text(),re.S)[1]
source = re.sub(r'\(\*.*?\*\)','',source,flags=re.S)
expected = bytes(int(b,16) for b in re.findall(r'0x([0-9a-fA-F]{2})',source))
assert len(expected) == 522 and (work/'driver.bin').read_bytes() == expected
for name,label,size in [('control_init','init',1543),('zero_words','zero',310)]:
    text = (root/'native/leaves'/name/(name+'.hol')).read_text()
    data = bytes.fromhex(re.search(r'"([0-9a-f]{80,})"',text)[1])
    assert len(data) == size
    (work/(label+'.bin')).write_bytes(data)
header = []
for file,name,slot,label in [('control_init_driver','cinit',0,'control_init'),('zero_init','zinit',2,'control_zero')]:
    text = (root/'native/hol'/(file+'.ml')).read_text()
    literal = re.search(r'`'+name+r'_step slot\s*=\s*\[([^\]]+)\]',text,re.S)[1]
    tokens = [token.strip() for token in literal.split(';')]
    assert all(re.fullmatch(r'word (?:[0-9]+|slot)',token) for token in tokens)
    row = [slot if token == 'word slot' else int(token[5:]) for token in tokens]
    assert len(row) == 18
    if label == 'control_zero': row[0] = 1
    header.append('static const uint64_t '+label+'_step[18] = {'+','.join(map(str,row))+'};\n')
(work/'control_init_plan.h').write_text('#include <stdint.h>\n'+''.join(header))
print('Driver image matches its theorem; plan words and leaf bytes extracted from proof sources.')
PY
"$cc" -std=gnu11 -O2 -g -D_GNU_SOURCE -Wall -Wextra -Werror \
  -I"$root/tisa" -I"$root/native/p1" -I"$work" \
  "$here/test_control_init.c" "$root/native/p1/p1_load.c" "$root/tisa/tisa_ref.c" \
  "$root/tisa/tisa_print.c" "$work/driver.o" "$work/init.S" "$work/zero.S" \
  -o "$work/test_control_init"
args=("$work/driver.bin" "$work/init.bin" "$work/zero.bin" \
      "$root/native/leaves/control_init/control_init_prog.txt" "$root/native/leaves/zero_words/zero_words_prog.txt")
"$work/test_control_init" "${args[@]}" > "$work/positive.log" 2>&1
cat "$work/positive.log"
for mutation in --wrong-arg --payload-to-core --wrong-binding --reverse-order; do
  if "$work/test_control_init" "${args[@]}" "$mutation" > "$work/$mutation.log" 2>&1; then
    echo "undetected mutation: $mutation" >&2; exit 1
  else
    status=$?
    [ "$status" -eq 1 ] || { cat "$work/$mutation.log"; exit "$status"; }
  fi
  grep -Eq '[1-9][0-9]* failures;' "$work/$mutation.log"
  echo "detected $mutation"
done
echo "check_control_init.sh: all passed"

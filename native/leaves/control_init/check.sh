#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
work=${1:?usage: check.sh WORKDIR}
mkdir -p "$work"
work=$(cd "$work" && pwd)
cc=${CC:-gcc}
"$cc" -std=gnu11 -O2 -Wall -Wextra -Werror "$here/control_init_tests.c" -o "$work/control_init_tests"
"$work/control_init_tests" "$work/control_init.p1t"
"${TISA_CETTA:-cetta}" --no-results "$here/control_init.metta" "$work/control_init.txt" \
  "$work/control_init.notes" "$work/control_init_program.ml"
cmp "$work/control_init.txt" "$here/control_init_prog.txt"
cmp "$work/control_init_program.ml" "$here/control_init_program.ml"
make -s -C "$root/native/p1"
"$root/native/p1/build/p1run" --quiet --image "$work/control_init.hol" control_init \
  "$work/control_init.txt" "$work/control_init.p1t"
cmp "$work/control_init.hol" "$here/control_init.hol"
python3 - "$work/control_init.txt" "$work" <<'PY'
from pathlib import Path
import sys
source, work = map(Path, sys.argv[1:])
text = source.read_text()
mutations = {
    'policy-guard': ('(OpImm (word 2))', '(OpImm (word 3))'),
    'fnv-basis': ('14695981039346656037', '14695981039346656038'),
    'policy-slot': ('(TStore 8 0 1 (&56:int) 2)', '(TStore 8 0 1 (&64:int) 2)'),
    'extra-word': ('(TStore 8 0 1 (&184:int) 4)', '(TStore 8 0 1 (&192:int) 4)'),
}
for name, (before, after) in mutations.items():
    assert text.count(before) == 1, (name, 'ambiguous mutation')
    (work / (name + '.txt')).write_text(text.replace(before, after))
PY
for mutation in policy-guard fnv-basis policy-slot extra-word; do
  if "$root/native/p1/build/p1run" --quiet "$work/$mutation.txt" "$work/control_init.p1t" \
       > "$work/$mutation.log" 2>&1; then
    echo "undetected mutation: $mutation" >&2
    exit 1
  else
    status=$?
    [ "$status" -eq 1 ] || { cat "$work/$mutation.log"; exit "$status"; }
  fi
  grep -Eq 'expectations [0-9]+ checked, [1-9][0-9]* missed' "$work/$mutation.log"
  echo "detected $mutation"
done
echo "control_init: all passed"

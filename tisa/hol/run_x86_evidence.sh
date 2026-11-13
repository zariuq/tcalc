#!/bin/bash
# run_x86_evidence.sh SCRIPT OUTDIR [DRIVER]
#
# In a fresh HOL Light process, loads tisa_x86_evidence.ml, then SCRIPT (which
# names the images to prove, e.g. tisa_evidence_images on the v2 export), then
# DRIVER (controls, if any), and lists the axioms.
# OUTDIR must not exist; it receives input hashes, a copy of every HOL source
# loaded (sources/), the HOL log and result.txt.
set -euo pipefail
records=$(realpath "$1"); out=$2; driver=${3:-}
here=$(cd "$(dirname "$0")" && pwd)
export TCALC_DIR=$(cd "$here/../.." && pwd)
hol=${HOLDIR:?set HOLDIR to a HOL Light checkout}
s2n=${S2N:?set S2N to an s2n-bignum checkout}
[ -e "$out" ] && { echo "refusing to overwrite $out" >&2; exit 2; }
mkdir -p "$out"; out=$(realpath "$out")
{
  sha256sum "$here"/tisa_p1.ml "$here"/tisa_p1_memory.ml "$here"/tisa_p1_frame.ml \
            "$here"/tisa_x86_steps.ml "$here"/tisa_x86_rel.ml "$here"/tisa_x86_compose.ml \
            "$here"/tisa_x86_decide.ml "$here"/tisa_x86_templates.ml "$here"/tisa_x86_image.ml "$here"/tisa_p1_noninterference.ml \
            "$here"/tisa_x86_wrapper.ml "$here"/tisa_x86_loops.ml "$here"/tisa_x86_evidence.ml \
            "$here"/tisa_x86_hoist.ml "$here"/tisa_x86_hoist_fund.ml "$here"/tisa_x86_hoist_early.ml \
            "$here"/tisa_x86_hoist_early_fund.ml "$here"/tisa_x86_hoist_gen.ml "$records"
  [ -n "$driver" ] && sha256sum "$(realpath "$driver")"
  sha256sum "$here/../tisa_x86.c" "$here/../SEMANTICS.txt" "$here/../manifests/tisa_x86_p1_programs_v2.json" "$here"/tisa_x86_v2.ml
  echo "hol-light $(git -C "$hol" rev-parse HEAD)"; echo "s2n-bignum $(git -C "$s2n" rev-parse HEAD)"
} > "$out/inputs.sha256"
mkdir -p "$out/sources"
cp "$here"/tisa_p1.ml "$here"/tisa_p1_memory.ml "$here"/tisa_p1_frame.ml "$here"/tisa_x86_steps.ml \
   "$here"/tisa_x86_rel.ml "$here"/tisa_x86_compose.ml "$here"/tisa_x86_decide.ml "$here"/tisa_x86_templates.ml "$here"/tisa_x86_image.ml \
   "$here"/tisa_p1_noninterference.ml "$here"/tisa_x86_wrapper.ml "$here"/tisa_x86_v2.ml "$here"/tisa_x86_loops.ml \
   "$here"/tisa_x86_evidence.ml "$here"/tisa_x86_hoist.ml "$here"/tisa_x86_hoist_fund.ml \
   "$here"/tisa_x86_hoist_early.ml "$here"/tisa_x86_hoist_early_fund.ml "$here"/tisa_x86_hoist_gen.ml \
   "$records" "$out/sources/"
[ -n "$driver" ] && cp "$(realpath "$driver")" "$out/sources/"
start=$(date +%s)
: > "$out/hol.log"; inode=$(stat -c %i "$out/hol.log")
cd "$s2n"
{
  printf 'loadt "%s";;\n' "$TCALC_DIR/native/hol/roots.ml"
  printf 'loadt "%s";;\n' "$here/tisa_x86_evidence.ml"
  printf 'loadt "%s";;\n' "$records"
  [ -n "$driver" ] && printf 'loadt "%s";;\n' "$(realpath "$driver")"
  printf 'tisa_evidence_summary ();;\n'
} | LINE_EDITOR=env "$hol/hol.sh" > "$out/hol.log" 2>&1 || true
{
  grep -a -o 'IMAGE [A-Za-z_0-9]*: .*\|IMAGE [A-Za-z_0-9]* FAILED.*\|CALL [A-Za-z_0-9]*: .*\|ENTRY [A-Za-z_0-9]*: .*' "$out/hol.log" || true
  grep -a -o 'CONTROL .*' "$out/hol.log" || true
  grep -a -A6 -o 'AXIOMS .*' "$out/hol.log" | head -8 || true
  grep -a -o 'EVIDENCE .*' "$out/hol.log" | tail -1 || true
  echo "load errors: $(grep -a -c 'Error in included file\|^\(# *\)*Exception\|Sys_error' "$out/hol.log" || true)"
  echo "seconds: $(( $(date +%s) - start ))"
  echo "log: inode $( [ "$(stat -c %i "$out/hol.log")" = "$inode" ] && echo unchanged || echo REPLACED), $(stat -c %s "$out/hol.log") bytes"
} > "$out/result.txt"
sha256sum "$out/hol.log" >> "$out/result.txt"
cat "$out/result.txt"

#!/bin/bash
# audit_hbind.sh OUTDIR
#
# The fresh-process audit of tcalc/native/hol/bind_walk_hbind.ml (the hbind
# row of bind_walk's result): in a new HOL Light process (run from
# s2n-bignum), loads the file, prints the theorem with its hypothesis count
# and lists the axioms. OUTDIR must not exist; it receives input hashes, the
# HOL log and result.txt.
set -euo pipefail
out=${1:?usage: audit_hbind.sh OUTDIR}
here=$(cd "$(dirname "$0")" && pwd)
export TCALC_DIR=$(cd "$here/../.." && pwd)
hol=${HOLDIR:?set HOLDIR to a HOL Light checkout}
s2n=${S2N:?set S2N to an s2n-bignum checkout}
nhol=$(cd "$here/../hol" && pwd)
[ -e "$out" ] && { echo "refusing to overwrite $out" >&2; exit 2; }
mkdir -p "$out"; out=$(realpath "$out")
{
  sha256sum "$nhol/bind_walk_hbind.ml" "$nhol/bind_walk.ml" "$nhol/holfibre_rows.ml"
  echo "hol-light $(git -C "$hol" rev-parse HEAD)"; echo "s2n-bignum $(git -C "$s2n" rev-parse HEAD)"
} > "$out/inputs.sha256"
start=$(date +%s)
cd "$s2n"
{
  printf 'loadt "%s";;\n' "$TCALC_DIR/native/hol/roots.ml"
  printf 'loadt "%s";;\n' "$nhol/bind_walk_hbind.ml"
  printf 'print_endline "AUDIT DONE";;\n'
} | LINE_EDITOR=env "$hol/hol.sh" > "$out/hol.log" 2>&1 || true
{
  echo "routine: bind_walk (hbind row)"
  grep -a -o 'AUDIT BIND_WALK_HBIND: [0-9]* hyps' "$out/hol.log" || echo "BIND_WALK_HBIND NOT PROVED"
  grep -a -o 'AXIOMS [0-9]*' "$out/hol.log" | tail -1 || true
  grep -a -o 'AUDIT DONE' "$out/hol.log" || echo "AUDIT NOT DONE"
  echo "load errors: $(grep -a -c 'Error in included file\|^\(# *\)*Exception\|Sys_error\|^Error' "$out/hol.log" || true)"
  echo "new_axiom, mk_thm, CHEAT_TAC in the file: $(grep -c 'new_axiom\|mk_thm\|CHEAT_TAC' "$nhol/bind_walk_hbind.ml" || true)"
  echo "seconds: $(( $(date +%s) - start ))"
} > "$out/result.txt"
sha256sum "$out/hol.log" >> "$out/result.txt"
grep -a -A12 'THEOREM BIND_WALK_HBIND' "$out/hol.log" > "$out/theorem.txt" || true
cat "$out/result.txt"

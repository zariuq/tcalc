#!/bin/bash
# audit.sh OUTDIR
#
# The fresh-process audit of bind_walk's functional proof: in a new HOL Light
# process (run from s2n-bignum, whose x86 base t-ISA's semantics loads), loads
# tcalc/native/hol/bind_walk.ml, lists every theorem it states with its
# hypothesis count, prints the main theorems, and lists the axioms.
# OUTDIR must not exist; it receives input hashes, the HOL log and result.txt
# (load errors, hypothesis counts, axioms, a scan of the sources).
set -euo pipefail
out=${1:?usage: audit.sh OUTDIR}
here=$(cd "$(dirname "$0")" && pwd)
export TCALC_DIR=$(cd "$here/../.." && pwd)
hol=${HOLDIR:?set HOLDIR to a HOL Light checkout}
s2n=${S2N:?set S2N to an s2n-bignum checkout}
nhol=$(cd "$here/../hol" && pwd)
tisa=$(cd "$here/../../tisa/hol" && pwd)
hih=${METTAPEDIA_HOL_LIGHT:?set METTAPEDIA_HOL_LIGHT to the hol_light directory of Mettapedia}/HolInHol
# the main theorems (every theorem the file states is in its bw_theorems)
main="BW_RUN BIND_WALK_SOUND BIND_WALK_CANONICAL BW_CTX_SATISFIABLE"
nthms=$(sed -n '/^let bw_theorems = ref \[/,/^\];;/p' "$nhol/bind_walk.ml" | grep -c '", ')
[ -e "$out" ] && { echo "refusing to overwrite $out" >&2; exit 2; }
mkdir -p "$out"; out=$(realpath "$out")
srcs="$nhol/bind_walk.ml $nhol/intern16_complete.ml $nhol/intern16.ml $nhol/tisa_wp.ml $nhol/tisa_symex.ml
      $nhol/holfibre_rows.ml $hih/syntax.ml $hih/dbterm.ml"
{
  sha256sum $srcs "$tisa/tisa_p1.ml" "$tisa/tisa_p1_memory.ml" "$tisa/tisa_p1_frame.ml" \
            "$here/bind_walk_prog.txt"
  echo "hol-light $(git -C "$hol" rev-parse HEAD)"; echo "s2n-bignum $(git -C "$s2n" rev-parse HEAD)"
} > "$out/inputs.sha256"
start=$(date +%s)
cd "$s2n"
{
  printf 'loadt "%s";;\n' "$TCALC_DIR/native/hol/roots.ml"
  printf 'loadt "%s";;\n' "$nhol/bind_walk.ml"
  printf 'List.iter (fun (n,th) -> Printf.printf "AUDIT %%s: %%d hyps\\n%%!" n (length(hyp th))) !bw_theorems;;\n'
  for t in $main; do printf 'print_endline ("THEOREM %s: " ^ string_of_thm %s);;\n' "$t" "$t"; done
  printf 'let ax = axioms() in Printf.printf "AXIOMS %%d:\\n%%!" (length ax); List.iter (fun th -> Printf.printf "  %%s\\n%%!" (string_of_term (concl th))) ax;;\n'
  printf 'print_endline "AUDIT DONE";;\n'
} | LINE_EDITOR=env "$hol/hol.sh" > "$out/hol.log" 2>&1 || true
{
  echo "routine: bind_walk"
  grep -a -o 'AUDIT [A-Za-z_0-9]*: [0-9]* hyps' "$out/hol.log" || true
  echo "theorems audited: $(grep -a -c 'AUDIT [A-Za-z_0-9]*: [0-9]* hyps' "$out/hol.log" || true) of $nthms"
  echo "with hypotheses: $(grep -a 'AUDIT [A-Za-z_0-9]*: [0-9]* hyps' "$out/hol.log" | grep -v ': 0 hyps' | wc -l)"
  grep -a -A4 -o 'AXIOMS .*' "$out/hol.log" | head -5 || true
  grep -a -o 'AUDIT DONE' "$out/hol.log" || echo "AUDIT NOT DONE"
  echo "load errors: $(grep -a -c 'Error in included file\|^\(# *\)*Exception\|Sys_error\|^Error' "$out/hol.log" || true)"
  echo "new_axiom, mk_thm, CHEAT_TAC in the sources: $(cat $srcs | grep -c 'new_axiom\|mk_thm\|CHEAT_TAC' || true)"
  echo "seconds: $(( $(date +%s) - start ))"
} > "$out/result.txt"
sha256sum "$out/hol.log" >> "$out/result.txt"
grep -a 'THEOREM ' "$out/hol.log" > "$out/theorems.txt" || true
cat "$out/result.txt"

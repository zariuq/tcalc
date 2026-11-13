#!/bin/bash
# audit.sh ROUTINE OUTDIR
#
# The fresh-process audit of a reader routine's functional proof: in a new
# HOL Light process (run from s2n-bignum, whose x86 base t-ISA's semantics
# loads), loads tcalc/native/hol/reader_ROUTINE.ml, lists every theorem the
# routine states with its hypothesis count, and lists the axioms.
# ROUTINE is leb128 or fnv. OUTDIR must not exist; it receives input hashes,
# the HOL log and result.txt (load errors, hypothesis counts, axioms).
set -euo pipefail
routine=${1:?usage: audit.sh ROUTINE OUTDIR}; out=${2:?usage: audit.sh ROUTINE OUTDIR}
here=$(cd "$(dirname "$0")" && pwd)
export TCALC_DIR=$(cd "$here/../.." && pwd)
hol=${HOLDIR:?set HOLDIR to a HOL Light checkout}
s2n=${S2N:?set S2N to an s2n-bignum checkout}
nhol=$(cd "$here/../hol" && pwd)
tisa=$(cd "$here/../../tisa/hol" && pwd)
case $routine in
  leb128) thms="LEB_DEC_ENC LEB_ENC_INJ LEB_ENC_LENGTH_62 LEB_ENC_BYTES LEB_ENC_SEQ LEB_PREFIX_SCAN
                LEB_SEQ_FIRES LEB_SEQ_SHORT LEB_SEQ_NONMINIMAL LEB_SEQ_TOO_BIG LEB_SEQ_NINE
                LEB_FIRES_UNIQUE LEB_FIRES_NOT_SHORT REGION_FROM_SPLIT LEB128_TERM LEB128_ENTRY
                LEB128_BODY_WP LEB128_PROLOGUE_WP LEB128_ROOT_WP LEB128_RUN LEB128_SOUND
                LEB128_COMPLETE LEB128_SHORT LEB128_MALFORMED"
          main="LEB128_RUN LEB128_SOUND LEB128_COMPLETE LEB128_SHORT LEB128_MALFORMED" ;;
  fnv)    thms="FNV1A_APPEND FNV1A_SEQ_SUC FNV_TERM FNV_ENTRY FNV_BODY_WP FNV_PROLOGUE_WP
                FNV_ROOT_WP FNV_RUN FNV_SOUND FNV_COMPLETE FNV_REFUSED"
          main="FNV_RUN FNV_SOUND FNV_COMPLETE FNV_REFUSED" ;;
  *) echo "audit.sh: ROUTINE is leb128 or fnv" >&2; exit 2 ;;
esac
[ -e "$out" ] && { echo "refusing to overwrite $out" >&2; exit 2; }
mkdir -p "$out"; out=$(realpath "$out")
{
  sha256sum "$nhol/reader_$routine.ml" "$nhol/reader_common.ml" "$nhol/holr_bytes.ml" \
            "$nhol/holr_leb.ml" "$nhol/tisa_wp.ml" "$nhol/tisa_symex.ml" \
            "$tisa/tisa_p1.ml" "$tisa/tisa_p1_memory.ml" "$tisa/tisa_p1_frame.ml" \
            "$here/${routine}_prog.txt"
  echo "hol-light $(git -C "$hol" rev-parse HEAD)"; echo "s2n-bignum $(git -C "$s2n" rev-parse HEAD)"
} > "$out/inputs.sha256"
start=$(date +%s)
cd "$s2n"
{
  printf 'loadt "%s";;\n' "$TCALC_DIR/native/hol/roots.ml"
  printf 'loadt "%s";;\n' "$nhol/reader_$routine.ml"
  for t in $thms; do printf 'Printf.printf "AUDIT %s: %%d hyps\\n%%!" (length(hyp %s));;\n' "$t" "$t"; done
  for t in $main; do printf 'print_endline ("THEOREM %s: " ^ string_of_thm %s);;\n' "$t" "$t"; done
  printf 'let ax = axioms() in Printf.printf "AXIOMS %%d:\\n%%!" (length ax); List.iter (fun th -> Printf.printf "  %%s\\n%%!" (string_of_term (concl th))) ax;;\n'
  printf 'print_endline "AUDIT DONE";;\n'
} | LINE_EDITOR=env "$hol/hol.sh" > "$out/hol.log" 2>&1 || true
{
  echo "routine: $routine"
  grep -a -o 'AUDIT [A-Za-z_0-9]*: [0-9]* hyps' "$out/hol.log" || true
  echo "theorems audited: $(grep -a -c 'AUDIT [A-Za-z_0-9]*: [0-9]* hyps' "$out/hol.log" || true) of $(echo $thms | wc -w)"
  echo "with hypotheses: $(grep -a 'AUDIT [A-Za-z_0-9]*: [0-9]* hyps' "$out/hol.log" | grep -v ': 0 hyps' | wc -l)"
  grep -a -A4 -o 'AXIOMS .*' "$out/hol.log" | head -5 || true
  grep -a -o 'AUDIT DONE' "$out/hol.log" || echo "AUDIT NOT DONE"
  echo "load errors: $(grep -a -c 'Error in included file\|^\(# *\)*Exception\|Sys_error\|^Error' "$out/hol.log" || true)"
  echo "new_axiom, mk_thm, CHEAT_TAC in the sources: $(grep -c 'new_axiom\|mk_thm\|CHEAT_TAC' "$nhol/reader_$routine.ml" "$nhol/reader_common.ml" "$nhol/holr_bytes.ml" "$nhol/holr_leb.ml" "$nhol/tisa_wp.ml" | awk -F: '{s+=$2} END {print s}')"
  echo "seconds: $(( $(date +%s) - start ))"
} > "$out/result.txt"
sha256sum "$out/hol.log" >> "$out/result.txt"
cat "$out/result.txt"

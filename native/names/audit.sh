#!/bin/bash
# audit.sh OUTDIR
#
# The fresh-process audit of intern_name's functional proof: in a new HOL
# Light process (run from s2n-bignum, whose x86 base t-ISA's semantics loads),
# loads tcalc/native/hol/intern_name.ml, lists every theorem it states with its
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
thms="INTERN_NAME_TERM NAME_POS_LT NAME_WORD_SUC_NZ NAME_WORD_SUC_PRED NAME_SLOTS_VAL
      NAME_ROW_BYTES_TRANSFER NAME_LIST_OF_SEQ_EQ NAME_OK_TRANSFER NAME_APPENDED_ROW
      NAME_APPENDED_OLD_ROWS NAME_OK_APPEND NAME_ENTRY NAME_REGION_WORD_VAL NAME_FINST_READ
      NAME_FINST_VIEW NAME_OK_FINST TISA_STATE_CASES TISA_STATE_EQ NAME_CMP_BODY_WP NAME_CMP_LOOP
      NAME_WRITE_COPY_STEP NAME_COPY_BODY_WP NAME_COPY_LOOP NAME_FINST_MEM NAME_STOP_RESULT
      NAME_EARLY_STOP_RESULT NAME_FOUND_RESULT NAME_APPEND_RESULT NAME_WORD_SHL NAME_ROW_KEY
      TISA_FAILST_FINST NAME_PROBED_STEP NAME_OCCUPIED_WP NAME_APPEND_WP NAME_BODY_WP
      NAME_PROLOGUE_WP NAME_ROOT_WP NAME_RUN NAME_SOUND NAME_RUN_COMPLETE NAME_APPEND_ABSENT
      NAME_PRESENT_FOUND"
main="NAME_RUN NAME_SOUND NAME_RUN_COMPLETE NAME_APPEND_ABSENT NAME_PRESENT_FOUND"
[ -e "$out" ] && { echo "refusing to overwrite $out" >&2; exit 2; }
mkdir -p "$out"; out=$(realpath "$out")
srcs="$nhol/intern_name.ml $nhol/reader_common.ml $nhol/holr_bytes.ml $nhol/tisa_wp.ml $nhol/tisa_symex.ml"
{
  sha256sum $srcs "$tisa/tisa_p1.ml" "$tisa/tisa_p1_memory.ml" "$tisa/tisa_p1_frame.ml" \
            "$here/intern_name_prog.txt"
  echo "hol-light $(git -C "$hol" rev-parse HEAD)"; echo "s2n-bignum $(git -C "$s2n" rev-parse HEAD)"
} > "$out/inputs.sha256"
start=$(date +%s)
cd "$s2n"
{
  printf 'loadt "%s";;\n' "$TCALC_DIR/native/hol/roots.ml"
  printf 'loadt "%s";;\n' "$nhol/intern_name.ml"
  for t in $thms; do printf 'Printf.printf "AUDIT %s: %%d hyps\\n%%!" (length(hyp %s));;\n' "$t" "$t"; done
  for t in $main; do printf 'print_endline ("THEOREM %s: " ^ string_of_thm %s);;\n' "$t" "$t"; done
  printf 'let ax = axioms() in Printf.printf "AXIOMS %%d:\\n%%!" (length ax); List.iter (fun th -> Printf.printf "  %%s\\n%%!" (string_of_term (concl th))) ax;;\n'
  printf 'print_endline "AUDIT DONE";;\n'
} | LINE_EDITOR=env "$hol/hol.sh" > "$out/hol.log" 2>&1 || true
{
  echo "routine: intern_name"
  grep -a -o 'AUDIT [A-Za-z_0-9]*: [0-9]* hyps' "$out/hol.log" || true
  echo "theorems audited: $(grep -a -c 'AUDIT [A-Za-z_0-9]*: [0-9]* hyps' "$out/hol.log" || true) of $(echo $thms | wc -w)"
  echo "with hypotheses: $(grep -a 'AUDIT [A-Za-z_0-9]*: [0-9]* hyps' "$out/hol.log" | grep -v ': 0 hyps' | wc -l)"
  grep -a -A4 -o 'AXIOMS .*' "$out/hol.log" | head -5 || true
  grep -a -o 'AUDIT DONE' "$out/hol.log" || echo "AUDIT NOT DONE"
  echo "load errors: $(grep -a -c 'Error in included file\|^\(# *\)*Exception\|Sys_error\|^Error' "$out/hol.log" || true)"
  echo "new_axiom, mk_thm, CHEAT_TAC in the sources: $(cat $srcs | grep -c 'new_axiom\|mk_thm\|CHEAT_TAC' || true)"
  echo "seconds: $(( $(date +%s) - start ))"
} > "$out/result.txt"
sha256sum "$out/hol.log" >> "$out/result.txt"
cat "$out/result.txt"

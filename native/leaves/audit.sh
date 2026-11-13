#!/bin/bash
# audit.sh OUTDIR
#
# The fresh-process audit of the plan leaves' functional proofs against their
# specifications (tcalc/native/hol/plans_leaves.ml). In a new HOL Light
# process on s2n-bignum's base it loads the t-ISA, driver and interner files
# the leaves need; the fibre's row decoders (holfibre_rows.ml, with HolInHol's
# syntax.ml and dbterm.ml), which plans_leaves.ml's walk specifications name;
# the three definitions plans_leaves.ml takes from plans_abs.ml (pl_ids,
# pl_tyids, pl_cells_new), extracted verbatim from plans_abs.ml into OUTDIR
# (a session that also loads plans_abs.ml takes them as benign
# redefinitions); plans_leaves.ml itself; every leaf's proof and
# leaves_spec.ml. It lists every theorem with its hypothesis count, prints
# the PL_*_SPEC and run statements, lists the axioms, and runs the evidence
# gate (every loaded file with its digest), which evidence_check.py checks
# against the files on disk. OUTDIR must not exist; it receives input
# hashes, the extracted definitions, the HOL log and result.txt.
#
# (The Model world, which loads all of plans_abs.ml, is not needed: the
# leaves' specifications use only these three of its definitions.)
set -euo pipefail
out=${1:?usage: audit.sh OUTDIR}
here=$(cd "$(dirname "$0")" && pwd)
export TCALC_DIR=$(cd "$here/../.." && pwd)
hol=${HOLDIR:?set HOLDIR to a HOL Light checkout}
s2n=${S2N:?set S2N to an s2n-bignum checkout}
nhol=$(cd "$here/../hol" && pwd)
drv=$(cd "$here/../driver" && pwd)
leaves="pack unpack eqw row_word live append_row put_word"
[ -e "$out" ] && { echo "refusing to overwrite $out" >&2; exit 2; }
mkdir -p "$out"; out=$(realpath "$out")
python3 -I - "$nhol/plans_abs.ml" "$out/plans_abs_defs.ml" <<'PYEOF'
import re, sys
s = open(sys.argv[1]).read()
out = ["(* Extracted verbatim from plans_abs.ml by leaves/audit.sh. *)\n"]
for name in ["pl_ids", "pl_tyids", "pl_cells_new"]:
    m = re.search(r"^let %s = (?:define|new_definition)\n.*?;;\n" % name, s, flags=re.S | re.M)
    if not m: sys.exit("audit.sh: no %s in plans_abs.ml" % name)
    out.append(m.group(0))
open(sys.argv[2], "w").write("\n".join(out))
PYEOF
srcs="$here/common/leaf_lib.ml $here/leaves_spec.ml"
for l in $leaves; do srcs="$srcs $here/$l/$l.ml"; done
{
  sha256sum $srcs "$nhol/plans_leaves.ml" "$nhol/plans_abs.ml" "$out/plans_abs_defs.ml" \
            "$nhol/holfibre_rows.ml" "$nhol/tisa_wp.ml" "$nhol/tisa_symex.ml" "$nhol/intern16.ml" \
            "$nhol/intern16_complete.ml" "$drv/driver_leaf.ml"
  for l in $leaves; do sha256sum "$here/$l/${l}_prog.txt"; done
  echo "hol-light $(git -C "$hol" rev-parse HEAD)"; echo "s2n-bignum $(git -C "$s2n" rev-parse HEAD)"
} > "$out/inputs.sha256"
start=$(date +%s)
cd "$s2n"
{
  printf 'loadt "%s";;\n' "$TCALC_DIR/native/hol/roots.ml"
  printf 'loadt "%s";;\n' "$drv/driver_leaf.ml"
  printf 'loadt "%s";;\n' "$nhol/intern16_complete.ml"
  printf 'loadt "%s";;\n' "$nhol/tisa_wp.ml"
  printf 'loadt "%s";;\n' "$nhol/holfibre_rows.ml"
  printf 'loadt "%s";;\n' "$out/plans_abs_defs.ml"
  printf 'loadt "%s";;\n' "$nhol/plans_leaves.ml"
  printf 'loadt "%s";;\n' "$here/leaves_spec.ml"
  printf 'let leaves_all = leaf_lib_theorems @ pack_theorems @ unpack_theorems @ eqw_theorems @ row_word_theorems @ live_theorems @ append_row_theorems @ put_word_theorems @ leaves_spec_theorems;;\n'
  printf 'List.iter (fun (n,th) -> Printf.printf "AUDIT %%s: %%d hyps\\n%%!" n (length(hyp th))) leaves_all;;\n'
  printf 'Printf.printf "AUDIT theorems %%d, with hypotheses %%d\\n%%!" (length leaves_all) (length (filter (fun (_,th) -> hyp th <> []) leaves_all));;\n'
  for t in PL_PACK_SPEC PL_UNPACK_SPEC PL_EQW_SPEC PL_ROW_WORD_SPEC PL_LIVE_SPEC PL_APPEND_ROW_SPEC PL_PUT_WORD_SPEC; do
    printf 'print_endline ("THEOREM %s: " ^ string_of_thm %s);;\n' "$t" "$t"
  done
  printf 'let ax = axioms() in Printf.printf "AXIOMS %%d:\\n%%!" (length ax); List.iter (fun th -> Printf.printf "  %%s\\n%%!" (string_of_term (concl th))) ax;;\n'
  printf 'loadt "%s";;\n' "$nhol/evidence_gate.ml"
  printf 'print_endline "AUDIT DONE";;\n'
} | LINE_EDITOR=env "$hol/hol.sh" > "$out/hol.log" 2>&1 || true
{
  echo "leaves: $leaves"
  grep -a -o 'AUDIT [A-Za-z_0-9]*: [0-9]* hyps' "$out/hol.log" || true
  grep -a -o 'AUDIT theorems .*' "$out/hol.log" || true
  echo "with hypotheses (lines): $(grep -a 'AUDIT [A-Za-z_0-9]*: [0-9]* hyps' "$out/hol.log" | grep -v ': 0 hyps' | wc -l)"
  grep -a -A4 -o 'AXIOMS .*' "$out/hol.log" | head -5 || true
  grep -a -o 'AUDIT DONE' "$out/hol.log" || echo "AUDIT NOT DONE"
  echo "load errors: $(grep -a -c 'Error in included file\|^\(# *\)*Exception\|Sys_error\|^Error' "$out/hol.log" || true)"
  echo "new_axiom, mk_thm, CHEAT_TAC in the leaves' sources: $(cat $srcs | grep -c 'new_axiom\|mk_thm\|CHEAT_TAC' || true)"
  python3 -I "$nhol/evidence_check.py" "$out/hol.log" > "$out/evidence-check.txt" 2>&1 && ev=ok || ev=FAILED
  echo "evidence check: $ev; $(tail -1 "$out/evidence-check.txt")"
  echo "seconds: $(( $(date +%s) - start ))"
} > "$out/result.txt"
sha256sum "$out/hol.log" >> "$out/result.txt"
grep -a 'THEOREM ' "$out/hol.log" > "$out/theorems.txt" || true
cat "$out/result.txt"

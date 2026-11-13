#!/bin/sh
# Check the machine-code proofs of the compiled leaves with HOL Light, on the x86-64
# model of s2n-bignum, against the leaf objects in the parent directory.
#   HOLDIR: HOL Light, built with HOLLIGHT_USE_MODULE=1
#   S2N:    an s2n-bignum checkout
# The run ends with check_axioms, which fails if any axiom beyond HOL Light's three
# basic ones was added.
set -e
here=$(cd "$(dirname "$0")" && pwd)
HOLDIR=${HOLDIR:-$here/../../../../repos/hol-light}
S2N=${S2N:-$here/../../../../repos/s2n-bignum}
HOLDIR=$(cd "$HOLDIR" && pwd)
S2N=$(cd "$S2N" && pwd)
export HOLLIGHT_DIR="$HOLDIR"
out="$here/../build-proof"
mkdir -p "$out"

for leaf in mm_sub1_leaf flat_fire; do
  obj="$here/../$leaf.o"
  if [ "$leaf" = flat_fire ]; then
    obj="$out/$leaf.o"
    as --64 "$here/../flat_fire.S" -o "$obj"
  fi
  tmpl="$out/$leaf.check.ml"
  {
    echo "let ${leaf}_object = \"$obj\";;"
    echo "loadt \"$(realpath --relative-to="$S2N" "$here/$leaf.ml")\";;"
    echo "check_axioms ();;"
    for thm in $(grep -o '^let [A-Z0-9_]* = prove' "$here/$leaf.ml" | awk '{print $2}' | grep 'INSIDE\|OUTSIDE'); do
      echo "Printf.printf \"val $thm : thm = %s\\n\" (string_of_thm $thm);;"
    done
    if [ "$leaf" = flat_fire ]; then
      echo "Printf.printf \"val FLAT_FIRE_CORRECT : thm = %s\\n\" (string_of_thm FLAT_FIRE_CORRECT);;"
    fi
  } > "$tmpl"
  cd "$S2N"
  ocaml "$HOLDIR/inline_load.ml" "$tmpl" "$out/$leaf.inlined.ml"
  OCAMLRUNPARAM=l=2000000000 ocamlopt.byte -pp "$("$HOLDIR/hol.sh" -pp)" -I "$HOLDIR" -I +unix \
    -c hol_lib.cmxa "$out/$leaf.inlined.ml" -o "$out/$leaf.inlined.cmx" -w -a
  ocamlfind ocamlopt -package zarith,unix -linkpkg hol_lib.cmxa -I "$HOLDIR" \
    "$out/$leaf.inlined.cmx" -o "$out/$leaf.native"
  "$out/$leaf.native" > "$out/$leaf.correct" 2>&1 || { tail -20 "$out/$leaf.correct"; echo "$leaf: proof run failed"; exit 1; }
  if grep -i 'error:\|exception:' "$out/$leaf.correct"; then echo "$leaf: proof failed"; exit 1; fi
  case "$leaf" in
    mm_sub1_leaf)
      grep -c '^val MM_' "$out/$leaf.correct" | grep -q '^2$' || { echo "$leaf: theorems missing"; exit 1; }
      ;;
    flat_fire)
      grep -c '^val FLAT_FIRE_CORRECT ' "$out/$leaf.correct" | grep -q '^1$' || { echo "$leaf: final theorem missing"; exit 1; }
      ;;
  esac
  echo "$leaf: proved, no new axioms"
  cd "$here"
done

leaf=ordinary_flat
tmpl="$out/$leaf.check.ml"
{
  echo "let flat_fire_object = \"$out/flat_fire.o\";;"
  echo "loadt \"$(realpath --relative-to="$S2N" "$here/flat_fire.ml")\";;"
  echo "loadt \"$(realpath --relative-to="$S2N" "$here/ordinary_flat.ml")\";;"
  echo "check_axioms ();;"
  for thm in ORDINARY_PACKED_VALID ORDINARY_PACKED_GUARDS_HOLD \
             ORDINARY_PACKED_SELECTED ORDINARY_FIRE_REFINEMENT \
             ORDINARY_WROW_INDEX_NONWRAP ORDINARY_ARENA_ROW_LENGTH \
             ORDINARY_ARENA_ROW_EL ORDINARY_ARENA_ROWS_EL \
             ORDINARY_ARENA_ROW_VALID ORDINARY_ARENA_OFFSET_BOUND \
             ORDINARY_ARENA_OFFSETS_CESTA; do
    echo "Printf.printf \"val $thm : thm = %s\\n\" (string_of_thm $thm);;"
  done
} > "$tmpl"
cd "$S2N"
ocaml "$HOLDIR/inline_load.ml" "$tmpl" "$out/$leaf.inlined.ml"
OCAMLRUNPARAM=l=2000000000 ocamlopt.byte -pp "$("$HOLDIR/hol.sh" -pp)" -I "$HOLDIR" -I +unix \
  -c hol_lib.cmxa "$out/$leaf.inlined.ml" -o "$out/$leaf.inlined.cmx" -w -a
ocamlfind ocamlopt -package zarith,unix -linkpkg hol_lib.cmxa -I "$HOLDIR" \
  "$out/$leaf.inlined.cmx" -o "$out/$leaf.native"
"$out/$leaf.native" > "$out/$leaf.correct" 2>&1 || { tail -20 "$out/$leaf.correct"; echo "$leaf: proof run failed"; exit 1; }
if grep -i 'error:\|exception:' "$out/$leaf.correct"; then echo "$leaf: proof failed"; exit 1; fi
grep -c '^val ORDINARY_' "$out/$leaf.correct" | grep -q '^11$' || { echo "$leaf: final theorems missing"; exit 1; }
echo "$leaf: proved, no new axioms"
cd "$here"

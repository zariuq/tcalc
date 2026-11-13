#!/bin/bash
# run_fidelity.sh CORPUS OUTDIR [CASES] [MUTANT]
#
# Checks the HOL semantics against the C reference on a corpus written by
# `test_tisa_ref --export-hol`, in a fresh HOL Light process. OUTDIR must not
# exist; it receives input hashes, the HOL log and result.txt. CASES limits
# the run to the first CASES lines. MUTANT names a deliberate fault planted
# in a copy of the semantics (fund-pays-first, bool-load-2); a mutant run
# passes when the corpus catches it, that is when some case differs.
set -euo pipefail
corpus=$(realpath "$1"); out=$2; cases=${3:-0}; mutant=${4:-}
here=$(cd "$(dirname "$0")" && pwd)
export TCALC_DIR=$(cd "$here/../.." && pwd)
hol=${HOLDIR:?set HOLDIR to a HOL Light checkout}
s2n=${S2N:?set S2N to an s2n-bignum checkout}
[ -e "$out" ] && { echo "refusing to overwrite $out" >&2; exit 2; }
mkdir -p "$out"; out=$(realpath "$out")

src=$here
if [ -n "$mutant" ]; then
  src=$out/mutant; mkdir -p "$src"
  cp "$here/tisa_p1.ml" "$here/tisa_p1_memory.ml" "$here/tisa_p1_eval.ml" "$here/tisa_p1_fidelity.ml" "$src/"
  sed -i "s#needs \"tisa/hol/#needs \"$src/#" "$src/tisa_p1_memory.ml" "$src/tisa_p1_eval.ml" "$src/tisa_p1_fidelity.ml"
  case $mutant in
    fund-pays-first)
      python3 - "$src/tisa_p1.ml" <<'EOF'
import sys; p=sys.argv[1]; s=open(p).read()
a="if val(word_sub (tisa_fword st 20) (tisa_fword st 21)) < u then tisa_fail 4 st"
assert a in s
s=s.replace(a,"if val(word_sub (tisa_fword st 20) (tisa_fword st 21)) < u\n    then tisa_fail 4 (tisa_setfword 21 (word_add (tisa_fword st 21) (word u)) st)",1)
open(p,'w').write(s)
EOF
      ;;
    bool-load-2)
      python3 - "$src/tisa_p1.ml" <<'EOF'
import sys; p=sys.argv[1]; s=open(p).read()
a="else if t = TyBool /\\ ~tisa_bool (tisa_read st (iword(tisa_ea st p off)) w)"
assert a in s
s=s.replace(a,"else if t = TyBool /\\ ~(val(tisa_read st (iword(tisa_ea st p off)) w) <= 2)",1)
open(p,'w').write(s)
EOF
      ;;
    *) echo "unknown mutant $mutant" >&2; exit 2;;
  esac
fi

input=$corpus
if [ "$cases" != 0 ]; then input=$out/corpus.ml; head -n "$cases" "$corpus" > "$input"; fi
{
  sha256sum "$src/tisa_p1.ml" "$src/tisa_p1_memory.ml" "$src/tisa_p1_eval.ml" "$src/tisa_p1_fidelity.ml" "$input"
  sha256sum "$here/../SEMANTICS.txt" "$here/../tisa_ref.c" "$here/../test_tisa_ref.c" "$here/../tisa.h"
  echo "hol-light $(git -C "$hol" rev-parse HEAD)"; echo "s2n-bignum $(git -C "$s2n" rev-parse HEAD)"
} > "$out/inputs.sha256"

start=$(date +%s)
cd "$s2n"
printf 'loadt "%s";;\nloadt "%s";;\nloadt "%s";;\ntisa_fidelity_report "%s";;\n' "$TCALC_DIR/native/hol/roots.ml" \
  "$src/tisa_p1_fidelity.ml" "$input" "$(basename "$corpus")${mutant:+ mutant $mutant}" |
  LINE_EDITOR=env "$hol/hol.sh" > "$out/hol.log" 2>&1 || true
line=$(grep -a -o 'FIDELITY .*' "$out/hol.log" | tail -1 || true)
errors=$(grep -a -c 'Error in included file\|^Exception' "$out/hol.log" || true)
{ echo "$line"; echo "load errors: $errors"; echo "seconds: $(( $(date +%s) - start ))"; } > "$out/result.txt"
sha256sum "$out/hol.log" >> "$out/result.txt"
cat "$out/result.txt"

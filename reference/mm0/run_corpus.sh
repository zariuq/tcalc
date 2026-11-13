#!/bin/sh
# The MM0 corpus of tcalc's run.sh, checked by mm0_ref with the specifications run.sh gives:
# FILE.mm0 when it exists (peano_hex.mmu: --proof-only), otherwise --proof-only.  Every positive
# must be accepted, every negative refused (exit 1) with a reason; the summary counts refusals by
# a firing of the step and by the reader.
#   usage: run_corpus.sh MM0_REF [TCALC_DIR] [MM0_ROOT]
set -u
BIN=$1
T=${2:-$(dirname "$0")/../..}
MM0_ROOT=${3:-$T/../repos/mm0}
pos=0 posok=0 neg=0 negok=0 bystep=0 byreader=0
spec_of() { # FILE: the specification argument run.sh gives
  s="${1%.mmu}.mm0"
  if [ "$1" = "$MM0_ROOT/examples/peano_hex.mmu" ] || [ ! -f "$s" ]; then echo --proof-only; else echo "$s"; fi
}
for f in "$MM0_ROOT/examples/peano.mmu" "$MM0_ROOT/examples/peano_hex.mmu" "$T"/mm0-controls/ok-*.mmu \
         "$T"/mm0-controls/pos-*.mmu "$MM0_ROOT"/tests/mm0_mmu/pass/*.mmu; do
  pos=$((pos + 1))
  if out=$("$BIN" "$f" "$(spec_of "$f")" 2>&1); then posok=$((posok + 1)); echo "accepted  $f: ${out##*terms; }"
  else echo "REFUSED POSITIVE $f: $out"; fi
done
negative() { # LABEL ARGS...
  label=$1; shift
  neg=$((neg + 1))
  out=$("$BIN" "$@" 2>&1); rc=$?
  if [ "$rc" -eq 1 ]; then
    case "$out" in
      *"FAIL (step)"*) bystep=$((bystep + 1)); negok=$((negok + 1)); echo "refused   $label: $out" | cut -c1-230 ;;
      *FAIL*) byreader=$((byreader + 1)); negok=$((negok + 1)); echo "refused   $label: $out" | cut -c1-230 ;;
      *) echo "NO REASON $label: $out" ;;
    esac
  else echo "ACCEPTED NEGATIVE (exit $rc) $label: $out" | cut -c1-230; fi
}
for f in "$T"/mm0-controls/bad-*.mmu "$T"/mm0-controls/dv-*.mmu "$T"/mm0-controls/peano-bad-*.mmu \
         "$T"/mm0-controls/x-*.mmu "$T"/mm0-controls/neg-*.mmu "$T"/mm0-controls/c-*.mmu \
         "$T"/mm0-controls/blank_binder_alias.mmu "$MM0_ROOT"/tests/mm0_mmu/fail/*.mmu; do
  negative "$f" "$f" "$(spec_of "$f")"
done
# run.sh: the same negative under a file name that no longer matches its specification
work=$(dirname "$BIN")/renamed
mkdir -p "$work"
cp "$T"/mm0-controls/blank_binder_alias.mmu "$work/renamed_bba.mmu"
negative "renamed blank_binder_alias, no specification argument" "$work/renamed_bba.mmu"
negative "renamed blank_binder_alias, its specification" "$work/renamed_bba.mmu" "$T"/mm0-controls/blank_binder_alias.mm0
rm -f "$work/renamed_bba.mmu"
rmdir "$work" 2> /dev/null
echo "positives accepted $posok/$pos; negatives refused $negok/$neg ($bystep by a firing of the step, $byreader by the reader)"
[ "$posok" -eq "$pos" ] && [ "$negok" -eq "$neg" ]

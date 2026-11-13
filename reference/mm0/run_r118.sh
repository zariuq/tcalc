#!/bin/sh
# The specification-reader controls of tcalc's run.sh (R118: ob, local, rob, dum, nota, cmt, coe,
# up), the lines run with a proof file (.mmu), checked by mm0_ref: positives accepted, negatives
# refused (exit 1) with a reason.
#   usage: run_r118.sh MM0_REF [TCALC_DIR]
set -u
BIN=$1
T=${2:-$(dirname "$0")/../..}
R=$T/mm0-controls/r118
pos=0 posok=0 neg=0 negok=0
p() { # ARGS: must be accepted
  pos=$((pos + 1))
  if out=$("$BIN" "$@" 2>&1); then posok=$((posok + 1)); else echo "REFUSED POSITIVE $*: $out"; fi
}
n() { # ARGS: must be refused, with a reason
  neg=$((neg + 1))
  out=$("$BIN" "$@" 2>&1); rc=$?
  case "$rc:$out" in 1:*FAIL*) negok=$((negok + 1)); echo "refused  $(basename "$2"): $out" | cut -c1-200 ;;
    *) echo "NOT REFUSED (exit $rc) $*: $out" | cut -c1-300 ;; esac
}
for s in "$R"/ob/*.mm0; do
  case $(basename "$s" .mm0) in
    abs_add_body|ax_explicit_paren|ax_hyp_named|ax_prefix_app|ax_rename|base|\
    def_drop_body|def_dummy_but_body_no|def_dummy_drop_body|def_dummy_extra|\
    def_dummy_rename|def_rename|term_arrow|term_rename|thm_bound_rename|utf8_comment) p "$R/ob/base.mmu" "$s" ;;
    *) n "$R/ob/base.mmu" "$s" ;;
  esac
done
for x in la ls lt; do n "$R/local/$x.mmu" "$R/local/$x.mm0"; done
n "$R/rob/v300.mmu" "$R/rob/v300.mm0"
# s130 declares 131 sorts.  run.sh expects a refusal: 128 sorts is the limit of the .mmb format and
# of mm0-c.  MM0 itself sets no such limit for a proof file, and this checker has none: a deliberate
# difference, counted apart.
if out=$("$BIN" "$R/rob/s130.mmu" "$R/rob/s130.mm0" 2>&1); then
  echo "accepted s130 (131 sorts; run.sh expects mm0-c's 128-sort limit): ${out##*terms; }"
  deliberate=1
else echo "s130: $out"; deliberate=0; fi
for s in "$R"/rob/deep_*.mm0; do n "$R/ob/base.mmu" "$s"; done
for u in d2 d2_swapdecl d2_extra; do p "$R/dum/$u.mmu" "$R/dum/d2.mm0"; done
for s in d2_noninj d2_noninj1; do n "$R/dum/d2.mmu" "$R/dum/$s.mm0"; done
p "$R/nota/ov.mmu" "$R/nota/ov_good.mm0"
n "$R/nota/ov.mmu" "$R/nota/ov_bad.mm0"
n "$R/nota/dl.mmu" "$R/nota/dl_bad.mm0"
n "$R/cmt/cm.mmu" "$R/cmt/cm_bad.mm0"
p "$R/coe/co.mmu" "$R/coe/co.mm0"
for s in "$R"/up/bad-*.mm0; do n "$R/up/sp.mmu" "$s"; done
# adversarial_controls.sh: proof files against a fixed specification
for f in "$T"/mm0-controls/proof-file/*.mmu; do
  case $(basename "$f") in neg-*) n "$f" "$R/ob/base.mm0" ;; *) p "$f" "$R/ob/base.mm0" ;; esac
done
echo "r118 and proof-file controls: positives accepted $posok/$pos; negatives refused $negok/$neg; s130 accepted on purpose: $deliberate"
[ "$posok" -eq "$pos" ] && [ "$negok" -eq "$neg" ]

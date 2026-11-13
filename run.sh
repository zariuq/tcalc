#!/bin/sh
# The tcalc test entry.  Builds everything with make (the one build entry), then runs:
#   1. the compiled-leaf tests (Cesta adapter, Cesta pack)
#   2. test_tcalc, the kernel controls and the kernel differentials (kernel-controls/)
#   3. test_cetta_bridge (prepared steps, admission profiles, events)
#   4. mm0_tcalc and mmb_tcalc on the MM0 suites and the specification controls
#   5. hol_tcalc on the HOL Light streams
#   6. mg_tcalc on Megalodon fixtures, profiles, baselines and mutants (oracle: OCaml Megalodon)
#   7. dk_tcalc on the Dedukti suites (oracles: dk check --type-lhs, Kontroli)
#   8. the tower: mg_tcalc --emit-dk, checked by dk_tcalc, Kontroli and dk
#   9. dl_tcalc: its self-test, and the D0 programs against Souffle
#  10. test_tisa (it must reproduce the stored program manifest) and the lean_tcalc self-test
#  11. the Cesta differential gate
#  12. diff_micromath (the tcalc routes against Micromath's own kernel)
#  13. adversarial_controls.sh (independent oracles)
# Every binary that links the proved leaf is checked for the exact proof-image bytes.
# Every count printed is counted by this run.  Scratch files go to a temporary directory
# outside the tree (mktemp -d, so TMPDIR chooses where).
set -eu
cd "$(dirname "$0")"
MICROMATH=${MICROMATH:-ref}
# The corpora: each variable may be set; otherwise it is searched next to this repository.
# first_dir DIR...: the first of the directories that exists, else the last one named
first_dir() {
  for d in "$@"; do [ -d "$d" ] && { echo "$d"; return; }; done
  echo "$d"
}
MM0_ROOT=${MM0_ROOT:-$(first_dir ../repos/mm0 ../../../repos/mm0 ../../repos/mm0)}
HOL_DIR=${HOL_DIR:-$(first_dir ../Mettapedia/hol_light/Transform ../../hol_light/Transform ../../Mettapedia/hol_light/Transform)}
MG_FIX=${MG_FIX:-$(first_dir ../hyperon/CeTTa/tests/megalodon/fixtures ../../../hyperon/CeTTa/tests/megalodon/fixtures ../../hyperon/CeTTa/tests/megalodon/fixtures)}
MG_EGAL=${MG_EGAL:?set MG_EGAL to a directory holding the egal corpus Part1.sexpr ... Part14.sexpr}
DK_CURR=${DK_CURR:-$(first_dir ../Mettapedia/MettaKernel/Curriculum/DeduktiLambdapi ../Curriculum/DeduktiLambdapi ../../Mettapedia/MettaKernel/Curriculum/DeduktiLambdapi)}
DK_EX=${DK_EX:-$(first_dir ../repos/dedukti/examples ../../../repos/dedukti/examples ../../repos/dedukti/examples)}
KO_EX=${KO_EX:-$(first_dir ../repos/kontroli-rs/examples ../../../repos/kontroli-rs/examples ../../repos/kontroli-rs/examples)}
DK_THEORIES=${DK_THEORIES:-$(first_dir ../repos/dedukti/libraries/theories ../../../repos/dedukti/libraries/theories ../../repos/dedukti/libraries/theories)}
DL_TESTS=${DL_TESTS:-../Mettapedia/metta/gslt}
MM0=${MM0:-$MM0_ROOT/examples}
MM0_MMU_TEST=${MM0_MMU_TEST:-$MM0_ROOT/tests/mm0_mmu}
MMB=${MMB:-$MM0_ROOT/mm0-js/test}
MMB_TEST=${MMB_TEST:-$MM0_ROOT/tests/mmb}
FLAT_RUNTIME=compiled/ordinary_flat_cesta_runtime.o
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

# leaf_bytes OBJECT-OR-BINARY FUNCTION: the function's bytes, one hex pair per line
leaf_bytes() {
  objdump -d --disassemble="$2" "$1" | awk -F'\t' '/^ *[0-9a-f]+:\t/ { n = split($2, b, " "); for (i = 1; i <= n; i++) print b[i] }'
}
check_flat_bytes() { # BINARY
  for fn in flat_fire ordinary_flat_pack ordinary_flat_adapter ordinary_flat_failure; do
    leaf_bytes "$FLAT_RUNTIME" "$fn" > "$WORK/flat-$fn.object"
    leaf_bytes "$1" "$fn" > "$WORK/flat-$fn.linked"
    [ -s "$WORK/flat-$fn.object" ] && cmp -s "$WORK/flat-$fn.object" "$WORK/flat-$fn.linked" || {
      echo "$1: $fn differs from the exact proof-image bytes" >&2; exit 1;
    }
  done
  echo "$1: exact Cesta pack, adapter, failure, and flat_fire bytes"
}

# This is the complete corpus gate, not an opportunistic subset check.
for required in "$MG_EGAL/Part1.sexpr" "$DK_CURR/10_kernel_curriculum_lf_positive.dk" "$HOL_DIR/core.holr" "$HOL_DIR/transform.holr"; do
  [ -f "$required" ] || { echo "MISSING REQUIRED CORPUS: $required" >&2; exit 1; }
done
for required in "$DK_EX" "$KO_EX" "$DK_THEORIES" dk-bridge mg-controls/mutants/baseline_sexpr mg-controls/mutants/sexpr; do
  [ -d "$required" ] || { echo "MISSING REQUIRED CORPUS: $required" >&2; exit 1; }
done

make -s all MICROMATH="$MICROMATH"

./test_ordinary_flat_cesta_adapter
./test_tcalc_cesta_pack

./test_tcalc
check_flat_bytes test_tcalc
sh kernel-controls/run.sh "$WORK/kernel-controls" > "$WORK/kernel-controls.out" || { cat "$WORK/kernel-controls.out"; exit 1; }
tail -1 "$WORK/kernel-controls.out"
sh kernel-controls/run_differential.sh "$WORK/kernel-differential" "" "${KERNEL_SEEDS:-20000}"

./test_cetta_bridge
check_flat_bytes test_cetta_bridge

mmu_pos=0
for f in "$MM0/peano.mmu" "$MM0/peano_hex.mmu" mm0-controls/ok-*.mmu mm0-controls/pos-*.mmu "$MM0_MMU_TEST"/pass/*.mmu; do
  [ -f "$f" ] || { echo "MISSING MMU POSITIVE CONTROL: $f"; exit 1; }
  spec="${f%.mmu}.mm0"
  if [ "$f" = "$MM0/peano_hex.mmu" ] || [ ! -f "$spec" ]; then
    ./mm0_tcalc "$f" --proof-only
  else
    ./mm0_tcalc "$f" "$spec"
  fi
  mmu_pos=$((mmu_pos + 1))
done
[ "$mmu_pos" -eq 17 ] || { echo "EXPECTED 17 MMU POSITIVE CONTROLS, GOT $mmu_pos"; exit 1; }

mmu_refused=0
for f in mm0-controls/bad-*.mmu mm0-controls/dv-*.mmu mm0-controls/peano-bad-*.mmu \
         mm0-controls/x-*.mmu mm0-controls/neg-*.mmu mm0-controls/c-*.mmu \
         mm0-controls/blank_binder_alias.mmu "$MM0_MMU_TEST"/fail/*.mmu; do
  [ -f "$f" ] || { echo "MISSING MMU NEGATIVE CONTROL: $f"; exit 1; }
  spec="${f%.mmu}.mm0"
  [ -f "$spec" ] || spec="--proof-only"
  set +e
  msg=$(./mm0_tcalc "$f" "$spec" 2>&1)
  rc=$?
  set -e
  if [ "$rc" -ne 1 ]; then echo "WRONG EXIT CODE ($rc, expected 1) ON MMU NEGATIVE: $f ($msg)"; exit 1; fi
  case "$msg" in *FAIL*) ;; *) echo "MISSING FAIL REASON ON MMU NEGATIVE: $f ($msg)"; exit 1 ;; esac
  mmu_refused=$((mmu_refused + 1))
done
# The same negative under a file name that no longer matches its specification.
cat mm0-controls/blank_binder_alias.mmu > "$WORK/renamed_bba.mmu"
for arg in "" "mm0-controls/blank_binder_alias.mm0"; do
  set +e
  if [ -z "$arg" ]; then msg=$(./mm0_tcalc "$WORK/renamed_bba.mmu" 2>&1); else msg=$(./mm0_tcalc "$WORK/renamed_bba.mmu" "$arg" 2>&1); fi
  rc=$?
  set -e
  if [ "$rc" -ne 1 ]; then echo "WRONG EXIT CODE ($rc, expected 1) ON RENAMED MMU ($arg): $msg"; exit 1; fi
  case "$msg" in *FAIL*) ;; *) echo "MISSING FAIL REASON ON RENAMED MMU ($arg): $msg"; exit 1 ;; esac
  mmu_refused=$((mmu_refused + 1))
done
[ "$mmu_refused" -eq 79 ] || { echo "EXPECTED 79 MMU NEGATIVE CONTROLS, GOT $mmu_refused"; exit 1; }
printf 'mmu controls: %d/17 positive accepted, %d/79 negative refused cleanly (exit 1)\n' "$mmu_pos" "$mmu_refused"

./mmb_tcalc "$MMB/peano.mmb" "$MM0/peano.mm0"
./mmb_tcalc "$MMB_TEST/pass/max_bound_vars.mmb" "$MMB_TEST/pass/max_bound_vars.mm0"
for f in "$MMB/hol.mmb" "$MMB_TEST/pass/no_index.mmb"; do
  [ -f "$f" ] || { echo "MISSING MMB POSITIVE CONTROL: $f"; exit 1; }
  ./mmb_tcalc "$f" --proof-only
done
mmb_refused=0
for f in "$MMB_TEST"/fail/*.mmb mm0-controls/blank_binder_alias.mmb; do
  [ -f "$f" ] || { echo "MISSING MMB NEGATIVE CONTROL: $f"; exit 1; }
  spec="${f%.mmb}.mm0"
  [ -f "$spec" ] || spec="--proof-only"
  set +e
  msg=$(./mmb_tcalc "$f" "$spec" 2>&1)
  rc=$?
  set -e
  if [ "$rc" -ne 1 ]; then echo "WRONG EXIT CODE ($rc, expected 1) ON MMB NEGATIVE: $f ($msg)"; exit 1; fi
  case "$msg" in *FAIL*) ;; *) echo "MISSING FAIL REASON ON MMB NEGATIVE: $f ($msg)"; exit 1 ;; esac
  mmb_refused=$((mmb_refused + 1))
done
cat mm0-controls/blank_binder_alias.mmb > "$WORK/renamed_bba.mmb"
for arg in "" "mm0-controls/blank_binder_alias.mm0"; do
  set +e
  if [ -z "$arg" ]; then msg=$(./mmb_tcalc "$WORK/renamed_bba.mmb" 2>&1); else msg=$(./mmb_tcalc "$WORK/renamed_bba.mmb" "$arg" 2>&1); fi
  rc=$?
  set -e
  if [ "$rc" -ne 1 ]; then echo "WRONG EXIT CODE ($rc, expected 1) ON RENAMED MMB ($arg): $msg"; exit 1; fi
  case "$msg" in *FAIL*) ;; *) echo "MISSING FAIL REASON ON RENAMED MMB ($arg): $msg"; exit 1 ;; esac
  mmb_refused=$((mmb_refused + 1))
done
# One flipped byte in a valid proof stream.
cat "$MMB/peano.mmb" > "$WORK/sf_peano.mmb"
printf '\001' | dd of="$WORK/sf_peano.mmb" bs=1 seek=46176 count=1 conv=notrunc status=none
set +e
msg=$(./mmb_tcalc "$WORK/sf_peano.mmb" "$MM0/peano.mm0" 2>&1)
rc=$?
set -e
if [ "$rc" -ne 1 ]; then echo "WRONG EXIT CODE ($rc, expected 1) ON SF_PEANO MMB: $msg"; exit 1; fi
case "$msg" in *FAIL*) ;; *) echo "MISSING FAIL REASON ON SF_PEANO MMB: $msg"; exit 1 ;; esac
mmb_refused=$((mmb_refused + 1))
[ "$mmb_refused" -eq 25 ] || { echo "EXPECTED 25 MMB NEGATIVE CONTROLS, GOT $mmb_refused"; exit 1; }
printf 'mmb controls: 4/4 positive accepted, %d/25 negative refused cleanly (exit 1)\n' "$mmb_refused"

# R118 .mm0 specification-reader control suite (ob, local, rob, dum, nota, cmt, coe, up)
r118_pos=0
r118_neg=0
check_r118_pos() {
  "$@" >/dev/null
  r118_pos=$((r118_pos + 1))
}
check_r118_neg() {
  set +e
  msg=$("$@" 2>&1)
  rc=$?
  set -e
  if [ "$rc" -ne 1 ]; then echo "WRONG EXIT CODE ($rc, expected 1) ON R118 NEGATIVE ($*): $msg"; exit 1; fi
  case "$msg" in *FAIL*) ;; *) echo "MISSING FAIL REASON ON R118 NEGATIVE ($*): $msg"; exit 1 ;; esac
  r118_neg=$((r118_neg + 1))
}
for s in mm0-controls/r118/ob/*.mm0; do
  bn=$(basename "$s" .mm0)
  case "$bn" in
    abs_add_body|ax_explicit_paren|ax_hyp_named|ax_prefix_app|ax_rename|base|\
    def_drop_body|def_dummy_but_body_no|def_dummy_drop_body|def_dummy_extra|\
    def_dummy_rename|def_rename|term_arrow|term_rename|thm_bound_rename|utf8_comment)
      check_r118_pos ./mm0_tcalc mm0-controls/r118/ob/base.mmu "$s"
      check_r118_pos ./mmb_tcalc mm0-controls/r118/ob/base.mmb "$s"
      ;;
    *)
      check_r118_neg ./mm0_tcalc mm0-controls/r118/ob/base.mmu "$s"
      check_r118_neg ./mmb_tcalc mm0-controls/r118/ob/base.mmb "$s"
      ;;
  esac
done
for x in la ls lt; do
  check_r118_neg ./mm0_tcalc "mm0-controls/r118/local/$x.mmu" "mm0-controls/r118/local/$x.mm0"
done
for x in s130 v300; do
  check_r118_neg ./mm0_tcalc "mm0-controls/r118/rob/$x.mmu" "mm0-controls/r118/rob/$x.mm0"
done
for s in mm0-controls/r118/rob/deep_*.mm0; do
  check_r118_neg ./mm0_tcalc mm0-controls/r118/ob/base.mmu "$s"
  check_r118_neg ./mmb_tcalc mm0-controls/r118/ob/base.mmb "$s"
done
for u in d2 d2_swapdecl d2_extra; do
  check_r118_pos ./mm0_tcalc "mm0-controls/r118/dum/$u.mmu" mm0-controls/r118/dum/d2.mm0
done
check_r118_pos ./mmb_tcalc mm0-controls/r118/dum/d2.mmb mm0-controls/r118/dum/d2.mm0
for s in d2_noninj d2_noninj1; do
  check_r118_neg ./mm0_tcalc mm0-controls/r118/dum/d2.mmu "mm0-controls/r118/dum/$s.mm0"
  check_r118_neg ./mmb_tcalc mm0-controls/r118/dum/d2.mmb "mm0-controls/r118/dum/$s.mm0"
done
check_r118_pos ./mm0_tcalc mm0-controls/r118/nota/ov.mmu mm0-controls/r118/nota/ov_good.mm0
check_r118_pos ./mmb_tcalc mm0-controls/r118/nota/ov.mmb mm0-controls/r118/nota/ov_good.mm0
check_r118_neg ./mm0_tcalc mm0-controls/r118/nota/ov.mmu mm0-controls/r118/nota/ov_bad.mm0
check_r118_neg ./mmb_tcalc mm0-controls/r118/nota/ov.mmb mm0-controls/r118/nota/ov_bad.mm0
check_r118_neg ./mm0_tcalc mm0-controls/r118/nota/dl.mmu mm0-controls/r118/nota/dl_bad.mm0
check_r118_neg ./mmb_tcalc mm0-controls/r118/nota/dl.mmb mm0-controls/r118/nota/dl_bad.mm0
check_r118_neg ./mm0_tcalc mm0-controls/r118/cmt/cm.mmu mm0-controls/r118/cmt/cm_bad.mm0
check_r118_neg ./mmb_tcalc mm0-controls/r118/cmt/cm.mmb mm0-controls/r118/cmt/cm_bad.mm0
check_r118_pos ./mm0_tcalc mm0-controls/r118/coe/co.mmu mm0-controls/r118/coe/co.mm0
for s in mm0-controls/r118/up/bad-*.mm0; do
  check_r118_neg ./mm0_tcalc mm0-controls/r118/up/sp.mmu "$s"
  check_r118_neg ./mmb_tcalc mm0-controls/r118/up/sp.mmb "$s"
done
[ "$r118_pos" -eq 39 ] || { echo "EXPECTED 39 R118 POSITIVE CONTROLS, GOT $r118_pos"; exit 1; }
[ "$r118_neg" -eq 151 ] || { echo "EXPECTED 151 R118 NEGATIVE CONTROLS, GOT $r118_neg"; exit 1; }
printf 'r118 spec controls: %d/39 positive accepted, %d/151 negative refused cleanly (exit 1)\n' "$r118_pos" "$r118_neg"

# ax5 side conditions over bound arguments (mm0.md Vars): one valid use, five violations
./mmb_tcalc mm0-controls/ax5/fresh.mmb mm0-controls/ax5/fresh.mm0 >/dev/null
ax5_neg=0
for x in def_dependency_isz definition_dependency binder_position context_layout disjoint; do
  check_r118_neg ./mmb_tcalc "mm0-controls/ax5/$x.mmb" "mm0-controls/ax5/$x.mm0"
  ax5_neg=$((ax5_neg + 1))
done
printf 'ax5 controls: 1/1 positive accepted, %d/5 negative refused cleanly (exit 1)\n' "$ax5_neg"

# HOL Light LCF kernel & HOLRPLY1 stream verifier on tcalc
./hol_tcalc --test > "$WORK/hol_selftest.out" || { cat "$WORK/hol_selftest.out"; exit 1; }
tail -1 "$WORK/hol_selftest.out"
hol_streams=0
hol_unspecified=0
for s in "$HOL_DIR"/*.holr; do
  spec="${s%.holr}.checked-sequents.txt"
  # the default policy is `standard`: a stream cannot bring an axiom of its own
  if [ -f "$spec" ]; then
    ./hol_tcalc --spec "$spec" "$s"
    hol_streams=$((hol_streams + 1))
  else
    ./hol_tcalc "$s"
    hol_unspecified=$((hol_unspecified + 1))
  fi
done
hol_neg=0
set +e
./hol_tcalc --spec "$HOL_DIR/transform.checked-sequents.txt" "$HOL_DIR/core.holr" >/dev/null 2>&1
[ "$?" -eq 1 ] || { echo "EXPECTED EXIT 1 ON HOL SPEC MISMATCH"; exit 1; }
hol_neg=$((hol_neg + 1))
head -c 1024 "$HOL_DIR/core.holr" > "$WORK/trunc_core.holr"
./hol_tcalc "$WORK/trunc_core.holr" >/dev/null 2>&1
[ "$?" -eq 1 ] || { echo "EXPECTED EXIT 1 ON TRUNCATED HOLR"; exit 1; }
hol_neg=$((hol_neg + 1))
cat "$HOL_DIR/core.holr" > "$WORK/bad_core.holr"
printf '\377' | dd of="$WORK/bad_core.holr" bs=1 seek=256 count=1 conv=notrunc status=none
./hol_tcalc "$WORK/bad_core.holr" >/dev/null 2>&1
[ "$?" -eq 1 ] || { echo "EXPECTED EXIT 1 ON CORRUPTED HOLR"; exit 1; }
hol_neg=$((hol_neg + 1))
set -e
printf 'hol_tcalc controls: %d streams accepted against their checked sequents, %d replayed without a sequent list, %d/3 negative streams refused cleanly (exit 1)\n' "$hol_streams" "$hol_unspecified" "$hol_neg"

# Megalodon (Egal HoTTG, HF, Mizar, HOAS) proof-kernel & -sexprinfo verifier on tcalc
MG_BIN="${MG_BIN:-}"
if [ -z "$MG_BIN" ] && [ -x ../Mettapedia/megalodon/bin/megalodon ]; then
  MG_BIN="../Mettapedia/megalodon/bin/megalodon"
elif [ -z "$MG_BIN" ]; then
  MG_BIN="$(command -v megalodon || true)"
fi
[ -n "$MG_BIN" ] && [ -x "$MG_BIN" ] || {
  echo "MISSING ORACLE: set MG_BIN to OCaml Megalodon" >&2; exit 1;
}

./mg_tcalc --self-test --profile egal --axioms none "$MG_FIX/pfghotg_churchnum.sexpr" --profile hf --axioms all "$MG_FIX/pfghf_logic.sexpr"
./mg_tcalc --profile egal --chain \
  --axioms all "$MG_EGAL/Part1.sexpr" \
  --axioms none \
  "$MG_EGAL/Part2.sexpr" "$MG_EGAL/Part3.sexpr" \
  "$MG_EGAL/Part4.sexpr" "$MG_EGAL/Part5.sexpr" "$MG_EGAL/Part6.sexpr" \
  "$MG_EGAL/Part7.sexpr" "$MG_EGAL/Part8.sexpr" "$MG_EGAL/Part9.sexpr" \
  "$MG_EGAL/Part10.sexpr" "$MG_EGAL/Part10b.sexpr" "$MG_EGAL/Part11.sexpr" \
  "$MG_EGAL/Part12.sexpr" "$MG_EGAL/Part13.sexpr" "$MG_EGAL/Part14.sexpr"

# 4 profile positive & negative upstream examples + cross-profile primitive guards
mg_prof_pos=0
mg_prof_neg=0
for pair in "egal:" "mizar:-mizar" "hf:-hf" "hoas:-hoas"; do
  prof="${pair%%:*}"
  mflag="${pair#*:}"
  ./mg_tcalc --profile "$prof" "mg-controls/profiles/${prof}_pos.sexpr" >/dev/null
  "$MG_BIN" $mflag "mg-controls/profiles/${prof}_pos.mg" >/dev/null
  mg_prof_pos=$((mg_prof_pos + 1))

  set +e
  ./mg_tcalc --profile "$prof" "mg-controls/profiles/${prof}_neg.sexpr" >/dev/null 2>&1
  rc=$?
  set -e
  [ "$rc" -eq 1 ] || { echo "EXPECTED EXIT 1 ON mg-controls/profiles/${prof}_neg.sexpr"; exit 1; }
  set +e
  "$MG_BIN" $mflag "mg-controls/profiles/${prof}_neg.mg" >/dev/null 2>&1
  orc=$?
  set -e
  [ "$orc" -ne 0 ] || { echo "ORACLE ACCEPTED mg-controls/profiles/${prof}_neg.mg"; exit 1; }
  mg_prof_neg=$((mg_prof_neg + 1))
done
for pair in "egal_pos:hf:-hf" "egal_pos:mizar:-mizar" "egal_pos:hoas:-hoas" "hf_pos:mizar:-mizar" "hf_pos:hoas:-hoas" "mizar_pos:hoas:-hoas"; do
  f="${pair%%:*}"; rest="${pair#*:}"; prof="${rest%%:*}"; mflag="${rest#*:}"
  set +e
  ./mg_tcalc --profile "$prof" "mg-controls/profiles/$f.sexpr" >/dev/null 2>&1
  rc=$?
  set -e
  [ "$rc" -eq 1 ] || { echo "EXPECTED EXIT 1 ON CROSS-PROFILE $f UNDER $prof"; exit 1; }
  set +e
  "$MG_BIN" $mflag "mg-controls/profiles/$f.mg" >/dev/null 2>&1
  orc=$?
  set -e
  [ "$orc" -ne 0 ] || { echo "ORACLE ACCEPTED CROSS-PROFILE $f UNDER $prof"; exit 1; }
  mg_prof_neg=$((mg_prof_neg + 1))
done
printf 'mg_tcalc profile controls: %d/4 positive accepted, %d/10 negative/cross-profile refused (oracle: OCaml megalodon)\n' "$mg_prof_pos" "$mg_prof_neg"

# 20 baseline theorems + 100 mutants (5 mutation kinds x 20 theorems across Part1..Part14)
mg_base_pos=0
for f in mg-controls/mutants/baseline_sexpr/*.sexpr; do
  ./mg_tcalc "$f" >/dev/null
  bname="$(basename "$f" .sexpr)"
  "$MG_BIN" "mg-controls/mutants/baseline_mg/$bname.mg" >/dev/null
  mg_base_pos=$((mg_base_pos + 1))
done
mg_mut_neg=0
for f in mg-controls/mutants/sexpr/*.sexpr; do
  set +e
  ./mg_tcalc "$f" >/dev/null 2>&1
  rc=$?
  set -e
  [ "$rc" -eq 1 ] || { echo "EXPECTED EXIT 1 ON MUTANT $f"; exit 1; }
  bname="$(basename "$f" .sexpr)"
  set +e
  "$MG_BIN" "mg-controls/mutants/mg/$bname.mg" >/dev/null 2>&1
  orc=$?
  set -e
  [ "$orc" -ne 0 ] || { echo "ORACLE ACCEPTED MUTANT $bname.mg"; exit 1; }
  mg_mut_neg=$((mg_mut_neg + 1))
done
[ "$mg_base_pos" -eq 20 ] || { echo "EXPECTED 20 MG BASELINES, GOT $mg_base_pos"; exit 1; }
[ "$mg_mut_neg" -eq 100 ] || { echo "EXPECTED 100 MG MUTANTS, GOT $mg_mut_neg"; exit 1; }
printf 'mg_tcalc mutant controls: %d/20 baselines accepted, %d/100 mutants refused (oracle: OCaml megalodon)\n' "$mg_base_pos" "$mg_mut_neg"

# Dedukti (Lambda-Pi Modulo Rewriting) verifier on tcalc (default --pts lf; --pts cc opt-in)
DK_BIN="${DK_BIN:-}"
if [ -z "$DK_BIN" ] && [ -x ../repos/dedukti/_build/default/commands/main.exe ]; then
  DK_BIN="../repos/dedukti/_build/default/commands/main.exe"
elif [ -z "$DK_BIN" ]; then
  DK_BIN="$(command -v dk || true)"
fi
[ -n "$DK_BIN" ] && [ -x "$DK_BIN" ] || {
  echo "MISSING ORACLE: set DK_BIN to Dedukti" >&2; exit 1;
}
KO_BIN="${KO_BIN:-../repos/kontroli-rs/target/release/kocheck}"
[ -x "$KO_BIN" ] || {
  echo "MISSING ORACLE: set KO_BIN to Kontroli kocheck" >&2; exit 1;
}
KO_BIN="$(realpath "$KO_BIN")"

sh ./admission_controls.sh "$PWD/dk_tcalc" "$PWD/mg_tcalc" "$(realpath "$DK_BIN")" "$KO_BIN"
./dk_tcalc --self-test "$DK_CURR/10_kernel_curriculum_lf_positive.dk"
./dk_tcalc --pts cc "$DK_CURR/10_kernel_curriculum_positive.dk" >/dev/null
"$DK_BIN" check --type-lhs "$DK_CURR/10_kernel_curriculum_lf_positive.dk" >/dev/null
"$DK_BIN" check --coc --type-lhs "$DK_CURR/10_kernel_curriculum_positive.dk" >/dev/null
dk_neg=0
set +e
./dk_tcalc "$DK_CURR/10_kernel_curriculum_positive.dk" >/dev/null 2>&1
rc=$?
set -e
if [ "$rc" -ne 1 ]; then echo "EXPECTED EXIT 1 ON CoC FILE IN DEFAULT STRICT LF MODE"; exit 1; fi
set +e
"$DK_BIN" check --type-lhs "$DK_CURR/10_kernel_curriculum_positive.dk" >/dev/null 2>&1
orc=$?
set -e
if [ "$orc" -eq 0 ]; then echo "EXPECTED dk check TO REFUSE CoC FILE WITHOUT --coc"; exit 1; fi
dk_neg=$((dk_neg + 1))
for f in "$DK_CURR"/neg_kernel_*.dk; do
  set +e
  ./dk_tcalc --pts cc "$f" >/dev/null 2>&1
  rc=$?
  set -e
  if [ "$rc" -ne 1 ]; then echo "EXPECTED EXIT 1 ON DK NEGATIVE: $f"; exit 1; fi
  set +e
  "$DK_BIN" check --coc --type-lhs "$f" >/dev/null 2>&1
  orc=$?
  set -e
  if [ "$orc" -eq 0 ]; then echo "EXPECTED dk check TO REFUSE DK NEGATIVE: $f"; exit 1; fi
  dk_neg=$((dk_neg + 1))
done
[ "$dk_neg" -eq 5 ] || { echo "EXPECTED 5 DK NEGATIVE CONTROLS, GOT $dk_neg"; exit 1; }

# 18+5 adversarial controls (dk-controls/n01..n17, p01..p07) with dk check --type-lhs as oracle
adv_neg=0
adv_pos=0
for f in dk-controls/n*.dk; do
  set +e
  ./dk_tcalc "$f" >/dev/null 2>&1
  rc=$?
  "$DK_BIN" check --type-lhs "$f" >/dev/null 2>&1
  orc=$?
  set -e
  if [ "$rc" -ne 1 ]; then echo "EXPECTED EXIT 1 ON DK ADV NEGATIVE: $f"; exit 1; fi
  if [ "$orc" -eq 0 ]; then echo "ORACLE DISAGREEMENT ON $f"; exit 1; fi
  adv_neg=$((adv_neg + 1))
done
[ "$adv_neg" -eq 18 ] || { echo "EXPECTED 18 DK ADV NEGATIVE CONTROLS, GOT $adv_neg"; exit 1; }
for f in dk-controls/p*.dk; do
  ./dk_tcalc "$f" >/dev/null
  "$DK_BIN" check --type-lhs "$f" >/dev/null || { echo "ORACLE DISAGREEMENT ON $f"; exit 1; }
  adv_pos=$((adv_pos + 1))
done
[ "$adv_pos" -eq 5 ] || { echo "EXPECTED 5 DK ADV POSITIVE CONTROLS, GOT $adv_pos"; exit 1; }
printf 'dk_tcalc adv controls (oracle: dk check --type-lhs): %d/5 positive twins accepted, %d/18 adversarial negatives refused, 0 disagreements\n' "$adv_pos" "$adv_neg"

# Dedukti libraries/theories in strict LF
th_cnt=0
for f in "$DK_THEORIES"/*.dk; do
  ./dk_tcalc "$f" >/dev/null
  "$DK_BIN" check --type-lhs "$f" >/dev/null
  th_cnt=$((th_cnt + 1))
done
[ "$th_cnt" -eq 13 ] || { echo "EXPECTED 13 DEDUKTI THEORIES, GOT $th_cnt"; exit 1; }
printf 'dk_tcalc libraries/theories (oracle: dk check --type-lhs): %d/13 accepted, 0 disagreements\n' "$th_cnt"

# Dedukti examples & Kontroli examples
dk_ex_oracle=0
dk_ex_no_oracle=0
for f in "$DK_EX/coc.dk" "$DK_EX/append.dk" "$DK_EX/plus.dk" "$DK_EX/church.dk" \
         "$DK_EX/compute.dk" "$DK_EX/emptySet.dk" "$DK_EX/pureLambdaCalculus2.dk"; do
  ./dk_tcalc "$f" >/dev/null
  "$DK_BIN" check --type-lhs "$f" >/dev/null
  dk_ex_oracle=$((dk_ex_oracle + 1))
done
# Legacy Dedukti 2.5 syntax files (unspaced -> / => rejected by dk check 2.7 lexer): reported as no-oracle
for f in "$DK_EX/lambda.dk" "$DK_EX/pureLambdaCalculus.dk" "$DK_EX/surjective.dk"; do
  ./dk_tcalc "$f" >/dev/null
  dk_ex_no_oracle=$((dk_ex_no_oracle + 1))
done
./dk_tcalc --chain "$DK_EX/FO.dk" "$DK_EX/FO_theorems.dk" "$DK_EX/classical.dk" >/dev/null
dk_ex_no_oracle=$((dk_ex_no_oracle + 3))
printf 'dk_tcalc dedukti/examples: %d/7 verified (oracle: dk check --type-lhs), 0 disagreements; %d unchecked (no oracle: legacy Dedukti 2.5 unspaced ->/=> syntax)\n' "$dk_ex_oracle" "$dk_ex_no_oracle"
ko_cnt=0
./dk_tcalc \
  "$KO_EX/nat.dk" "$KO_EX/bool.dk" "$KO_EX/fo_imp.dk" "$KO_EX/magic.dk" "$KO_EX/pure.dk" >/dev/null
./dk_tcalc --chain "$KO_EX/bool.dk" "$KO_EX/sudoku/sudoku.dk" "$KO_EX/sudoku/solve_easy.dk" >/dev/null
for f in "$KO_EX/nat.dk" "$KO_EX/bool.dk" "$KO_EX/fo_imp.dk" "$KO_EX/magic.dk" "$KO_EX/pure.dk"; do
  (cd "$(dirname "$f")" && "$KO_BIN" "$(basename "$f")") >/dev/null
  "$DK_BIN" check --type-lhs "$f" >/dev/null
  ko_cnt=$((ko_cnt + 1))
done
# These three fixtures share unqualified names, so check their shared context
# as one article rather than assigning each file a different Kontroli module.
cat "$KO_EX/bool.dk" "$KO_EX/sudoku/sudoku.dk" "$KO_EX/sudoku/solve_easy.dk" > "$WORK/sudoku.dk"
"$KO_BIN" - < "$WORK/sudoku.dk" >/dev/null
printf 'dk_tcalc kontroli-rs/examples: %d/5 standalone (Dedukti and Kontroli), 3-file sudoku chain (Kontroli) accepted\n' "$ko_cnt"

# Extracted Megalodon-Dedukti bridge fixtures (dk-bridge/*.dk)
br_cnt=0
for f in dk-bridge/*.dk; do
  ./dk_tcalc "$f" >/dev/null
  "$DK_BIN" check --type-lhs "$f" >/dev/null
  br_cnt=$((br_cnt + 1))
done
[ "$br_cnt" -eq 26 ] || { echo "EXPECTED 26 DK BRIDGE FIXTURES, GOT $br_cnt"; exit 1; }
printf 'dk_tcalc dk-bridge fixtures (oracle: dk check --type-lhs): %d/26 accepted, 0 disagreements\n' "$br_cnt"
printf 'dk_tcalc curriculum controls (oracle: dk check --type-lhs): 2/2 positive (lf + cc) accepted, %d/5 curriculum negatives refused cleanly (exit 1)\n' "$dk_neg"

# The tower (Megalodon -> Dedukti) across Part1..Part14, 20 baselines, and 100 mutants
./dk_tcalc --pts lf tower/sttfa_hotg_base.dk >/dev/null
"$KO_BIN" tower/sttfa_hotg_base.dk >/dev/null
"$DK_BIN" check --type-lhs tower/sttfa_hotg_base.dk >/dev/null
tower_parts=0
for p in Part1 Part2 Part3 Part4 Part5 Part6 Part7 Part8 Part9 Part10 Part10b Part11 Part12 Part13 Part14; do
  ./mg_tcalc --emit-dk "$WORK/tower_${p}.dk" "$MG_EGAL/${p}.sexpr" >/dev/null
  ./dk_tcalc --pts lf "$WORK/tower_${p}.dk" >/dev/null
  "$DK_BIN" check --type-lhs "$WORK/tower_${p}.dk" >/dev/null
  rm -f "$WORK/tower_${p}.dk"
  tower_parts=$((tower_parts + 1))
done
[ "$tower_parts" -eq 15 ] || { echo "EXPECTED 15 TOWER PARTS, GOT $tower_parts"; exit 1; }
tower_base_pos=0
for f in mg-controls/mutants/baseline_sexpr/*.sexpr; do
  ./mg_tcalc --emit-dk "$WORK/tower_base.dk" "$f" >/dev/null
  ./dk_tcalc --pts lf "$WORK/tower_base.dk" >/dev/null
  "$DK_BIN" check --type-lhs "$WORK/tower_base.dk" >/dev/null
  rm -f "$WORK/tower_base.dk"
  tower_base_pos=$((tower_base_pos + 1))
done
tower_mut_neg=0
for f in mg-controls/mutants/sexpr/*.sexpr; do
  set +e
  ./mg_tcalc --emit-dk "$WORK/tower_mut.dk" "$f" >/dev/null 2>&1
  rc=$?
  set -e
  [ "$rc" -eq 1 ] || { echo "EXPECTED EXIT 1 FROM mg_tcalc ON MUTANT $f"; exit 1; }
  set +e
  ./dk_tcalc --pts lf "$WORK/tower_mut.dk" >/dev/null 2>&1
  drc=$?
  "$DK_BIN" check --type-lhs "$WORK/tower_mut.dk" >/dev/null 2>&1
  orc=$?
  set -e
  [ "$drc" -eq 1 ] || { echo "EXPECTED EXIT 1 FROM dk_tcalc ON TRANSLATED MUTANT $f"; exit 1; }
  [ "$orc" -ne 0 ] || { echo "ORACLE dk check ACCEPTED TRANSLATED MUTANT $f"; exit 1; }
  rm -f "$WORK/tower_mut.dk"
  tower_mut_neg=$((tower_mut_neg + 1))
done
[ "$tower_base_pos" -eq 20 ] || { echo "EXPECTED 20 TOWER BASELINES, GOT $tower_base_pos"; exit 1; }
[ "$tower_mut_neg" -eq 100 ] || { echo "EXPECTED 100 TOWER MUTANTS, GOT $tower_mut_neg"; exit 1; }
printf 'tower controls (oracles: OCaml megalodon, dk check --type-lhs): %d/15 Egal parts + %d/20 baselines accepted, %d/100 translated mutants refused\n' "$tower_parts" "$tower_base_pos" "$tower_mut_neg"

# The bodhisattva tower (HOTG -> mg_tcalc --bodhisattva-gate -> .dk -> dk_tcalc, Kontroli, dk)
"$MG_BIN" tower/bodhisattva_tower.mg >/dev/null
./mg_tcalc --emit-dk "$WORK/bodhisattva_tower.dk" tower/bodhisattva_tower.sexpr --bodhisattva-gate
cmp -s "$WORK/bodhisattva_tower.dk" tower/bodhisattva_tower.dk || { echo "mg_tcalc --emit-dk no longer reproduces tower/bodhisattva_tower.dk"; exit 1; }
./dk_tcalc --pts lf tower/bodhisattva_tower.dk
"$KO_BIN" tower/bodhisattva_tower.dk >/dev/null
"$DK_BIN" check --type-lhs tower/bodhisattva_tower.dk >/dev/null
printf 'bodhisattva tower: accepted by OCaml megalodon, mg_tcalc (its gate report is printed above), dk_tcalc, Kontroli and dk check --type-lhs\n'

# Datalog (D0) and CHR (C0/C1) on tcalc
./dl_tcalc --self-test > "$WORK/dl_selftest.out" || { grep -v '^PASS' "$WORK/dl_selftest.out" | tail -40; exit 1; }
printf 'dl_tcalc self-test: %s\n' "$(tail -1 "$WORK/dl_selftest.out")"
SOUFFLE_BIN="${SOUFFLE_BIN:-}"
if [ -z "$SOUFFLE_BIN" ]; then
  SOUFFLE_BIN="$(command -v souffle || true)"
fi
# norm_dl: one line "RELATION<TAB>TUPLE" per printed tuple, sorted; reads the relations as
# both dl_tcalc and `souffle -D -` print them (Souffle adds a line of attribute names).
norm_dl() {
  awk '/^-+$/ { state = 1; next }
       /^=+$/ { state = (state == 2) ? 3 : 2; next }
       state == 1 { rel = $0; state = 4; next }
       state == 4 { next }
       state == 2 { print rel "\t" $0 }' | LC_ALL=C sort
}
if [ -n "$SOUFFLE_BIN" ]; then
  d0_same=0
  for c in tests/datalog/basic tests/datalog/boundaries tests/datalog/nonlinear_closure tests/datalog/same_generation \
           module/gold/SouffleDatalog/examples/cyclic_graph module/gold/SouffleDatalog/examples/points_to; do
    if [ -d "$DL_TESTS/$c" ]; then
      ./dl_tcalc --facts-dir "$DL_TESTS/$c" "$DL_TESTS/$c.dl" | norm_dl > "$WORK/d0.tcalc"
      "$SOUFFLE_BIN" -F "$DL_TESTS/$c" -D - "$DL_TESTS/$c.dl" 2>/dev/null | norm_dl > "$WORK/d0.souffle"
    else
      ./dl_tcalc "$DL_TESTS/$c.dl" | norm_dl > "$WORK/d0.tcalc"
      "$SOUFFLE_BIN" -D - "$DL_TESTS/$c.dl" 2>/dev/null | norm_dl > "$WORK/d0.souffle"
    fi
    [ -s "$WORK/d0.souffle" ] && cmp -s "$WORK/d0.tcalc" "$WORK/d0.souffle" || { echo "DL_TCALC DIFFERS FROM SOUFFLE ON $c"; exit 1; }
    d0_same=$((d0_same + 1))
  done
  # Negative control of the comparison: one fact less on Souffle's side (the only Pair that
  # gives a Same tuple) must show.
  grep -v '^Pair(1,1)\.$' "$DL_TESTS/tests/datalog/basic.dl" > "$WORK/basic_minus_fact.dl"
  ./dl_tcalc "$DL_TESTS/tests/datalog/basic.dl" | norm_dl > "$WORK/d0.tcalc"
  "$SOUFFLE_BIN" -D - "$WORK/basic_minus_fact.dl" 2>/dev/null | norm_dl > "$WORK/d0.souffle"
  ! cmp -s "$WORK/d0.tcalc" "$WORK/d0.souffle" || { echo "THE D0 COMPARISON DOES NOT SEE A CHANGED PROGRAM"; exit 1; }
  printf 'dl_tcalc D0 programs: %d/6 print the same tuples as Souffle (the comparison catches a removed fact)\n' "$d0_same"
else
  echo 'dl_tcalc D0 programs against Souffle: NOT RUN (set SOUFFLE_BIN)'
fi
SWIPL_BIN="${SWIPL_BIN:-$(command -v swipl || true)}"
if [ -n "$SWIPL_BIN" ]; then
  mkdir -p "$WORK/chr"
  sh dl-controls/chr_against_swi.sh "$PWD/dl_tcalc" "$SWIPL_BIN" "$DL_TESTS" "$WORK/chr"
else
  echo 'dl_tcalc CHR programs against SWI-Prolog: NOT RUN (set SWIPL_BIN)'
fi
check_flat_bytes dl_tcalc
# The self-test again under the address and undefined-behaviour sanitizers, and under the
# thread sanitizer (the parallel CHR mode runs threads), built into the scratch directory.
# Both reserve terabytes of address space, so they cannot run under a `ulimit -v` cap.
if [ "$(ulimit -v)" = unlimited ]; then
  for san in address,undefined thread; do
    ${CC:-gcc} -O1 -g -fno-omit-frame-pointer -fsanitize=$san -fno-sanitize-recover=all -std=c11 -Wall -Wextra -Werror -pthread \
      -DTC_ORDINARY_FLAT_TEST_HOOKS tcalc.c "$FLAT_RUNTIME" bridge/tc_cetta_bridge.c dl_tcalc.c -o "$WORK/dl_tcalc_san"
    ASAN_OPTIONS=detect_leaks=1 "$WORK/dl_tcalc_san" --self-test > "$WORK/dl_san.out" 2>&1 || { grep -v '^PASS' "$WORK/dl_san.out" | tail -40; exit 1; }
    ! grep -q 'runtime error\|ERROR: AddressSanitizer\|WARNING: ThreadSanitizer' "$WORK/dl_san.out" || { grep -m5 'runtime error\|Sanitizer' "$WORK/dl_san.out"; exit 1; }
    printf 'dl_tcalc self-test under -fsanitize=%s: %s\n' "$san" "$(tail -1 "$WORK/dl_san.out")"
  done
  rm -f "$WORK/dl_tcalc_san"
else
  echo "dl_tcalc self-test under the sanitizers: NOT RUN (the address space is capped: ulimit -v $(ulimit -v))"
fi

# t-ISA and the Lean 4 checker.  test_tisa writes the program manifests it computes (v1, and the
# p1 manifest v2) into the scratch directory, the only place this script lets it write them, and
# each must reproduce the stored manifest byte for byte.
tree=$PWD
mkdir -p "$WORK/tisa/manifests"
(cd "$WORK" && TISA_WRITE_MANIFESTS=1 TISA_WRITE_P1_MANIFEST=1 "$tree/test_tisa" > test_tisa.out) || { tail -40 "$WORK/test_tisa.out"; exit 1; }
tail -1 "$WORK/test_tisa.out"
for m in tisa_x86_programs_v1.json tisa_x86_p1_programs_v2.json; do
  cmp -s "$WORK/tisa/manifests/$m" "tisa/manifests/$m" || { echo "test_tisa no longer reproduces tisa/manifests/$m"; exit 1; }
done
./lean_tcalc --selftest > "$WORK/lean_selftest.out" || { tail -40 "$WORK/lean_selftest.out"; exit 1; }
printf 'lean_tcalc self-test: %s\n' "$(tail -1 "$WORK/lean_selftest.out")"

# Cesta checked-c/1 + native-c/1 ownership check-all + differential gate
make -s cesta-check
for bin in test_tcalc_cesta test_cetta_bridge_cesta dk_tcalc_cesta mg_tcalc_cesta dl_tcalc_cesta lean_tcalc_cesta; do
  check_flat_bytes "$bin"
done
rm -f test_tcalc_cesta test_cetta_bridge_cesta dk_tcalc_cesta mg_tcalc_cesta dl_tcalc_cesta lean_tcalc_cesta

./diff_micromath
check_flat_bytes diff_micromath
for bin in mm0_tcalc mmb_tcalc hol_tcalc mg_tcalc dk_tcalc lean_tcalc; do
  check_flat_bytes "$bin"
done

# Adversarial controls with independent oracles (hol policy, probe and deep-term streams; mg
# definitions and integers; dk matching profiles, directives, modules, widths and memory; mm0
# proof files; dl capacity; lean recursors, quotients and wide declarations).
# LEAN_ORACLE is the official Lean 4 kernel replay of lean4export NDJSON and LEAN_SAN a
# sanitizer build of lean_tcalc, when available; a missing one is reported as NOT RUN.
# The script changes directory to run some oracles, so every program is passed by absolute path.
abs() { [ -n "$1" ] && realpath "$1" || true; }
mkdir -p "$WORK/adversarial"
HOLR_SAMPLE="$(abs "$HOL_DIR/core.holr")" MG_BIN="$(abs "$MG_BIN")" DK_BIN="$(abs "$DK_BIN")" \
  SOUFFLE_BIN="$(abs "$SOUFFLE_BIN")" LEAN_ORACLE="$(abs "${LEAN_ORACLE:-}")" LEAN_SAN="$(abs "${LEAN_SAN:-}")" \
  sh ./adversarial_controls.sh . "$WORK/adversarial"

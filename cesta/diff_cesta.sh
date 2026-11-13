#!/bin/sh
# Cesta differential verification gate for tcalc (Track 5):
# 1. Verifies cesta/tc_scanner.cesta (checked-c/1) and cesta/tc_bridge.cesta (native-c/1 ownership check-all)
#    plus compiled/micromath_{leaf,compiled}.cesta via ../cesta/build/cesta.
# 2. Exports cesta/tc_scanner.export.{h,c} and cesta/tc_bridge.export.c.
# 3. Builds test_tcalc_cesta, dk_tcalc_cesta, and mg_tcalc_cesta with -DTC_USE_CESTA_EXPORT
#    (replacing baseline hash_bytes / skip_ws / lex_skip_ws_comments / tc_commit_prepared / tc_step_cursor).
# 4. Differential-tests Cesta-exported binaries against baseline C binaries on the run.sh corpus,
#    requiring identical exit codes and identical normalized outputs.
set -eu
cd "$(dirname "$0")/.."

CESTA="${CESTA:-../cesta/build/cesta}"
CC="${CC:-gcc}"
CFLAGS="${CFLAGS:--O3 -march=native -fno-tree-vectorize -fno-tree-loop-distribute-patterns -flto -Wall -Wextra -Werror}"
MG_EGAL="${MG_EGAL:-}"  # optional: a directory with Part1-3.sexpr; that comparison is skipped without it
if [ -z "${DK_CURR:-}" ]; then if [ -d ../Mettapedia/MettaKernel/Curriculum/DeduktiLambdapi ]; then DK_CURR=../Mettapedia/MettaKernel/Curriculum/DeduktiLambdapi; else DK_CURR=../../Mettapedia/MettaKernel/Curriculum/DeduktiLambdapi; fi; fi

echo "=== Track 5: Cesta Check, Export & Differential Gate ==="
"$CESTA" checked check cesta/tc_scanner.cesta
"$CESTA" checked header cesta/tc_scanner.cesta -o cesta/tc_scanner.export.h
"$CESTA" export-c cesta/tc_scanner.cesta -o cesta/tc_scanner.export.c --

"$CESTA" checked check cesta/tc_lean_guard.cesta
"$CESTA" checked header cesta/tc_lean_guard.cesta -o cesta/tc_lean_guard.export.h
"$CESTA" export-c cesta/tc_lean_guard.cesta -o cesta/tc_lean_guard.export.c --

"$CESTA" cc --cc "$CC" -std=c11 -I. -fsyntax-only cesta/tc_bridge.cesta
"$CESTA" export-c cesta/tc_bridge.cesta --std=c11 --cc "$CC" -o cesta/tc_bridge.export.c -- -I.

"$CESTA" cc --cc "$CC" -std=c11 -I. -fsyntax-only cesta/tc_event_view.cesta
"$CESTA" export-c cesta/tc_event_view.cesta --std=c11 --cc "$CC" -o cesta/tc_event_view.export.c -- -I.

"$CESTA" cc --cc "$CC" -std=c11 -I. -fsyntax-only cesta/tc_recorded_cursor.cesta
"$CESTA" export-c cesta/tc_recorded_cursor.cesta --std=c11 --cc "$CC" -o cesta/tc_recorded_cursor.export.c -- -I.

"$CESTA" cc --cc "$CC" -I. -Icompiled -fsyntax-only compiled/micromath_leaf.cesta
"$CESTA" cc --cc "$CC" -I. -Icompiled -fsyntax-only compiled/micromath_compiled.cesta

make -s test_tcalc test_cetta_bridge dk_tcalc mg_tcalc dl_tcalc lean_tcalc test_tcalc_cesta test_cetta_bridge_cesta dk_tcalc_cesta mg_tcalc_cesta dl_tcalc_cesta lean_tcalc_cesta

norm_out() {
  sed -E 's/\([0-9]+\.[0-9]+ ms\)/(TIME ms)/g; s/[0-9]+\.[0-9]+ ms/TIME ms/g; s/\([0-9]+\.[0-9]+ us\)/(TIME us)/g; s/Speedup: [0-9]+\.[0-9]+x/Speedup: SPEEDUPx/g'
}

diff_pair() {
  label="$1"
  expect_rc="$2"
  shift 2
  bin_base="$1"
  bin_cesta="$2"
  shift 2

  set +e
  out_base=$("$bin_base" "$@" 2>&1)
  rc_base=$?
  out_cesta=$("$bin_cesta" "$@" 2>&1)
  rc_cesta=$?
  set -e

  if [ "$rc_base" -ne "$expect_rc" ] || [ "$rc_cesta" -ne "$expect_rc" ]; then
    echo "FAIL [cesta-diff]: $label exit code mismatch (base=$rc_base, cesta=$rc_cesta, expected=$expect_rc)" >&2
    exit 1
  fi

  n_base=$(printf '%s\n' "$out_base" | norm_out)
  n_cesta=$(printf '%s\n' "$out_cesta" | norm_out)
  if [ "$n_base" != "$n_cesta" ]; then
    echo "FAIL [cesta-diff]: $label output mismatch between $bin_base and $bin_cesta" >&2
    echo "--- base ---" >&2
    printf '%s\n' "$n_base" >&2
    echo "--- cesta ---" >&2
    printf '%s\n' "$n_cesta" >&2
    exit 1
  fi
}

pos_pairs=0
neg_pairs=0

for mode in plain eta; do
  if [ "$mode" = eta ]; then eta_flag=--eta; else eta_flag=--no-eta; fi
  diff_pair "beta conversion $mode" 0 ./dk_tcalc ./dk_tcalc_cesta "$eta_flag" dk-controls/profiles/beta_only.dk
  pos_pairs=$((pos_pairs + 1))
  if [ "$mode" = eta ]; then expected=0; else expected=1; fi
  diff_pair "eta profile $mode" "$expected" ./dk_tcalc ./dk_tcalc_cesta "$eta_flag" dk-controls/profiles/eta_required.dk
  if [ "$expected" = 0 ]; then pos_pairs=$((pos_pairs + 1)); else neg_pairs=$((neg_pairs + 1)); fi
  diff_pair "wrong eta $mode" 1 ./dk_tcalc ./dk_tcalc_cesta "$eta_flag" dk-controls/profiles/eta_wrong.dk
  neg_pairs=$((neg_pairs + 1))
done
for name in checked_proof repeated_definition missing_proof unpaired_qed redefined duplicate_proof; do
  case "$name" in checked_proof|repeated_definition) expected=0 ;; *) expected=1 ;; esac
  diff_pair "proof article $name" "$expected" ./mg_tcalc ./mg_tcalc_cesta "mg-controls/admission/$name.sexpr"
  if [ "$expected" = 0 ]; then pos_pairs=$((pos_pairs + 1)); else neg_pairs=$((neg_pairs + 1)); fi
done

# 1. test_tcalc & test_cetta_bridge vs Cesta-exported twins
diff_pair "test_tcalc" 0 ./test_tcalc ./test_tcalc_cesta
pos_pairs=$((pos_pairs + 1))

diff_pair "test_cetta_bridge" 0 ./test_cetta_bridge ./test_cetta_bridge_cesta
pos_pairs=$((pos_pairs + 1))

diff_pair "dl_tcalc --self-test" 0 ./dl_tcalc ./dl_tcalc_cesta --self-test
pos_pairs=$((pos_pairs + 1))

diff_pair "lean_tcalc --selftest" 0 ./lean_tcalc ./lean_tcalc_cesta --selftest
pos_pairs=$((pos_pairs + 1))

# 2. dk_tcalc vs dk_tcalc_cesta (self-test + p01..p07 + 26 dk-bridge + theories + n01..n17)
diff_pair "dk_tcalc --self-test" 0 ./dk_tcalc ./dk_tcalc_cesta --self-test "$DK_CURR/10_kernel_curriculum_lf_positive.dk"
pos_pairs=$((pos_pairs + 1))

diff_pair "dk_tcalc --pts cc curriculum" 0 ./dk_tcalc ./dk_tcalc_cesta --pts cc "$DK_CURR/10_kernel_curriculum_positive.dk"
pos_pairs=$((pos_pairs + 1))

for f in dk-controls/p*.dk dk-bridge/*.dk tower/sttfa_hotg_base.dk tower/bodhisattva_tower.dk \
         ../repos/dedukti/libraries/theories/*.dk; do
  diff_pair "dk valid $(basename "$f")" 0 ./dk_tcalc ./dk_tcalc_cesta --pts lf "$f"
  pos_pairs=$((pos_pairs + 1))
done

for f in dk-controls/n*.dk; do
  diff_pair "dk wrong $(basename "$f")" 1 ./dk_tcalc ./dk_tcalc_cesta --pts lf "$f"
  neg_pairs=$((neg_pairs + 1))
done

for f in "$DK_CURR"/neg_kernel_*.dk; do
  diff_pair "dk neg_kernel $(basename "$f")" 1 ./dk_tcalc ./dk_tcalc_cesta --pts cc "$f"
  neg_pairs=$((neg_pairs + 1))
done

# 3. mg_tcalc vs mg_tcalc_cesta (self-test + bodhisattva + 20 baselines + UpToOctonions Part1..3 + 100 mutants)
diff_pair "mg_tcalc --self-test" 0 ./mg_tcalc ./mg_tcalc_cesta --self-test
pos_pairs=$((pos_pairs + 1))

diff_pair "mg_tcalc bodhisattva_tower" 0 ./mg_tcalc ./mg_tcalc_cesta tower/bodhisattva_tower.sexpr --bodhisattva-gate
pos_pairs=$((pos_pairs + 1))

for f in mg-controls/mutants/baseline_sexpr/*.sexpr; do
  diff_pair "mg baseline $(basename "$f")" 0 ./mg_tcalc ./mg_tcalc_cesta "$f"
  pos_pairs=$((pos_pairs + 1))
done

if [ -f "$MG_EGAL/Part1.sexpr" ]; then
  diff_pair "mg_tcalc UpToOctonions Part1..3" 0 ./mg_tcalc ./mg_tcalc_cesta --chain \
    "$MG_EGAL/Part1.sexpr" "$MG_EGAL/Part2.sexpr" "$MG_EGAL/Part3.sexpr"
  pos_pairs=$((pos_pairs + 1))
fi

for f in mg-controls/mutants/sexpr/*.sexpr; do
  diff_pair "mg mutant $(basename "$f")" 1 ./mg_tcalc ./mg_tcalc_cesta "$f"
  neg_pairs=$((neg_pairs + 1))
done

echo "cesta-check differential gate: $pos_pairs/$pos_pairs positive pairs and $neg_pairs/$neg_pairs negative pairs matched 100% (oracle: baseline C vs Cesta export-c)"

#!/bin/sh
# Random differentials of the tcalc kernel against naive references (tree terms, brute-force matching).
#   differential/diff_main.c: takes, keeps, tells, disequations, absent, count, fresh names, extra makes,
#     static spaces 0..3, protection and sealing, five firing entry points (ref.h is its reference);
#   differential/diff_loc.c: located premises, dynamic spaces, births and reach, seven entry points;
#   differential/diff_lemma.c: lemma checking (steps, installation) and firing the installed lemmas;
#   differential/diff_bind.c: bound holes, dependency declarations and separation guards;
#   differential/diff_conv.c: conversions (CV_REFL, CV_SYM, CV_CONG, CV_UNFOLD over tc_def) and the rho law;
#   differential/diff_tell.c: open tells and disequations, facts holding unknowns, caller tells.
#
#   sh kernel-controls/run_differential.sh BUILD_DIR [KERNEL_C] [SEEDS]
#
# Builds both drivers against KERNEL_C (default: the tcalc.c next to this directory) into BUILD_DIR,
# which must lie outside the tree, and runs SEEDS scenarios of each (default 20000). A disagreement is
# printed shrunk (diff_main) or with its rule and operands (diff_loc); the exit status is 1 if any.
set -u
here=$(cd "$(dirname "$0")" && pwd)
tree=$(dirname "$here")
[ $# -ge 1 ] || { echo "usage: sh $0 BUILD_DIR [KERNEL_C] [SEEDS]"; exit 2; }
parent=$(cd "$(dirname "$1")" 2>/dev/null && pwd) || { echo "the parent of BUILD_DIR must exist"; exit 2; }
bdir=$parent/$(basename "$1")
case "$bdir/" in "$tree"/*) echo "BUILD_DIR must lie outside $tree"; exit 2 ;; esac
mkdir -p "$bdir" || exit 2
kc=${2:-$tree/tcalc.c}
seeds=${3:-20000}
rt=$tree/compiled/ordinary_flat_cesta_runtime.o
flags="-O3 -march=native -fno-tree-vectorize -fno-tree-loop-distribute-patterns -flto -w"
st=0
for d in diff_main diff_loc diff_lemma diff_bind diff_conv diff_tell; do
  ${CC:-gcc} $flags -I"$tree" -I"$here/differential" "$kc" "$here/differential/$d.c" "$rt" -o "$bdir/$d" 2> "$bdir/$d.build.log" || { echo "NO BUILD $d (see $bdir/$d.build.log)"; st=2; continue; }
done
[ $st -eq 0 ] || exit $st
"$bdir/diff_main" 1 "$seeds" --future 0.05 > "$bdir/diff_main.log" 2>&1 || st=1
grep -E "^summary|scenarios ended|^DISAGREEMENT" "$bdir/diff_main.log" | head -20
"$bdir/diff_loc" 1 "$seeds" > "$bdir/diff_loc.log" 2>&1 || st=1
grep -E "^summary|DISAGREEMENT|^seed" "$bdir/diff_loc.log" | head -20
"$bdir/diff_lemma" 1 "$seeds" > "$bdir/diff_lemma.log" 2>&1 || st=1
grep -E "^summary|DISAGREEMENT|^seed" "$bdir/diff_lemma.log" | head -20
"$bdir/diff_bind" 1 "$seeds" > "$bdir/diff_bind.log" 2>&1 || st=1
grep -E "^summary|DISAGREEMENT" "$bdir/diff_bind.log" | head -20
"$bdir/diff_conv" 1 "$seeds" > "$bdir/diff_conv.log" 2>&1 || st=1
grep -E "^summary|DISAGREEMENT|UNSOUND" "$bdir/diff_conv.log" | head -20
"$bdir/diff_tell" 1 "$seeds" > "$bdir/diff_tell.log" 2>&1 || st=1
grep -E "^summary|DISAGREEMENT" "$bdir/diff_tell.log" | head -20
exit $st

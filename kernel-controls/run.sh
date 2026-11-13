#!/bin/sh
# Kernel controls: one small C program per guarantee of the tcalc kernel.
# Each exits 0 when the guarantee holds, 1 when it is violated, 2 when its scene could not be set up.
#
#   sh kernel-controls/run.sh BUILD_DIR [KERNEL_C] [repo|san]
#
# Builds every control against KERNEL_C (default: the tcalc.c next to this directory) into BUILD_DIR,
# which must lie outside the tree, and runs them. "repo" uses the repository's compiler flags, "san"
# the address and undefined-behaviour sanitizers (k25 and k31 cap the address space and run in repo mode only).
set -u
here=$(cd "$(dirname "$0")" && pwd)
tree=$(dirname "$here")
[ $# -ge 1 ] || { echo "usage: sh $0 BUILD_DIR [KERNEL_C] [repo|san]"; exit 2; }
parent=$(cd "$(dirname "$1")" 2>/dev/null && pwd) || { echo "the parent of BUILD_DIR must exist"; exit 2; }
bdir=$parent/$(basename "$1")
case "$bdir/" in "$tree"/*) echo "BUILD_DIR must lie outside $tree"; exit 2 ;; esac
mkdir -p "$bdir" || exit 2
kc=${2:-$tree/tcalc.c}
mode=${3:-repo}
case "$mode" in
  repo) flags="-O3 -march=native -fno-tree-vectorize -fno-tree-loop-distribute-patterns -flto -w" ;;
  san)  flags="-O1 -g -march=native -fno-omit-frame-pointer -fsanitize=address,undefined -fno-sanitize-recover=undefined -w" ;;
  *) echo "unknown mode $mode"; exit 2 ;;
esac
rt=$tree/compiled/ordinary_flat_cesta_runtime.o
[ -f "$rt" ] || { echo "missing $rt (run the tree's build first)"; exit 2; }
ok=0; viol=0; nov=0
for src in "$here"/k*.c; do
  name=$(basename "$src" .c)
  case "$mode:$name" in san:k25_rollback_set_store|san:k31_hash_growth_failure) echo "not run   $name (repo mode only)"; continue ;; esac
  if ! ${CC:-gcc} $flags -I"$tree" -I"$here" "$kc" "$src" "$rt" -o "$bdir/$name" 2> "$bdir/$name.build.log"; then
    echo "NO BUILD  $name (see $bdir/$name.build.log)"; nov=$((nov + 1)); continue
  fi
  ASAN_OPTIONS=${ASAN_OPTIONS:-detect_leaks=0} timeout 300 "$bdir/$name" > "$bdir/$name.out" 2> "$bdir/$name.err"
  st=$?
  case $st in
    0) echo "holds     $name"; ok=$((ok + 1)) ;;
    1) echo "VIOLATED  $name (see $bdir/$name.out)"; viol=$((viol + 1)) ;;
    2) echo "NO VERDICT $name (setup, see $bdir/$name.out)"; nov=$((nov + 1)) ;;
    *) echo "VIOLATED  $name (exit $st: crash or sanitizer report, see $bdir/$name.err)"; viol=$((viol + 1)) ;;
  esac
done
echo "kernel controls: $ok hold, $viol violated, $nov without verdict (kernel $kc, mode $mode)"
[ $viol -gt 0 ] && exit 1
[ $nov -gt 0 ] && exit 2
exit 0

#!/bin/sh
# Single-edit mutants of a .mmu file, judged by mm0_ref and by another checker (the tree's
# mm0_tcalc, an independent implementation): every mutant must get the same accept/refuse verdict.
# Disagreements are printed with the edit; they are bugs in one checker or the other.
#   usage: diff_mutants.sh MM0_REF OTHER BASE.mmu FIRST_SEED COUNT WORKDIR
set -u
BIN=$1 OTHER=$2 BASE=$3 FIRST=$4 COUNT=$5 W=$6
mkdir -p "$W"
MUT=$(dirname "$BIN")/mutate_mmu
agree=0 disagree=0 bothok=0 bothrefuse=0 mine_nv=0
s=$FIRST
while [ "$s" -lt $((FIRST + COUNT)) ]; do
  edit=$("$MUT" "$s" < "$BASE" 2>&1 > "$W/m.mmu")
  "$BIN" "$W/m.mmu" --proof-only > "$W/a.out" 2>&1; a=$?
  "$OTHER" "$W/m.mmu" --proof-only > "$W/b.out" 2>&1; b=$?
  [ "$a" -eq 2 ] && mine_nv=$((mine_nv + 1))
  if { [ "$a" -eq 0 ] && [ "$b" -eq 0 ]; } || { [ "$a" -ne 0 ] && [ "$b" -ne 0 ]; }; then
    agree=$((agree + 1))
    [ "$a" -eq 0 ] && bothok=$((bothok + 1)) || bothrefuse=$((bothrefuse + 1))
  else
    disagree=$((disagree + 1))
    echo "seed $s ($edit): mm0_ref exit $a: $(head -c 200 "$W/a.out" | tr '\n' ' ') | other exit $b: $(head -c 200 "$W/b.out" | tr '\n' ' ')"
    [ "$disagree" -le 20 ] && cp "$W/m.mmu" "$W/disagree-$s.mmu" # the first few, to read; mutate_mmu SEED remakes any
  fi
  s=$((s + 1))
done
rm -f "$W/m.mmu" "$W/a.out" "$W/b.out"
echo "mutants $COUNT: agree $agree (both accept $bothok, both refuse $bothrefuse), disagree $disagree; mm0_ref no verdict $mine_nv"

#!/bin/sh
# Field-mutation differential on the inductive blocks of lean4export NDJSON files.
#
# usage: mutate_inductive.sh LEAN_TCALC OFFICIAL_KERNEL WORKDIR FILE.ndjson...
#
# Every FILE must be accepted by both checkers.  For each `{"inductive":...}` line and
# each mutation below, one field of the block is changed, and both checkers run on
# the mutant.  The official kernel derives constructors' and recursors' data from the
# inductive types itself and compares the export with what it derived, so it is the
# oracle for "this field matters".
#
#   ACCEPT-BAD   the checker accepts a mutant the official kernel refuses
#   REJECT-GOOD  the checker refuses a mutant the official kernel accepts
#
# Mutations (the first matching occurrence in the line):
#   rec-k            flip the recursor's k flag
#   rec-minors       recursor numMinors + 1
#   rec-motives      recursor numMotives + 1
#   rec-indices      recursor numIndices + 1
#   rec-params       recursor numParams + 1
#   rec-type         recursor type index - 1
#   rule-nfields     first rule's nfields + 1
#   rule-rhs         first rule's rhs index - 1
#   ctor-cidx        first constructor's cidx + 1
#   ctor-fields      first constructor's numFields + 1
#   ctor-params      first constructor's numParams + 1
#   type-indices     first type's numIndices + 1
#   type-params      first type's numParams + 1
#   type-rec         flip the first type's isRec
#   type-reflexive   flip the first type's isReflexive
#   type-nested      first type's numNested + 1
set -u
BIN=$1; ORACLE=$2; WORK=$3; shift 3
ulimit -c 0
total=0; agree_rej=0; agree_acc=0; acc_bad=0; rej_good=0; other=0; skipped=0

bump() { # LINE REGEX-PREFIX DELTA -> prints the sed program, or nothing if no match
  line=$1; pre=$2; delta=$3
  old=$(printf '%s\n' "$line" | grep -o "${pre}[0-9][0-9]*" | head -1 | grep -o '[0-9][0-9]*$')
  [ -n "$old" ] || return 1
  new=$((old + delta))
  [ "$new" -ge 0 ] || return 1
  printf 's/\\(%s\\)%s/\\1%s/' "$pre" "$old" "$new"
}

flip() { # LINE REGEX-PREFIX -> sed program flipping the first boolean after the prefix
  line=$1; pre=$2
  old=$(printf '%s\n' "$line" | grep -o "${pre}\(true\|false\)" | head -1 | grep -o '\(true\|false\)$')
  [ -n "$old" ] || return 1
  if [ "$old" = true ]; then new=false; else new=true; fi
  printf 's/\\(%s\\)%s/\\1%s/' "$pre" "$old" "$new"
}

run_mutant() { # FILE LINENO KIND SEDPROG
  f=$1; ln=$2; kind=$3; prog=$4
  sed "${ln}${prog}" "$f" > "$WORK/mutant.ndjson"
  if cmp -s "$f" "$WORK/mutant.ndjson"; then skipped=$((skipped+1)); return; fi
  ( timeout 60 "$BIN" "$WORK/mutant.ndjson" >/dev/null 2>&1 ); rc=$?
  timeout 120 "$ORACLE" "$WORK/mutant.ndjson" >/dev/null 2>&1; orc=$?
  total=$((total+1))
  if [ "$rc" -eq 0 ] && [ "$orc" -eq 0 ]; then agree_acc=$((agree_acc+1))
  elif [ "$rc" -eq 1 ] && [ "$orc" -ne 0 ]; then agree_rej=$((agree_rej+1))
  elif [ "$rc" -eq 0 ]; then acc_bad=$((acc_bad+1)); echo "ACCEPT-BAD $kind line=$ln $(basename "$f")"
  elif [ "$rc" -eq 1 ]; then rej_good=$((rej_good+1)); echo "REJECT-GOOD $kind line=$ln $(basename "$f")"
  else other=$((other+1)); echo "OTHER rc=$rc oracle_rc=$orc $kind line=$ln $(basename "$f")"
  fi
}

for f in "$@"; do
  "$BIN" "$f" >/dev/null 2>&1 || { echo "BASELINE-NOT-ACCEPTED-BY-CHECKER $(basename "$f")"; continue; }
  "$ORACLE" "$f" >/dev/null 2>&1 || { echo "BASELINE-NOT-ACCEPTED-BY-ORACLE $(basename "$f")"; continue; }
  for ln in $(grep -n '^{"inductive":' "$f" | cut -d: -f1 | head -${MAX_BLOCKS:-4}); do
    line=$(sed -n "${ln}p" "$f")
    p=$(flip "$line" '"k":') && run_mutant "$f" "$ln" rec-k "$p"
    p=$(bump "$line" '"numMinors":' 1) && run_mutant "$f" "$ln" rec-minors "$p"
    p=$(bump "$line" '"numMotives":' 1) && run_mutant "$f" "$ln" rec-motives "$p"
    p=$(bump "$line" '"k":\(true\|false\),"levelParams":\[[0-9,]*\],"name":[0-9]*,"numIndices":' 1) && run_mutant "$f" "$ln" rec-indices "$p"
    p=$(bump "$line" '"numMotives":[0-9]*,"numParams":' 1) && run_mutant "$f" "$ln" rec-params "$p"
    p=$(bump "$line" '"rules":\[[^]]*\],"type":' -1) && run_mutant "$f" "$ln" rec-type "$p"
    p=$(bump "$line" '"nfields":' 1) && run_mutant "$f" "$ln" rule-nfields "$p"
    p=$(bump "$line" '"rhs":' -1) && run_mutant "$f" "$ln" rule-rhs "$p"
    p=$(bump "$line" '"cidx":' 1) && run_mutant "$f" "$ln" ctor-cidx "$p"
    p=$(bump "$line" '"numFields":' 1) && run_mutant "$f" "$ln" ctor-fields "$p"
    p=$(bump "$line" '"numFields":[0-9]*,"numParams":' 1) && run_mutant "$f" "$ln" ctor-params "$p"
    p=$(bump "$line" '"isUnsafe":\(true\|false\),"levelParams":\[[0-9,]*\],"name":[0-9]*,"numIndices":' 1) && run_mutant "$f" "$ln" type-indices "$p"
    p=$(bump "$line" '"numNested":[0-9]*,"numParams":' 1) && run_mutant "$f" "$ln" type-params "$p"
    p=$(flip "$line" '"isRec":') && run_mutant "$f" "$ln" type-rec "$p"
    p=$(flip "$line" '"isReflexive":') && run_mutant "$f" "$ln" type-reflexive "$p"
    p=$(bump "$line" '"numNested":' 1) && run_mutant "$f" "$ln" type-nested "$p"
  done
done
rm -f "$WORK/mutant.ndjson"
echo "SUMMARY mutants=$total both-reject=$agree_rej both-accept=$agree_acc accept-bad=$acc_bad reject-good=$rej_good other=$other unchanged-skipped=$skipped"

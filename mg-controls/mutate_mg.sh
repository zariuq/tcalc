#!/bin/sh
# Index-mutation differential for mg_tcalc, with Dedukti as the independent judge.
#
# usage: mutate_mg.sh MG_TCALC DK_ORACLE WORKDIR FILE.sexpr...
#
# Every FILE must be accepted by mg_tcalc and its `--emit-dk` translation by dk.
# A mutant adds one to one index, `(HYP n)` or `(DB n)`, at one occurrence in a THM or
# PROOF form (KIND selects hyp or db; STRIDE and OFFSET select the occurrences;
# MAX_PER_FILE bounds them).  mg_tcalc runs on the mutant.  When it accepts, the
# mutant's translation goes to `dk check --type-lhs`:
#   ACCEPT-BAD     mg_tcalc accepts a mutant whose translation dk refuses
#   ACCEPT-AGREED  mg_tcalc accepts and dk accepts the translation (the mutant is still a proof,
#                  usually of a different statement)
set -u
MG=$1; DK=$2; WORK=$3; shift 3
KIND=${KIND:-hyp}; STRIDE=${STRIDE:-1}; OFFSET=${OFFSET:-0}; MAXF=${MAX_PER_FILE:-200}
case "$KIND" in hyp) TAG=HYP ;; *) TAG=DB ;; esac
ulimit -c 0
total=0; refused=0; agreed=0; acc_bad=0; other=0
for f in "$@"; do
  base=$(basename "$f" .sexpr)
  "$MG" --emit-dk "$WORK/base_$base.dk" "$f" >/dev/null 2>&1 || { echo "BASELINE-NOT-ACCEPTED-BY-CHECKER $base"; continue; }
  ( cd "$WORK" && "$DK" check --type-lhs "base_$base.dk" >/dev/null 2>&1 ) || { echo "BASELINE-TRANSLATION-NOT-ACCEPTED-BY-ORACLE $base"; continue; }
  rm -f "$WORK/base_$base.dk"
  nocc=$(grep -E '^\((THM|PROOF) ' "$f" | grep -o "($TAG [0-9][0-9]*)" | wc -l)
  i=0; nfile=0
  while [ "$i" -lt "$nocc" ] && [ "$nfile" -lt "$MAXF" ]; do
    i=$((i + 1))
    [ $((i % STRIDE)) -eq "$OFFSET" ] || continue
    awk -v want="$i" -v tag="$TAG" '
      !/^\((THM|PROOF) / { print; next }
      {
        line = $0; out = ""; pat = "\\(" tag " [0-9]+\\)"
        while (match(line, pat)) {
          seen++
          tok = substr(line, RSTART, RLENGTH)
          if (seen == want) {
            num = tok; sub("^\\(" tag " ", "", num); sub("\\)$", "", num)
            tok = "(" tag " " (num + 1) ")"
          }
          out = out substr(line, 1, RSTART - 1) tok
          line = substr(line, RSTART + RLENGTH)
        }
        print out line
      }' "$f" > "$WORK/mutant.sexpr"
    total=$((total+1)); nfile=$((nfile+1))
    ( timeout 60 "$MG" --emit-dk "$WORK/mutant_$base.dk" "$WORK/mutant.sexpr" >/dev/null 2>&1 ); rc=$?
    if [ "$rc" -eq 1 ]; then refused=$((refused+1))
    elif [ "$rc" -eq 0 ]; then
      if ( cd "$WORK" && timeout 120 "$DK" check --type-lhs "mutant_$base.dk" >/dev/null 2>&1 ); then agreed=$((agreed+1))
      else acc_bad=$((acc_bad+1)); echo "ACCEPT-BAD $TAG occurrence=$i $base"; cp "$WORK/mutant.sexpr" "$WORK/accept-bad-$acc_bad-$base.sexpr"
      fi
    else other=$((other+1)); echo "OTHER rc=$rc $TAG occurrence=$i $base"
    fi
    rm -f "$WORK/mutant_$base.dk"
  done
done
rm -f "$WORK/mutant.sexpr"
echo "SUMMARY kind=$KIND mutants=$total refused=$refused accepted-and-dk-agrees=$agreed accept-bad=$acc_bad other=$other"

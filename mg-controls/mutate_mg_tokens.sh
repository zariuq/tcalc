#!/bin/sh
# Token-mutation differential for mg_tcalc, with Dedukti as the independent judge.
#
# usage: mutate_mg_tokens.sh MG_TCALC DK_ORACLE WORKDIR FILE.sexpr...
#
# Every FILE must be accepted by mg_tcalc and its `--emit-dk` translation by dk.  A mutant
# changes one token at one occurrence in a THM or PROOF form; KIND selects the change:
#   tmh           a constant (TMH "h") becomes the next distinct constant of the file
#   known         a cited lemma (KNOWN "h") becomes the next distinct cited lemma
#   set-prop      a type leaf (SET) becomes (PROP)        prop-set     the reverse
#   ptmap-ppfap   a proof applied to a term becomes a proof applied to a proof, and
#   ppfap-ptmap   the reverse
#   lam-all       an abstraction becomes a quantifier     all-lam      the reverse
#   plam-tlam     a proof abstraction over a hypothesis becomes one over a term, and
#   tlam-plam     the reverse
# STRIDE and OFFSET select the occurrences, MAX_PER_FILE bounds them.  mg_tcalc runs on the
# mutant.  When it accepts, the mutant's translation goes to `dk check --type-lhs`:
#   ACCEPT-BAD     mg_tcalc accepts a mutant whose translation dk refuses
#   accepted-and-dk-agrees   the mutant is still a proof (usually of another statement)
set -u
MG=$1; DK=$2; WORK=$3; shift 3
KIND=${KIND:-tmh}; STRIDE=${STRIDE:-1}; OFFSET=${OFFSET:-0}; MAXF=${MAX_PER_FILE:-200}
case "$KIND" in
  tmh) PAT='\(TMH "[^"]*"'; MODE=next ;;
  known) PAT='\(KNOWN "[^"]*"'; MODE=next ;;
  set-prop) PAT='\(SET\)'; TO='(PROP)'; MODE=fixed ;;
  prop-set) PAT='\(PROP\)'; TO='(SET)'; MODE=fixed ;;
  ptmap-ppfap) PAT='\(PTMAP '; TO='(PPFAP '; MODE=fixed ;;
  ppfap-ptmap) PAT='\(PPFAP '; TO='(PTMAP '; MODE=fixed ;;
  lam-all) PAT='\(LAM '; TO='(ALL '; MODE=fixed ;;
  all-lam) PAT='\(ALL '; TO='(LAM '; MODE=fixed ;;
  plam-tlam) PAT='\(PLAM '; TO='(TLAM '; MODE=fixed ;;
  tlam-plam) PAT='\(TLAM '; TO='(PLAM '; MODE=fixed ;;
  *) echo "unknown KIND $KIND" >&2; exit 2 ;;
esac
APAT=$(printf '%s' "$PAT" | sed 's/\\/\\\\/g')    # the same pattern as an awk string
ulimit -c 0
total=0; refused=0; agreed=0; acc_bad=0; other=0
for f in "$@"; do
  base=$(basename "$f" .sexpr)
  "$MG" --emit-dk "$WORK/base_$base.dk" "$f" >/dev/null 2>&1 || { echo "BASELINE-NOT-ACCEPTED-BY-CHECKER $base"; continue; }
  ( cd "$WORK" && "$DK" check --type-lhs "base_$base.dk" >/dev/null 2>&1 ) || { echo "BASELINE-TRANSLATION-NOT-ACCEPTED-BY-ORACLE $base"; continue; }
  rm -f "$WORK/base_$base.dk"
  nocc=$(grep -E '^\((THM|PROOF) ' "$f" | grep -oE "$PAT" | wc -l)
  grep -E '^\((THM|PROOF) ' "$f" | grep -oE "$PAT" | awk '!seen[$0]++' > "$WORK/distinct.txt"
  i=0; nfile=0
  while [ "$i" -lt "$nocc" ] && [ "$nfile" -lt "$MAXF" ]; do
    i=$((i + 1))
    [ $((i % STRIDE)) -eq "$OFFSET" ] || continue
    awk -v want="$i" -v pat="$APAT" -v mode="$MODE" -v to="${TO:-}" -v list="$WORK/distinct.txt" '
      BEGIN { while ((getline t < list) > 0) { n++; d[n] = t; pos[t] = n } }
      !/^\((THM|PROOF) / { print; next }
      {
        line = $0; out = ""
        while (match(line, pat)) {
          seen++
          tok = substr(line, RSTART, RLENGTH)
          if (seen == want) tok = (mode == "next") ? d[pos[tok] % n + 1] : to
          out = out substr(line, 1, RSTART - 1) tok
          line = substr(line, RSTART + RLENGTH)
        }
        print out line
      }' "$f" > "$WORK/mutant.sexpr"
    cmp -s "$f" "$WORK/mutant.sexpr" && continue
    total=$((total+1)); nfile=$((nfile+1))
    ( timeout 60 "$MG" --emit-dk "$WORK/mutant_$base.dk" "$WORK/mutant.sexpr" >/dev/null 2>&1 ); rc=$?
    if [ "$rc" -eq 1 ]; then refused=$((refused+1))
    elif [ "$rc" -eq 0 ]; then
      if ( cd "$WORK" && timeout 120 "$DK" check --type-lhs "mutant_$base.dk" >/dev/null 2>&1 ); then agreed=$((agreed+1))
      else acc_bad=$((acc_bad+1)); echo "ACCEPT-BAD $KIND occurrence=$i $base"; cp "$WORK/mutant.sexpr" "$WORK/accept-bad-$KIND-$acc_bad-$base.sexpr"
      fi
    else other=$((other+1)); echo "OTHER rc=$rc $KIND occurrence=$i $base"
    fi
    rm -f "$WORK/mutant_$base.dk"
  done
done
rm -f "$WORK/mutant.sexpr" "$WORK/distinct.txt"
echo "SUMMARY kind=$KIND mutants=$total refused=$refused accepted-and-dk-agrees=$agreed accept-bad=$acc_bad other=$other"

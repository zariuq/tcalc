#!/bin/sh
# Mutation sweep: single-edit mutants (mutate_dk) of files every checker accepts, judged by dk_ref,
# by `dk` (upstream master) and by the fixed candidate.
#
# usage: run_mutants.sh DK_REF MUTATE WORK DK DK_FIXED STRIDE FILE.dk ...
#
# Every STRIDE-th mutant of each file is checked (the mutant keeps the file's name, so its module).
#   ACCEPT-BAD      dk_ref accepts a mutant the fixed candidate refuses (a soundness question)
#   REJECT-GOOD     dk_ref refuses a mutant the fixed candidate accepts
#   NO-VERDICT      dk_ref gives no verdict
#   ORACLE-TIMEOUT  dk_ref decides, the fixed candidate does not finish in the time allowed
#   DK-MATCHER      dk_ref and the fixed candidate agree, dk master differs
# A disagreeing mutant is kept in WORK/keep/.
set -u
REF=$1; MUT=$2; W=$3; DK=$4; FIX=$5; STRIDE=$6; shift 6
mkdir -p "$W/m" "$W/keep" || exit 2
ulimit -c 0
st() { [ "$1" = 0 ] && echo 0 || echo 1; }
total=0; agree=0; accbad=0; rejgood=0; nov=0; matcher=0; skipped=0; otime=0
for f in "$@"; do
  base=$(basename "$f")
  ( timeout 60 "$REF" -q "$f" >/dev/null 2>&1 ) || { skipped=$((skipped + 1)); continue; }
  ( cd "$(dirname "$f")" && timeout 60 "$FIX" check "$base" >/dev/null 2>&1 ) || { skipped=$((skipped + 1)); continue; }
  n=$("$MUT" "$f")
  k=0
  while [ "$k" -lt "$n" ]; do
    "$MUT" "$f" "$k" > "$W/m/$base"
    total=$((total + 1))
    # a mutant can make rewriting loop or explode: a timeout is no verdict for dk_ref, and for the
    # fixed candidate its own class (ORACLE-TIMEOUT), never a refusal
    ( timeout 5 "$REF" -q "$W/m/$base" >/dev/null 2>"$W/ref.err" ); r=$?
    [ "$r" -gt 2 ] && r=2
    ( cd "$W/m" && timeout 5 "$DK" check "$base" >/dev/null 2>&1 ); m=$(st $?)
    ( cd "$W/m" && timeout 5 "$FIX" check "$base" >/dev/null 2>&1 ); xr=$?; x=$(st $xr)
    cls=""
    if [ "$r" = 2 ]; then cls=NO-VERDICT; nov=$((nov + 1))
    elif [ "$xr" = 124 ]; then cls=ORACLE-TIMEOUT; otime=$((otime + 1))
    elif [ "$r" = 0 ] && [ "$x" = 1 ]; then cls=ACCEPT-BAD; accbad=$((accbad + 1))
    elif [ "$r" = 1 ] && [ "$x" = 0 ]; then cls=REJECT-GOOD; rejgood=$((rejgood + 1))
    elif [ "$m" != "$x" ]; then cls=DK-MATCHER; matcher=$((matcher + 1))
    else agree=$((agree + 1))
    fi
    if [ -n "$cls" ]; then
      cp "$W/m/$base" "$W/keep/$cls-$total-$base"
      echo "$cls mutant $k of $base: dk_ref=$r dk=$m fixed=$x | $(head -c 140 "$W/ref.err" | tr '\n' ' ')"
    fi
    k=$((k + STRIDE))
  done
done
rm -f "$W/m/"* "$W/ref.err"
echo "SUMMARY mutants=$total agree=$agree accept-bad=$accbad reject-good=$rejgood no-verdict=$nov oracle-timeout=$otime dk-matcher=$matcher files-skipped=$skipped"

#!/bin/sh
# Term-level mutation differential on lean4export NDJSON files.
#
# usage: mutate_terms.sh LEAN_TCALC OFFICIAL_KERNEL WORKDIR FILE.ndjson...
#
# Every FILE must be accepted by both checkers.  One number is changed on one line
# (a declaration's type or value, an application's argument, a bound-variable index,
# a sort's level, a constant's first universe argument, a projection index), and both
# checkers run on the mutant.  Many mutants are still valid exports; what matters is
# agreement:
#   ACCEPT-BAD   the checker accepts a mutant the official kernel refuses
#   REJECT-GOOD  the checker refuses a mutant the official kernel accepts
# STRIDE (default 7) selects every STRIDE-th candidate line (those at OFFSET modulo STRIDE,
# default 0), MAX_PER_FILE (default 40) bounds the mutants per file.
set -u
BIN=$1; ORACLE=$2; WORK=$3; shift 3
STRIDE=${STRIDE:-7}; MAXF=${MAX_PER_FILE:-40}
ulimit -c 0
total=0; agree_rej=0; agree_acc=0; acc_bad=0; rej_good=0; other=0

run_mutant() { # FILE LINENO KIND SEDPROG
  f=$1; ln=$2; kind=$3; prog=$4
  sed "${ln}${prog}" "$f" > "$WORK/mutant.ndjson"
  cmp -s "$f" "$WORK/mutant.ndjson" && return
  ( timeout 60 "$BIN" "$WORK/mutant.ndjson" >/dev/null 2>&1 ); rc=$?
  timeout 120 "$ORACLE" "$WORK/mutant.ndjson" >/dev/null 2>&1; orc=$?
  total=$((total+1))
  if [ "$rc" -eq 0 ] && [ "$orc" -eq 0 ]; then agree_acc=$((agree_acc+1))
  elif [ "$rc" -eq 1 ] && [ "$orc" -ne 0 ]; then agree_rej=$((agree_rej+1))
  elif [ "$rc" -eq 0 ]; then acc_bad=$((acc_bad+1)); echo "ACCEPT-BAD $kind line=$ln $(basename "$f")"; cp "$WORK/mutant.ndjson" "$WORK/accept-bad-$acc_bad.ndjson"
  elif [ "$rc" -eq 1 ]; then rej_good=$((rej_good+1)); echo "REJECT-GOOD $kind line=$ln $(basename "$f")"; cp "$WORK/mutant.ndjson" "$WORK/reject-good-$rej_good.ndjson"
  else other=$((other+1)); echo "OTHER rc=$rc oracle_rc=$orc $kind line=$ln $(basename "$f")"
  fi
}

num_after() { # LINE PREFIX -> first number after PREFIX
  printf '%s\n' "$1" | grep -o "$2[0-9][0-9]*" | head -1 | grep -o '[0-9][0-9]*$'
}

for f in "$@"; do
  "$BIN" "$f" >/dev/null 2>&1 || { echo "BASELINE-NOT-ACCEPTED-BY-CHECKER $(basename "$f")"; continue; }
  "$ORACLE" "$f" >/dev/null 2>&1 || { echo "BASELINE-NOT-ACCEPTED-BY-ORACLE $(basename "$f")"; continue; }
  nfile=0; cand=0
  grep -n -E '^\{"(thm|def|axiom|opaque)":|^\{"app":|^\{"bvar":|"sort":|^\{"const":|"proj":' "$f" | cut -d: -f1 > "$WORK/candidates.txt"
  while read -r ln; do
    cand=$((cand+1))
    [ $((cand % STRIDE)) -eq "${OFFSET:-0}" ] || continue
    [ "$nfile" -lt "$MAXF" ] || break
    line=$(sed -n "${ln}p" "$f")
    case "$line" in
      '{"thm":'*|'{"def":'*|'{"opaque":'*)
        v=$(num_after "$line" '"value":'); t=$(num_after "$line" '"type":')
        [ -n "$v" ] && [ "$v" -gt 0 ] && { run_mutant "$f" "$ln" decl-value-1 "s/\"value\":$v\\([,}]\\)/\"value\":$((v-1))\\1/"; nfile=$((nfile+1)); }
        [ -n "$t" ] && [ "$t" -gt 0 ] && { run_mutant "$f" "$ln" decl-type-1 "s/\"type\":$t\\([,}]\\)/\"type\":$((t-1))\\1/"; nfile=$((nfile+1)); } ;;
      '{"axiom":'*)
        t=$(num_after "$line" '"type":')
        [ -n "$t" ] && [ "$t" -gt 0 ] && { run_mutant "$f" "$ln" axiom-type-1 "s/\"type\":$t\\([,}]\\)/\"type\":$((t-1))\\1/"; nfile=$((nfile+1)); } ;;
      '{"app":'*)
        a=$(num_after "$line" '"arg":')
        [ -n "$a" ] && [ "$a" -gt 0 ] && { run_mutant "$f" "$ln" app-arg-1 "s/\"arg\":$a,/\"arg\":$((a-1)),/"; nfile=$((nfile+1)); } ;;
      '{"bvar":'*)
        b=$(num_after "$line" '"bvar":')
        [ -n "$b" ] && { run_mutant "$f" "$ln" bvar+1 "s/\"bvar\":$b,/\"bvar\":$((b+1)),/"; nfile=$((nfile+1)); } ;;
      *'"sort":'*)
        s=$(num_after "$line" '"sort":')
        [ -n "$s" ] && [ "$s" -gt 0 ] && { run_mutant "$f" "$ln" sort-1 "s/\"sort\":$s}/\"sort\":$((s-1))}/"; nfile=$((nfile+1)); } ;;
      '{"const":'*)
        u=$(num_after "$line" '"us":\[')
        [ -n "$u" ] && [ "$u" -gt 0 ] && { run_mutant "$f" "$ln" const-level-1 "s/\"us\":\\[$u\\([],]\\)/\"us\":[$((u-1))\\1/"; nfile=$((nfile+1)); } ;;
      *'"proj":'*)
        p=$(num_after "$line" '"proj":{"idx":')
        [ -n "$p" ] && { run_mutant "$f" "$ln" proj-idx+1 "s/\"proj\":{\"idx\":$p,/\"proj\":{\"idx\":$((p+1)),/"; nfile=$((nfile+1)); } ;;
    esac
  done < "$WORK/candidates.txt"
done
rm -f "$WORK/mutant.ndjson" "$WORK/candidates.txt"
echo "SUMMARY mutants=$total both-reject=$agree_rej both-accept=$agree_acc accept-bad=$acc_bad reject-good=$rej_good other=$other"

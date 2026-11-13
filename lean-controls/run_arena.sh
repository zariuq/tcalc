#!/bin/sh
# Differential of a lean_tcalc build against the Lean Kernel Arena's expected verdicts.
# usage: run_arena.sh LEAN_TCALC_BINARY ARENA_BUILD_TESTS_DIR [per-test timeout seconds]
# Prints one line per test: verdict-class, expected outcome, exit code, test name.
#   OK          checker verdict matches the arena's expected outcome
#   ACCEPT-BAD  checker accepted an export the arena expects to be rejected (soundness)
#   REJECT-GOOD checker refused an export the arena expects to be accepted (completeness)
#   DECLINE     checker declined (exit 2)
#   OTHER       timeout, crash or fault
# Skips init/std/perf unless ARENA_FULL=1.
set -u
BIN=$1
ROOT=$2
TMO=${3:-60}
ok=0; acc_bad=0; rej_good=0; decl=0; other=0; either=0
for stats in $(find "$ROOT" -name '*.stats.json' | sort); do
  nd="${stats%.stats.json}.ndjson"
  [ -f "$nd" ] || continue
  name=$(grep -o '"name": *"[^"]*"' "$stats" | head -1 | sed 's/.*: *"//; s/"$//')
  exp=$(grep -o '"outcome": *"[^"]*"' "$stats" | head -1 | sed 's/.*: *"//; s/"$//')
  case "$name" in
    init|std|perf/*|mathlib|cslib|cedar*) [ "${ARENA_FULL:-0}" = 1 ] || continue ;;
  esac
  ( timeout "$TMO" "$BIN" "$nd" >/dev/null 2>&1 )
  rc=$?
  cls=OTHER
  case "$exp:$rc" in
    accept:0|reject:1) cls=OK; ok=$((ok+1)) ;;
    either:0|either:1) cls=OK; either=$((either+1)) ;;
    reject:0) cls=ACCEPT-BAD; acc_bad=$((acc_bad+1)) ;;
    accept:1) cls=REJECT-GOOD; rej_good=$((rej_good+1)) ;;
    *:2) cls=DECLINE; decl=$((decl+1)) ;;
    *) other=$((other+1)) ;;
  esac
  printf '%s\t%s\t%s\t%s\n' "$cls" "$exp" "$rc" "$name"
done
printf 'SUMMARY ok=%d either=%d accept-bad=%d reject-good=%d decline=%d other=%d\n' \
  "$ok" "$either" "$acc_bad" "$rej_good" "$decl" "$other"

#!/bin/sh
# The specialized checker against the generic one: on every file, the same exit status, message
# and counts (declarations, definitions, theorems, rules, assertions, commands, firings, refused
# firings, facts).  Left out: times, the count of compiled decisions, and the count of terms (linking
# the compiled rules interns their schemas' terms into the table).
#
# usage: spec_check.sh DK_REF DK_REF_SPEC FILE.dk ...
set -u
abs() { (cd "$(dirname "$1")" && echo "$(pwd)/$(basename "$1")"); }
REF=$(abs "$1"); SPEC=$(abs "$2"); shift 2
[ -x "$REF" ] && [ -x "$SPEC" ] || { echo "spec_check: $REF or $SPEC is not a program"; exit 2; }
ulimit -c 0
n=0; same=0; fast=0; broken=0
for f in "$@"; do
  f=$(abs "$f")
  flags=$(head -n 1 "$f" | sed -n 's/^(; expect [0-9]\(.*\);)$/\1/p')
  # shellcheck disable=SC2086
  a=$(cd "$(dirname "$f")" && timeout 120 "$REF" --stats -q $flags "$f" 2>&1 >/dev/null; echo "rc=$?")
  # shellcheck disable=SC2086
  b=$(cd "$(dirname "$f")" && timeout 120 "$SPEC" --stats -q $flags "$f" 2>&1 >/dev/null; echo "rc=$?")
  n=$((n + 1))
  case "$a$b" in *rc=12[4-9]*|*rc=13[0-9]*|*"cannot open"*) broken=$((broken + 1)); echo "NOT RUN (timeout, not executable or not found): $f" ;; esac
  k=$(echo "$b" | sed -n 's/.* \([0-9]*\) decisions by compiled rules.*/\1/p')
  fast=$((fast + ${k:-0}))
  a2=$(echo "$a" | grep -v 'decided by the specializer' | sed 's/ \[[0-9.]* s\]//; s/; [0-9]* decisions by compiled rules//; s/, [0-9]* terms//')
  b2=$(echo "$b" | grep -v 'decided by the specializer' | sed 's/ \[[0-9.]* s\]//; s/; [0-9]* decisions by compiled rules//; s/, [0-9]* terms//')
  if [ "$a2" = "$b2" ]; then same=$((same + 1))
  else echo "DIFFERENT $f"; echo "  generic:     $a2" | head -3; echo "  specialized: $b2" | head -3
  fi
done
echo "SUMMARY files=$n same=$same not-run=$broken decisions-by-compiled-rules=$fast"
[ "$n" = "$same" ] && [ "$broken" = 0 ] && [ "$fast" -gt 0 ]

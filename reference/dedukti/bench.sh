#!/bin/sh
# Costs: dk_ref (generic, and with its fixed rules compiled by the specializer) against `dk` and the
# old prototype dk_tcalc.
#
# usage: bench.sh DK_REF DK DK_TCALC DEDUKTI_SRC WORK [DK_REF_SPEC]
#
# 1. A scaling workload: 2^n built two ways (unary numerals, rewriting), n = 8, 10, 12, 14.
# 2. The theories of Dedukti's libraries/theories that dk_ref accepts.
# 3. The files of Dedukti's tests/OK that dk_ref and dk accept without flags, checked one by one.
# Times are wall-clock seconds (the best of three for 1 and 2); dk_ref also reports its firings.
set -u
REF=$1; DK=$2; OLD=$3; SRC=$4; W=$5/bench; SPEC=${6:-}
mkdir -p "$W" || exit 2
now() { date +%s.%N; }
best() { # best of three wall-clock times of a command
  b=1000000
  for i in 1 2 3; do
    t0=$(now); "$@" > /dev/null 2>&1; t1=$(now)
    b=$(echo "$b $t0 $t1" | awk '{ t = $3 - $2; if (t < $1) printf "%.3f", t; else printf "%.3f", $1 }')
  done
  echo "$b"
}
gen() { # 2^$1
  awk -v n="$1" 'BEGIN {
    print "N : Type.\nz : N.\ns : N -> N."
    print "def dbl : N -> N.\n[] dbl z --> z.\n[n] dbl (s n) --> s (s (dbl n))."
    print "def pow2 : N -> N.\n[] pow2 z --> s z.\n[n] pow2 (s n) --> dbl (pow2 n)."
    print "def plus : N -> N -> N.\n[m] plus z m --> m.\n[n, m] plus (s n) m --> s (plus n m)."
    k = "z"; for (i = 0; i < n - 1; i++) k = "(s " k ")"
    print "#ASSERT pow2 (s " k ") == plus (pow2 " k ") (pow2 " k ")."
  }' > "$W/pow$1.dk"
}
printf '%-22s %10s %10s %10s %10s %10s\n' workload firings dk_ref dk_ref_spec dk dk_tcalc
row() { # name file dir
  fr=$("$REF" --stats -q "$2" 2>&1 | sed -n 's/.*; \([0-9]*\) firings.*/\1/p')
  a=$(best "$REF" -q "$2")
  s=-; [ -n "$SPEC" ] && s=$(best "$SPEC" -q "$2")
  d=$(cd "$3" && best "$DK" check "$(basename "$2")")
  o=$(best "$OLD" "$2")
  printf '%-22s %10s %10s %10s %10s %10s\n' "$1" "$fr" "$a" "$s" "$d" "$o"
}
for n in 8 10 12 14; do
  gen "$n"
  row "2^$n" "$W/pow$n.dk" "$W"
done
for f in "$SRC"/libraries/theories/*.dk; do
  "$REF" -q "$f" > /dev/null 2>&1 || continue
  row "$(basename "$f")" "$f" "$(dirname "$f")"
done
n=0; tr=0; ts=0; td=0; to=0
for f in "$SRC"/tests/OK/*.dk; do
  "$REF" -q "$f" > /dev/null 2>&1 || continue
  ( cd "$SRC/tests/OK" && "$DK" check "$(basename "$f")" > /dev/null 2>&1 ) || continue
  n=$((n + 1))
  t0=$(now); "$REF" -q "$f" > /dev/null 2>&1; t1=$(now)
  [ -n "$SPEC" ] && "$SPEC" -q "$f" > /dev/null 2>&1; t2=$(now)
  ( cd "$SRC/tests/OK" && "$DK" check "$(basename "$f")" > /dev/null 2>&1 ); t3=$(now)
  "$OLD" "$f" > /dev/null 2>&1; t4=$(now)
  tr=$(echo "$tr $t0 $t1" | awk '{ print $1 + $3 - $2 }')
  ts=$(echo "$ts $t1 $t2" | awk '{ print $1 + $3 - $2 }')
  td=$(echo "$td $t2 $t3" | awk '{ print $1 + $3 - $2 }')
  to=$(echo "$to $t3 $t4" | awk '{ print $1 + $3 - $2 }')
done
printf 'tests/OK (%d files both accept): dk_ref %.3f s, dk_ref_spec %.3f s, dk %.3f s, dk_tcalc %.3f s (start-up included)\n' \
  "$n" "$tr" "$ts" "$td" "$to"
rm -rf "$W"

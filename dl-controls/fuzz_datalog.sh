#!/bin/sh
# Random positive Datalog programs: dl_tcalc against Souffle.
#
# usage: fuzz_datalog.sh DL_TCALC SOUFFLE WORKDIR COUNT [SEED]
#
# Each program has three binary relations over small numbers, random facts for two of them
# and three to seven random rules (copy, join, converse, diagonal, mutual, three-way join,
# constant head, comparison guard).  Both engines print every relation; the sets must be
# identical.  A program on which they differ is kept in WORKDIR as diff-N.dl.
set -u
DL=$1; SOUF=$2; W=$3; COUNT=$4; SEED=${5:-1}
ulimit -c 0
same=0; diff=0; other=0
norm() { # prints "relation<TAB>row" for every row of every relation block, sorted
  awk '
    /^-+$/ { getline name; next }
    /^=+$/ { next }
    /^[0-9]+\t[0-9]+$/ { print name "\t" $0 }
  ' "$1" | sort
}
i=0
while [ "$i" -lt "$COUNT" ]; do
  i=$((i + 1))
  awk -v seed="$((SEED * 100000 + i))" '
    function r(n) { return int(rand() * n) }
    function rel() { return "R" r(3) }
    BEGIN {
      srand(seed)
      for (k = 0; k < 3; k++) printf ".decl R%d(x:number,y:number)\n.output R%d\n", k, k
      dom = 3 + r(6)
      nf = 2 + r(10)
      for (k = 0; k < nf; k++) printf "R%d(%d,%d).\n", r(2), 1 + r(dom), 1 + r(dom)
      nr = 3 + r(5)
      for (k = 0; k < nr; k++) {
        t = r(8); h = rel(); a = rel(); b = rel(); c = rel()
        if (t == 0) printf "%s(X,Y) :- %s(X,Y).\n", h, a
        else if (t == 1) printf "%s(X,Z) :- %s(X,Y), %s(Y,Z).\n", h, a, b
        else if (t == 2) printf "%s(Y,X) :- %s(X,Y).\n", h, a
        else if (t == 3) printf "%s(X,X) :- %s(X,Y).\n", h, a
        else if (t == 4) printf "%s(X,Y) :- %s(X,Y), %s(Y,X).\n", h, a, b
        else if (t == 5) printf "%s(X,Z) :- %s(X,Y), %s(Y,Z), %s(Z,X).\n", h, a, b, c
        else if (t == 6) printf "%s(X,%d) :- %s(X,Y).\n", h, 1 + r(dom), a
        else printf "%s(X,Y) :- %s(X,Y), X < Y.\n", h, a
      }
    }' > "$W/prog.dl"
  ( timeout 30 "$DL" "$W/prog.dl" > "$W/t.out" 2>"$W/t.err" ); rc=$?
  timeout 60 "$SOUF" -D - "$W/prog.dl" > "$W/s.out" 2>"$W/s.err"; orc=$?
  if [ "$rc" -ne 0 ] || [ "$orc" -ne 0 ]; then
    other=$((other + 1)); cp "$W/prog.dl" "$W/other-$other.dl"
    echo "OTHER program $i: dl_tcalc rc=$rc ($(head -c 80 "$W/t.err" | tr '\n' ' ')) souffle rc=$orc"
    continue
  fi
  norm "$W/t.out" > "$W/t.norm"; norm "$W/s.out" > "$W/s.norm"
  if cmp -s "$W/t.norm" "$W/s.norm"; then same=$((same + 1))
  else diff=$((diff + 1)); cp "$W/prog.dl" "$W/diff-$diff.dl"; echo "DIFFERENT program $i (seed $SEED): kept as diff-$diff.dl"
  fi
done
rm -f "$W/prog.dl" "$W/t.out" "$W/t.err" "$W/s.out" "$W/s.err" "$W/t.norm" "$W/s.norm"
echo "SUMMARY programs=$COUNT identical=$same different=$diff other=$other"

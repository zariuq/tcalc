#!/bin/sh
# Random higher-order rewrite patterns: a Dedukti checker against `dk check --type-lhs`.
#
# usage: fuzz_matcher.sh DK_TCALC DK_ORACLE WORKDIR COUNT [SEED]
#
# Each program declares one rule
#     [F, G] g3 (x => y => z => PATTERN) --> ok.
# over three bound variables, and asserts, under one more binder q, that
#     g3 (u => v => w => TARGET)  is (first file) / is not (second file)  convertible with ok.
# PATTERN is built from the constants c, d, a, b, the bound variables, a wildcard, and the
# pattern variables F and G applied to bound variables (now and then to a repeated variable
# or to a constant, which is not a Miller pattern).  TARGET is an instance of PATTERN, with
# one or two leaves changed in about half of the programs, so matches and near-misses both
# occur, as do repeated pattern variables, variables that escape their binder, and rules
# the oracle refuses.  The two checkers must agree on both files.  A disagreeing program is kept in
# WORKDIR as diff-N-is.dk and diff-N-isnot.dk.
set -u
BIN=$1; DK=$2; W=$3; COUNT=$4; SEED=${5:-1}
ulimit -c 0
cd "$W" || exit 2
agree=0; differ=0; matched=0; refused_rule=0
i=0
while [ "$i" -lt "$COUNT" ]; do
  i=$((i + 1))
  awk -v seed="$((SEED * 1000003 + i))" '
    function r(n) { return int(rand() * n) }
    # A term over the placeholders #1..#n (the arguments of an applied pattern variable),
    # the constants, and the outer variable q.
    function body(depth, n,    k) {
      k = rand()
      if (depth == 0 || k < 0.35) {
        k = r(n + 3)
        if (k < n) return "#" (k + 1)
        return k == n ? "a" : (k == n + 1 ? "b" : "q")
      }
      if (k < 0.75) return "(c " body(depth - 1, n) " " body(depth - 1, n) ")"
      return "(d " body(depth - 1, n) ")"
    }
    # An occurrence of the pattern variable v (arity ar[v], body bd[v]): sets P and T.
    function occurrence(v,    n, i, j, k, used, args, t, bad, pick) {
      n = ar[v]; used_var[v]++
      if (n == 0) { P = v; T = bd[v]; return }
      split("", used); args = ""; t = bd[v]; bad = rand() < 0.08
      for (i = 1; i <= n; i++) {
        do { k = r(3) + 1 } while ((k in used) && !(bad && i == n))
        used[k] = 1
        if (bad && i == n && rand() < 0.5) { args = args " a"; pick = "a" }
        else { args = args " " pv[k]; pick = tv[k] }
        gsub("#" i, pick, t)
      }
      P = "(" v args ")"; T = t
    }
    function gen(depth,    k, p1, t1) {
      k = rand()
      if (depth == 0 || k < 0.3) {
        k = r(10)
        if (k < 3) { P = pv[k + 1]; T = tv[k + 1] }
        else if (k == 3) { P = "a"; T = "a" }
        else if (k == 4) { P = "b"; T = "b" }
        else if (k < 8) occurrence("F")
        else if (k == 8) occurrence("G")
        else { P = "_"; T = body(1, 0); gsub("q", (rand() < 0.5 ? "u" : "q"), T) }
        return
      }
      if (k < 0.75) { gen(depth - 1); p1 = P; t1 = T; gen(depth - 1); P = "(c " p1 " " P ")"; T = "(c " t1 " " T ")" }
      else { gen(depth - 1); P = "(d " P ")"; T = "(d " T ")" }
    }
    # Replaces one randomly chosen leaf (u, v, w, a or b) of the target by another one.
    function perturb(    i, s, from, to, pos, k, cnt, rest, off) {
      s = r(5)
      for (i = 0; i < 5; i++) {
        from = leaf[(s + i) % 5 + 1]
        cnt = 0; rest = T; off = 0
        while (match(rest, "[ (]" from "[ )]")) { cnt++; pos[cnt] = off + RSTART; off += RSTART; rest = substr(rest, RSTART + 1) }
        if (cnt == 0) continue
        do { to = leaf[r(5) + 1] } while (to == from)
        k = pos[r(cnt) + 1]
        T = substr(T, 1, k) to substr(T, k + 2)
        return
      }
    }
    BEGIN {
      srand(seed)
      split("x y z", pv, " "); split("u v w", tv, " ")
      # The oracle does not fire a rule with a repeated pattern variable under a binder when
      # the variable stands for a term that mentions the enclosing context (here q), although
      # the two instances are the same term.  Such programs are drawn again, so that every
      # disagreement reported is about something else.
      do {
        split("", used_var)
        ar["F"] = r(4); ar["G"] = r(3)
        bd["F"] = body(2, ar["F"]); bd["G"] = body(2, ar["G"])
        gen(3)
      } while ((used_var["F"] > 1 && bd["F"] ~ /q/) || (used_var["G"] > 1 && bd["G"] ~ /q/))
      split("u v w a b", leaf, " ")
      if (rand() < 0.5) perturb()
      if (rand() < 0.2) perturb()
      ctx = ""
      if (used_var["F"]) ctx = "F"
      if (used_var["G"]) ctx = ctx (ctx == "" ? "" : ", ") "G"
      head = "A : Type.\na : A.\nb : A.\nok : A.\nc : A -> A -> A.\nd : A -> A.\ndef g3 : (A -> A -> A -> A) -> A.\n"
      rule = "[" ctx "] g3 (x => y => z => " P ") --> ok.\n"
      lhs = "(q : A => g3 (u => v => w => " T "))"
      printf "%s%s#ASSERT %s == (q : A => ok).\n", head, rule, lhs > "is.dk"
      printf "%s%s#ASSERTNOT %s == (q : A => ok).\n", head, rule, lhs > "isnot.dk"
    }'
  d1=0; timeout 20 "$DK" check --type-lhs is.dk >/dev/null 2>&1 || d1=1
  d2=0; timeout 20 "$DK" check --type-lhs isnot.dk >/dev/null 2>&1 || d2=1
  ( timeout 20 "$BIN" is.dk >/dev/null 2>&1 ); t1=$?
  ( timeout 20 "$BIN" isnot.dk >/dev/null 2>&1 ); t2=$?
  [ "$d1" = 0 ] && matched=$((matched + 1))
  [ "$d1" = 1 ] && [ "$d2" = 1 ] && refused_rule=$((refused_rule + 1))
  if [ "$d1" = "$t1" ] && [ "$d2" = "$t2" ]; then agree=$((agree + 1))
  else
    differ=$((differ + 1)); cp is.dk "diff-$differ-is.dk"; cp isnot.dk "diff-$differ-isnot.dk"
    echo "DIFFERENT program $i (seed $SEED): oracle is=$d1 isnot=$d2, checker is=$t1 isnot=$t2; kept as diff-$differ-*.dk"
  fi
done
rm -f is.dk isnot.dk
echo "SUMMARY programs=$COUNT agree=$agree different=$differ | oracle: matched=$matched, rule refused=$refused_rule"

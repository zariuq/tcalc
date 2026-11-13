#!/bin/sh
# CHR programs on dl_tcalc against SWI-Prolog's library(chr).
#
# usage: chr_against_swi.sh DL_TCALC SWIPL GSLT_DIR WORK_DIR
#   GSLT_DIR  the GSLT tree (module/gold/CHR/examples, examples/compiler_passes)
#   WORK_DIR  a directory for the generated Prolog files
#
# 1. Ground CHR (C0): the 13 Gold programs and constant folding, each run by dl_tcalc in the
#    naive, indexed and parallel (4 threads) modes.  Naive and indexed must agree exactly
#    (exit status, status, store, number of firings).  SWI-Prolog runs the same program and
#    query: its final store must equal dl_tcalc's, the parallel mode's too except on the four
#    programs whose answer depends on which partner is found first; a failure or an error in
#    SWI-Prolog must be a failure or a fault in dl_tcalc.
# 2. The review counterexamples (dl-controls/review/): exit status, status and store, fault
#    or diagnostic as the file's first line says, in the naive and indexed modes.
# 3. First-order CHR (C1): 16 queries over leq.chr, finite_terms.pl and resource_scheduler.pl;
#    naive and indexed agree, and status and final store equal SWI-Prolog's.
# A negative control checks that a changed store is seen.  Every count printed is counted
# here.  Exit status 1 if any comparison fails.
set -u
DL=$1; SWIPL=$2; G=$3; W=$4
cd "$(dirname "$0")/.."
fail=0
bad() { echo "FAIL: $*"; fail=1; }

# Fields of dl_tcalc's one-line answer {"status":...,"fault":...,"events":N,...,"store":"[...]"}.
status_of() { sed -n 's/^{"status":"\([^"]*\)".*/\1/p'; }
fault_of()  { sed -n 's/.*"fault":"\([^"]*\)".*/\1/p'; }
events_of() { sed -n 's/.*"events":\([0-9]*\).*/\1/p'; }
store_of()  { sed -n 's/.*"store":"\(.*\)"}$/\1/p'; }
# store_lines: a store "[a(1),b(2, x)]" as one constraint per line, sorted; ", " becomes ","
store_lines() {
  awk '{ s = $0; sub(/^\[/, "", s); sub(/\]$/, "", s); gsub(/, /, ",", s)
         if (s == "") exit
         depth = 0; start = 1
         for (i = 1; i <= length(s); i++) {
           c = substr(s, i, 1)
           if (c == "(" || c == "[") depth++
           else if (c == ")" || c == "]") depth--
           else if (c == "," && depth == 0) { print substr(s, start, i - start); start = i + 1 }
         }
         print substr(s, start) }' | LC_ALL=C sort
}
# run_dl NAME ARGS...: runs dl_tcalc, leaves its answer in $W/NAME.json and its exit status in $W/NAME.rc
run_dl() {
  name=$1; shift
  "$DL" "$@" > "$W/$name.json" 2> "$W/$name.err"; echo $? > "$W/$name.rc"
  head -c 1 "$W/$name.json" | grep -q '{' || printf '{"status":"refused"}\n' > "$W/$name.json"
}
# run_swi GOAL PROGRAM: SWI-Prolog's verdict in $W/swi.status (completed, failed, fault) and
# its final store, one constraint per line, sorted, in $W/swi.store
run_swi() {
  "$SWIPL" -q -s "$2" -g "$1" -t halt > "$W/swi.out" 2> "$W/swi.err"; rc=$?
  : > "$W/swi.store"
  if [ "$rc" -ne 0 ]; then echo fault > "$W/swi.status"
  elif grep -q 'SWIPL_STATUS:failed' "$W/swi.out"; then echo failed > "$W/swi.status"
  else echo completed > "$W/swi.status"; grep -v '^[[:space:]]*$' "$W/swi.out" | LC_ALL=C sort > "$W/swi.store"; fi
}
same_run() { # A B: naive and indexed answers agree exactly
  cmp -s "$W/$1.rc" "$W/$2.rc" && [ "$(status_of < "$W/$1.json")" = "$(status_of < "$W/$2.json")" ] &&
  [ "$(store_of < "$W/$1.json")" = "$(store_of < "$W/$2.json")" ] && [ "$(events_of < "$W/$1.json")" = "$(events_of < "$W/$2.json")" ]
}
# agrees NAME: dl_tcalc's answer NAME agrees with SWI-Prolog's
agrees() {
  st=$(status_of < "$W/$1.json"); sw=$(cat "$W/swi.status")
  [ "$st" = "$sw" ] || return 1
  [ "$sw" = completed ] || return 0
  store_of < "$W/$1.json" | store_lines > "$W/$1.store"
  cmp -s "$W/$1.store" "$W/swi.store"
}

# ---- 1. ground CHR (C0) ----
n=0; t=0
enum="chr:'\$enumerate_constraints'"
for f in "$G"/module/gold/CHR/examples/c0/*.chr "$G"/examples/compiler_passes/constant_fold.chr; do
  t=$((t + 1)); b=$(basename "$f" .chr)
  run_dl naive --chr --c0-mode naive "$f"
  run_dl indexed --chr --c0-mode indexed "$f"
  run_dl parallel --chr --c0-mode parallel --c0-threads 4 "$f"
  same_run naive indexed || { bad "C0 $b: naive and indexed modes differ"; continue; }
  q=$(sed -n 's/^[[:space:]]*?-[[:space:]]*\(.*\)\.[[:space:]]*$/\1/p' "$f" | paste -sd, -)
  [ -n "$q" ] || q=true
  { echo ':- use_module(library(chr)).'; grep -v '^[[:space:]]*?-' "$f" | grep -v 'use_module(library(chr))'; } > "$W/c0.pl"
  run_swi "catch((($q) -> (current_predicate($enum/1) -> findall(C, $enum(C), Cs), maplist(writeln, Cs) ; true) ; writeln('SWIPL_STATUS:failed')), E, (writeln(E), halt(2)))" "$W/c0.pl"
  agrees indexed || { bad "C0 $b: dl_tcalc says $(status_of < "$W/indexed.json") $(store_of < "$W/indexed.json"), SWI-Prolog $(cat "$W/swi.status") $(paste -sd, - < "$W/swi.store")"; continue; }
  case "$b" in
    partner_choice|partner_choice_wide|partner_pair|guarded_partner)
      [ "$(status_of < "$W/parallel.json")" = "$(cat "$W/swi.status")" ] || { bad "C0 $b: the parallel mode ends with another status"; continue; } ;;
    *) agrees parallel || { bad "C0 $b: the parallel mode differs from SWI-Prolog"; continue; } ;;
  esac
  n=$((n + 1))
done
echo "CHR C0 against SWI-Prolog: $n/$t programs agree (naive = indexed exactly; store as SWI-Prolog's in the indexed and parallel modes)"
# Negative control of the comparison: one constraint less on SWI-Prolog's side must show.
run_dl indexed --chr --c0-mode indexed "$G/module/gold/CHR/examples/c0/sieve.chr"
store_of < "$W/indexed.json" | store_lines | sed 1d > "$W/swi.store"; echo completed > "$W/swi.status"
if agrees indexed; then bad "the C0 comparison does not see a missing constraint"; else echo "CHR C0 comparison: a store with one constraint less is seen"; fi

# ---- 2. review counterexamples ----
n=0; t=0
for f in dl-controls/review/*.chr; do
  t=$((t + 1)); b=$(basename "$f" .chr)
  line=$(head -1 "$f")
  want_rc=$(printf '%s\n' "$line" | sed -n 's/.*rc=\([0-9]*\).*/\1/p')
  want_st=$(printf '%s\n' "$line" | sed -n 's/.*status=\([a-z]*\).*/\1/p')
  want_d=$(printf '%s\n' "$line" | sed -n 's/.*detail=\(.*\)$/\1/p')
  ok=1
  for mode in naive indexed; do
    run_dl "$mode" --chr --c0-mode "$mode" "$f"
    [ "$(cat "$W/$mode.rc")" = "$want_rc" ] && [ "$(status_of < "$W/$mode.json")" = "$want_st" ] || ok=0
    case "$want_st" in
      completed) [ "$(store_of < "$W/$mode.json")" = "$want_d" ] || ok=0 ;;
      fault) [ "$(fault_of < "$W/$mode.json")" = "$want_d" ] || ok=0 ;;
      refused) grep -q "$want_d" "$W/$mode.err" || ok=0 ;;
    esac
  done
  [ "$ok" = 1 ] && n=$((n + 1)) || bad "review counterexample $b: expected $line, got $(cat "$W/indexed.json") (exit $(cat "$W/indexed.rc"))"
done
echo "CHR review counterexamples: $n/$t as expected (naive and indexed)"

# ---- 3. first-order CHR (C1) ----
n=0; t=0
LEQ=dl-controls/chr/leq.chr
FT=$G/module/gold/CHR/examples/finite_terms.pl
RS=$G/module/gold/CHR/examples/resource_scheduler.pl
while IFS='|' read -r label file mod query; do
  [ -n "$label" ] || continue
  t=$((t + 1))
  case "$file" in leq) path=$LEQ ;; ft) path=$FT ;; rs) path=$RS ;; esac
  run_dl naive --c1 --c0-mode naive --c1-query "$query" "$path"
  run_dl indexed --c1 --c0-mode indexed --c1-query "$query" "$path"
  same_run naive indexed || { bad "C1 $label: naive and indexed modes differ"; continue; }
  { grep -q 'use_module(library(chr))' "$path" || echo ':- use_module(library(chr)).'; cat "$path"; } > "$W/c1.pl"
  if [ -n "$mod" ]; then e="$mod:find_chr_constraint"; else e=$enum; fi
  run_swi "catch((($query) -> (findall(C, $e(C), Cs), maplist(writeln, Cs)) ; writeln('SWIPL_STATUS:failed')), E, (writeln(E), halt(2)))" "$W/c1.pl"
  agrees indexed || { bad "C1 $label: dl_tcalc says $(status_of < "$W/indexed.json") $(store_of < "$W/indexed.json"), SWI-Prolog $(cat "$W/swi.status") $(paste -sd, - < "$W/swi.store")"; continue; }
  n=$((n + 1))
done <<'CASES'
leq:cycle-collapse|leq||leq(A, B), leq(B, C), leq(C, A), A == B, B == C
leq:chain|leq||leq(x, y), leq(y, z)
leq:antisymmetry-conflict|leq||leq(x, y), leq(y, x)
finite_terms:finite-term-propagation|ft|gold_finite_terms|wire(a,b), wire(b,c), value(a,pair(X,z)), value(c,pair(x,z)), X == x
finite_terms:equal-validation-evidence|ft|gold_finite_terms|value(a,pair(x,z)), value(a,pair(x,z))
finite_terms:wrong-conclusion|ft|gold_finite_terms|value(a,x), value(a,y)
finite_terms:occurs-check|ft|gold_finite_terms|same(X,node(X))
finite_terms:missing-wire|ft|gold_finite_terms|value(a,x)
resource_scheduler:equal-workers|rs|gold_resource_scheduler|ready(a,yes), token(worker), token(worker), request(a), request(a)
resource_scheduler:exhausted-workers|rs|gold_resource_scheduler|ready(a,yes), token(worker), request(a), request(a)
resource_scheduler:ordered-resource-choice|rs|gold_resource_scheduler|ready(a,yes), token(backup), token(worker), request(a)
resource_scheduler:backup-resource|rs|gold_resource_scheduler|ready(a,yes), token(backup), request(a)
resource_scheduler:failed-guard|rs|gold_resource_scheduler|ready(a,no), token(worker), request(a)
resource_scheduler:missing-permission|rs|gold_resource_scheduler|token(worker), request(a)
resource_scheduler:binding-wakes-suspended-constraints|rs|gold_resource_scheduler|ready(a,Flag), token(worker), request(a), unify_with_occurs_check(Flag,yes)
resource_scheduler:propagation-history-survives-wakeup|rs|gold_resource_scheduler|receipt(J,primary), unify_with_occurs_check(J,a), receipt(a,primary)
CASES
echo "CHR C1 against SWI-Prolog: $n/$t queries agree (naive = indexed exactly; status and store as SWI-Prolog's)"

[ "$fail" = 0 ] && echo "CHR AGAINST SWI-PROLOG: PASS" || echo "CHR AGAINST SWI-PROLOG: FAIL"
exit $fail

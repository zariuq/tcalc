#!/bin/sh
# Adversarial controls with independent oracles, for the checkers hosted on tcalc.
#
# usage: adversarial_controls.sh BIN_DIR WORK_DIR
#   BIN_DIR   directory holding hol_tcalc, mg_tcalc, dk_tcalc, mm0_tcalc, dl_tcalc, lean_tcalc
#   WORK_DIR  directory for generated streams and helper binaries
#
# Oracles, each optional; a missing oracle is reported and its comparisons are not run:
#   DK_BIN       Dedukti (`dk`), used as `dk check --type-lhs`
#   MG_BIN       OCaml Megalodon
#   LEAN_ORACLE  the official Lean 4 kernel replay of lean4export NDJSON
#   LEAN_SAN     a build of lean_tcalc with -fsanitize=address,undefined
#   SOUFFLE_BIN  Souffle
#   HOLR_SAMPLE  a genuine HOLRPLY1 stream (the generators copy its kernel hash)
#
# Every count printed is counted by this run.  Exit status 1 if any control fails.
set -u
B=$(cd "$1" && pwd); W=$(cd "$2" && pwd)
cd "$(dirname "$0")"
ulimit -c 0
DK_BIN=${DK_BIN:-$(command -v dk || true)}
MG_BIN=${MG_BIN:-}
LEAN_ORACLE=${LEAN_ORACLE:-}
HOLR_SAMPLE=${HOLR_SAMPLE:-}
fail=0
bad() { echo "FAIL: $*"; fail=1; }
status() { "$@" >/dev/null 2>&1; echo $?; }

# ---- hol_tcalc: the caller's axiom policy and probe streams ----
if [ -n "$HOLR_SAMPLE" ] && [ -f "$HOLR_SAMPLE" ]; then
  n=0
  cc -O2 -Wall -Wextra -Werror hol-controls/gen_forged_axiom_stream.c -o "$W/gen_forged_axiom_stream" &&
  cc -O2 -Wall -Wextra -Werror hol-controls/gen_probe_false_expectation.c -o "$W/gen_probe_false_expectation" &&
  "$W/gen_forged_axiom_stream" "$HOLR_SAMPLE" "$W/forged_axiom.holr" &&
  "$W/gen_probe_false_expectation" "$HOLR_SAMPLE" "$W/probe_false.holr" || bad "hol generators"
  [ "$(status "$B/hol_tcalc" --spec hol-controls/forged_axiom.checked-sequents.txt "$W/forged_axiom.holr")" = 1 ] && n=$((n+1)) || bad "hol: a stream that adds its own axiom under the open policy is accepted by default"
  [ "$(status "$B/hol_tcalc" --policy open --spec hol-controls/forged_axiom.checked-sequents.txt "$W/forged_axiom.holr")" = 0 ] && n=$((n+1)) || bad "hol: the same stream is refused under --policy open"
  "$B/hol_tcalc" --policy open "$W/forged_axiom.holr" 2>/dev/null | grep -q 'user_axioms=1' && n=$((n+1)) || bad "hol: the user axiom is not reported"
  [ "$(status "$B/hol_tcalc" "$W/probe_false.holr")" = 1 ] && n=$((n+1)) || bad "hol: a probe stream with a false expectation is accepted"
  [ "$(status "$B/hol_tcalc" --no-such-option "$HOLR_SAMPLE")" = 2 ] && n=$((n+1)) || bad "hol: an unknown option is ignored"
  # A valid theorem about a term nested 1,000,000 deep: the replay accepts it; printing it
  # under a stack that cannot be enlarged ends in "no verdict", not in a signal.
  cc -O2 -Wall -Wextra -Werror hol-controls/gen_deep_term_stream.c -o "$W/gen_deep_term_stream" &&
  "$W/gen_deep_term_stream" "$HOLR_SAMPLE" "$W/deep_term.holr" 1000000 || bad "hol deep-term generator"
  [ "$(status "$B/hol_tcalc" "$W/deep_term.holr")" = 0 ] && n=$((n+1)) || bad "hol: REFL of a term nested 1000000 deep is not accepted"
  rc=$( (ulimit -s 8192 2>/dev/null; ulimit -Hs 8192 2>/dev/null; "$B/hol_tcalc" --print-emits "$W/deep_term.holr" >/dev/null 2>"$W/deep_term.err"; echo $?) )
  [ "$rc" = 2 ] && grep -q 'no verdict' "$W/deep_term.err" && n=$((n+1)) || bad "hol: printing the deep term under a fixed 8 MiB stack gives status $rc, expected 2 and \"no verdict\""
  rm -f "$W/forged_axiom.holr" "$W/probe_false.holr" "$W/gen_forged_axiom_stream" "$W/gen_probe_false_expectation" \
        "$W/gen_deep_term_stream" "$W/deep_term.holr" "$W/deep_term.err"
  echo "hol_tcalc policy, probe and deep-term controls: $n/7"
else
  echo "hol_tcalc policy, probe and deep-term controls: NOT RUN (set HOLR_SAMPLE to a genuine stream)"
fi

# ---- mg_tcalc: definitions are typed as written ----
n=0; t=0
for f in mg-controls/definitions/neg_*.sexpr; do
  t=$((t+1))
  [ "$(status "$B/mg_tcalc" "$f")" = 1 ] || { bad "mg: $f is not refused with status 1"; continue; }
  if [ -n "$MG_BIN" ]; then
    [ "$(status "$MG_BIN" "${f%.sexpr}.mg")" != 0 ] || { bad "mg oracle accepts ${f%.sexpr}.mg"; continue; }
  fi
  n=$((n+1))
done
echo "mg_tcalc definition controls: $n/$t refused$([ -n "$MG_BIN" ] && echo ' (oracle: OCaml Megalodon)' || echo ' (oracle NOT RUN: set MG_BIN)')"

# ---- mg_tcalc: an index that does not fit is malformed; it does not wrap around to a small one ----
# The negatives differ from the accepted baseline in one index: 2^32, 2^64 (both used to be
# read as 0, and the file accepted) and 4294967295.  No second reader of this format exists.
n=0; t=0
for f in mg-controls/numbers/*.sexpr; do
  t=$((t+1))
  case "$(basename "$f")" in neg_*) want=1 ;; *) want=0 ;; esac
  rc=$(status "$B/mg_tcalc" "$f")
  [ "$rc" = "$want" ] && n=$((n+1)) || bad "mg: $f ends with status $rc, expected $want"
done
echo "mg_tcalc integer controls: $n/$t"

# ---- dk_tcalc: matching, directives, modules ----
n=0; t=0
for f in dk-controls/adversarial-2/n*.dk dk-controls/adversarial-2/p*.dk; do
  t=$((t+1))
  case "$(basename "$f")" in n*) want=1 ;; *) want=0 ;; esac
  [ "$(status "$B/dk_tcalc" "$f")" = "$want" ] || { bad "dk: $f, expected status $want"; continue; }
  if [ -n "$DK_BIN" ]; then
    orc=$(cd dk-controls/adversarial-2 && status "$DK_BIN" check --type-lhs "$(basename "$f")")
    if [ "$want" = 0 ]; then [ "$orc" = 0 ] || { bad "dk oracle refuses $f"; continue; }
    else [ "$orc" != 0 ] || { bad "dk oracle accepts $f"; continue; }
    fi
  fi
  n=$((n+1))
done
echo "dk_tcalc adversarial-2 controls: $n/$t agree$([ -n "$DK_BIN" ] && echo ' (oracle: dk check --type-lhs)' || echo ' (oracle NOT RUN: set DK_BIN)')"

# ---- dk_tcalc: the matching profiles (each file says why) ----
# By default dk_tcalc matches every instance of a left-hand side; --dk-matching leaves alone
# the instances Dedukti does not match.  The first line of each file gives the status expected
# from Dedukti and --dk-matching (dk=) and by default (complete=); files under eta/ are checked
# with --eta.  The oracle must agree with --dk-matching.
n=0; t=0
for f in dk-controls/known-differences/*.dk dk-controls/known-differences/eta/*.dk; do
  t=$((t+1))
  case "$f" in */eta/*) eta=--eta ;; *) eta= ;; esac
  want=$(sed -n '1s/.*expect dk=\([0-9]\) complete=\([0-9]\).*/\1 \2/p' "$f")
  [ -n "$want" ] || { bad "dk: $f has no expectation line"; continue; }
  set -- $want
  [ "$(status "$B/dk_tcalc" --dk-matching $eta "$f")" = "$1" ] || { bad "dk: $f, expected status $1 under --dk-matching"; continue; }
  [ "$(status "$B/dk_tcalc" $eta "$f")" = "$2" ] || { bad "dk: $f, expected status $2 by default"; continue; }
  if [ -n "$DK_BIN" ]; then
    orc=$(cd "$(dirname "$f")" && status "$DK_BIN" check $eta --type-lhs "$(basename "$f")")
    if [ "$1" = 0 ]; then [ "$orc" = 0 ] || { bad "dk oracle refuses $f"; continue; }
    else [ "$orc" != 0 ] || { bad "dk oracle accepts $f"; continue; }
    fi
  fi
  n=$((n+1))
done
echo "dk_tcalc matching profiles: $n/$t as expected, by default and under --dk-matching$([ -n "$DK_BIN" ] && echo ' (oracle for --dk-matching: dk check --type-lhs)' || echo ' (oracle NOT RUN: set DK_BIN)')"

# ---- dk_tcalc: a rule wider than the checker's fixed widths is "no verdict", not a refusal ----
n=0; t=0
for f in dk-controls/limits/*.dk; do
  t=$((t+1))
  "$B/dk_tcalc" "$f" >/dev/null 2>"$W/limit.err"; rc=$?
  [ "$rc" = 2 ] && grep -q 'no verdict' "$W/limit.err" || { bad "dk: $f gives status $rc, expected 2 and \"no verdict\""; continue; }
  if [ -n "$DK_BIN" ]; then
    [ "$(cd dk-controls/limits && status "$DK_BIN" check --type-lhs "$(basename "$f")")" = 0 ] || { bad "dk oracle refuses $f"; continue; }
  fi
  n=$((n+1))
done
rm -f "$W/limit.err"
echo "dk_tcalc rule-width controls: $n/$t end in \"no verdict\"$([ -n "$DK_BIN" ] && echo ' (oracle accepts them: dk check --type-lhs)' || echo ' (oracle NOT RUN: set DK_BIN)')"

# ---- dk_tcalc: out of memory is "no verdict"; it is not "not convertible" ----
n=0; t=0
for f in dk-controls/memory/*.dk; do
  t=$((t+1))
  rc=$( (ulimit -v 3000000 2>/dev/null; "$B/dk_tcalc" "$f" >/dev/null 2>"$W/memory.err"; echo $?) )
  [ "$rc" = 2 ] && grep -q 'no verdict: out of memory' "$W/memory.err" && n=$((n+1)) || bad "dk: $f under a 3 GB allowance gives status $rc, expected 2 and \"no verdict: out of memory\""
done
rm -f "$W/memory.err"
echo "dk_tcalc memory controls: $n/$t end in \"no verdict\" under a 3 GB allowance"

# ---- dk_tcalc, mg_tcalc: deep nesting ends in a verdict or in "no verdict", never in a signal ----
n=0
nest() { # nest DEPTH PREFIX SUFFIX: PREFIX, DEPTH opening parentheses, x, DEPTH closing ones, SUFFIX
  awk -v d="$1" -v pre="$2" -v suf="$3" 'BEGIN { printf "%s", pre; for (i = 0; i < d; i++) printf "("; printf "x"; for (i = 0; i < d; i++) printf ")"; printf "%s\n", suf }'
}
nest 400000 'A : Type.
def f : A -> A := x => ' '.' > "$W/deep.dk"
nest 400000 '' '' > "$W/deep.sexpr"
[ "$(status "$B/dk_tcalc" "$W/deep.dk")" = 0 ] && n=$((n+1)) || bad "dk: a definition nested 400000 deep is not accepted"
if [ -n "$DK_BIN" ]; then
  [ "$(cd "$W" && status "$DK_BIN" check --type-lhs deep.dk)" = 0 ] || bad "dk oracle refuses the deeply nested definition"
fi
[ "$(status "$B/mg_tcalc" "$W/deep.sexpr")" = 1 ] && n=$((n+1)) || bad "mg: 400000 nested parentheses are not refused with status 1"
# The same two inputs under a stack that cannot be enlarged: an explicit "no verdict".
for pair in "dk_tcalc deep.dk" "mg_tcalc deep.sexpr"; do
  set -- $pair
  rc=$( (ulimit -s 8192 2>/dev/null; ulimit -Hs 8192 2>/dev/null; "$B/$1" "$W/$2" >/dev/null 2>"$W/deep.err"; echo $?) )
  [ "$rc" = 2 ] && grep -q 'no verdict' "$W/deep.err" && n=$((n+1)) || bad "$1: stack exhaustion under a fixed 8 MiB stack gives status $rc, expected 2 and \"no verdict\""
done
rm -f "$W/deep.dk" "$W/deep.sexpr" "$W/deep.err"
echo "dk_tcalc and mg_tcalc deep-nesting controls: $n/4$([ -n "$DK_BIN" ] && echo ' (oracle for the accepted file: dk check --type-lhs)' || echo ' (oracle NOT RUN: set DK_BIN)')"

# ---- mm0_tcalc: the proof file against a fixed specification ----
n=0; t=0
for f in mm0-controls/proof-file/*.mmu; do
  t=$((t+1))
  case "$(basename "$f")" in neg-*) want=1 ;; *) want=0 ;; esac
  [ "$(status "$B/mm0_tcalc" "$f" mm0-controls/r118/ob/base.mm0)" = "$want" ] && n=$((n+1)) || bad "mm0: $f, expected status $want"
done
echo "mm0_tcalc proof-file controls: $n/$t (specification: mm0-controls/r118/ob/base.mm0)"

# ---- dl_tcalc: a full table is a reported cutoff, never a shortened answer ----
if [ -x "$B/dl_tcalc" ]; then
  n=0
  rows() { grep -cE '^[0-9]+	[0-9]+$' "$1"; }
  "$B/dl_tcalc" dl-controls/capacity/chain-361.dl > "$W/dl.out" 2> "$W/dl.err"; rc=$?
  [ "$rc" = 0 ] && [ "$(rows "$W/dl.out")" = 64980 ] && n=$((n+1)) || bad "dl: chain-361 does not give its 64980 Reach tuples"
  if [ -n "${SOUFFLE_BIN:-}" ]; then
    grep -E '^[0-9]+	[0-9]+$' "$W/dl.out" | sort > "$W/dl.sorted"
    "$SOUFFLE_BIN" -D - dl-controls/capacity/chain-361.dl 2>/dev/null | grep -E '^[0-9]+	[0-9]+$' | sort > "$W/souffle.sorted"
    cmp -s "$W/dl.sorted" "$W/souffle.sorted" && n=$((n+1)) || bad "dl: chain-361 differs from Souffle"
  fi
  "$B/dl_tcalc" dl-controls/capacity/chain-362.dl > "$W/dl.out" 2> "$W/dl.err"; rc=$?
  [ "$rc" = 2 ] && grep -q CapacityCutoff "$W/dl.err" && [ "$(rows "$W/dl.out")" = 0 ] && n=$((n+1)) || bad "dl: chain-362 (65341 tuples, past the fact table) is not reported as a cutoff"
  "$B/dl_tcalc" dl-controls/capacity/symbols-4400.dl > "$W/dl.out" 2> "$W/dl.err"; rc=$?
  [ "$rc" = 2 ] && grep -q CapacityCutoff "$W/dl.err" && n=$((n+1)) || bad "dl: 4400 distinct symbols (past the symbol table) are not reported as a cutoff"
  [ "$("$B/dl_tcalc" --chr dl-controls/capacity/chr_store_3000.chr 2>/dev/null | grep -o 'item(' | wc -l)" = 3000 ] && n=$((n+1)) || bad "dl: the 3000-constraint store is not printed in full"
  rm -f "$W/dl.out" "$W/dl.err" "$W/dl.sorted" "$W/souffle.sorted"
  echo "dl_tcalc capacity controls: $n/$([ -n "${SOUFFLE_BIN:-}" ] && echo 5 || echo 4)$([ -n "${SOUFFLE_BIN:-}" ] && echo ' (oracle: Souffle)' || echo ' (oracle NOT RUN: set SOUFFLE_BIN)')"
else
  echo "dl_tcalc capacity controls: NOT RUN (no dl_tcalc in BIN_DIR)"
fi

# ---- lean_tcalc: recursors and quotient primitives are derived, not trusted ----
n=0; t=0
for f in lean-controls/neg_*.ndjson; do
  t=$((t+1))
  rc=$(status timeout 30 "$B/lean_tcalc" "$f")
  [ "$rc" = 1 ] || { bad "lean: $f is not refused with status 1 (status $rc; 124 means no answer in 30 s)"; continue; }
  if [ -n "$LEAN_ORACLE" ]; then
    [ "$(status "$LEAN_ORACLE" "$f")" != 0 ] || { bad "lean oracle accepts $f"; continue; }
  fi
  n=$((n+1))
done
echo "lean_tcalc negative controls: $n/$t refused$([ -n "$LEAN_ORACLE" ] && echo ' (oracle: official Lean 4 kernel)' || echo ' (oracle NOT RUN: set LEAN_ORACLE)')"

# ---- lean_tcalc: valid declarations wider than the checker's fixed buffers ----
# 70 universe parameters, a recursive field of 70 arguments, 260 parameters.  The checker
# accepts them or says it has no verdict (status 2); a sanitizer build must stay silent.
n=0; t=0
for f in lean-controls/pos_*.ndjson; do
  t=$((t+1))
  rc=$(status timeout 30 "$B/lean_tcalc" "$f")
  [ "$rc" = 0 ] || [ "$rc" = 2 ] || { bad "lean: $f ends with status $rc, expected 0 or 2"; continue; }
  if [ -n "$LEAN_ORACLE" ]; then
    [ "$(status "$LEAN_ORACLE" "$f")" = 0 ] || { bad "lean oracle refuses $f"; continue; }
  fi
  if [ -n "${LEAN_SAN:-}" ]; then
    ASAN_OPTIONS=detect_leaks=0:exitcode=99 UBSAN_OPTIONS=exitcode=98 "$LEAN_SAN" "$f" >/dev/null 2>"$W/lean_san.err"; src=$?
    if [ "$src" = 98 ] || [ "$src" = 99 ] || grep -q 'AddressSanitizer\|runtime error' "$W/lean_san.err"; then
      bad "lean: the sanitizer build reports on $f: $(grep -m1 'runtime error\|ERROR: AddressSanitizer' "$W/lean_san.err" | cut -c1-120)"; continue
    fi
  fi
  n=$((n+1))
done
rm -f "$W/lean_san.err"
echo "lean_tcalc wide-declaration controls: $n/$t accepted or declined$([ -n "$LEAN_ORACLE" ] && echo ' (oracle accepts them: official Lean 4 kernel)' || echo ' (oracle NOT RUN: set LEAN_ORACLE)')$([ -n "${LEAN_SAN:-}" ] && echo '; each also run on the sanitizer build' || echo ' (sanitizer build NOT RUN: set LEAN_SAN)')"

[ "$fail" = 0 ] && echo "ADVERSARIAL CONTROLS: PASS" || echo "ADVERSARIAL CONTROLS: FAIL"
exit $fail

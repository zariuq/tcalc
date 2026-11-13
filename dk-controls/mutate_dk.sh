#!/bin/sh
# Identifier-substitution mutation differential for a Dedukti checker against `dk check --type-lhs`.
#
# usage: mutate_dk.sh DK_TCALC DK_ORACLE WORKDIR FILE.dk...
#
# Every FILE must be accepted by both.  A mutant replaces, on one line, one occurrence of a
# symbol the file declares by the symbol declared next in the file (the last by the first).
# OCC (default 1) selects which occurrence on the line; STRIDE (default 3) and OFFSET select
# the lines; MAX_PER_FILE (default 60) bounds the mutants per file.  Both checkers run on the
# mutant under the original module name.
#   ACCEPT-BAD   the checker accepts a mutant dk refuses
#   REJECT-GOOD  the checker refuses a mutant dk accepts
set -u
BIN=$1; DK=$2; WORK=$3; shift 3
STRIDE=${STRIDE:-3}; OFFSET=${OFFSET:-0}; MAXF=${MAX_PER_FILE:-60}; OCC=${OCC:-1}
ulimit -c 0
total=0; agree_rej=0; agree_acc=0; acc_bad=0; rej_good=0; other=0
for f in "$@"; do
  base=$(basename "$f")
  mkdir -p "$WORK/m"
  cp "$f" "$WORK/m/$base"
  "$BIN" "$WORK/m/$base" >/dev/null 2>&1 || { echo "BASELINE-NOT-ACCEPTED-BY-CHECKER $base"; continue; }
  ( cd "$WORK/m" && "$DK" check --type-lhs "$base" >/dev/null 2>&1 ) || { echo "BASELINE-NOT-ACCEPTED-BY-ORACLE $base"; continue; }
  # declared symbols, in order
  sed -n -E 's/^(def |thm |injective |private )*([A-Za-z_][A-Za-z0-9_'"'"']*) *(\(|:)[^=].*/\2/p' "$f" | grep -v -E '^(def|thm|injective|private|Type)$' | awk '!seen[$0]++' > "$WORK/syms.txt"
  nsyms=$(wc -l < "$WORK/syms.txt")
  [ "$nsyms" -ge 2 ] || continue
  nlines=$(wc -l < "$f")
  nfile=0; ln=0
  while [ "$ln" -lt "$nlines" ] && [ "$nfile" -lt "$MAXF" ]; do
    ln=$((ln + 1))
    [ $((ln % STRIDE)) -eq "$OFFSET" ] || continue
    awk -v target="$ln" -v occ="$OCC" -v symfile="$WORK/syms.txt" '
      BEGIN { n = 0; while ((getline s < symfile) > 0) { n++; sym[n] = s; idx[s] = n } }
      NR != target { print; next }
      {
        line = $0; out = ""; seen = 0; done = 0
        while (match(line, /[A-Za-z_][A-Za-z0-9_'"'"']*/)) {
          tok = substr(line, RSTART, RLENGTH)
          out = out substr(line, 1, RSTART - 1)
          if (!done && (tok in idx)) {
            seen++
            if (seen == occ) { tok = sym[idx[tok] % n + 1]; done = 1 }
          }
          out = out tok
          line = substr(line, RSTART + RLENGTH)
        }
        print out line
      }' "$f" > "$WORK/m/$base"
    cmp -s "$f" "$WORK/m/$base" && continue
    ( timeout 30 "$BIN" "$WORK/m/$base" >/dev/null 2>&1 ); rc=$?
    ( cd "$WORK/m" && timeout 60 "$DK" check --type-lhs "$base" >/dev/null 2>&1 ); orc=$?
    total=$((total+1)); nfile=$((nfile+1))
    if [ "$rc" -eq 0 ] && [ "$orc" -eq 0 ]; then agree_acc=$((agree_acc+1))
    elif [ "$rc" -eq 1 ] && [ "$orc" -ne 0 ]; then agree_rej=$((agree_rej+1))
    elif [ "$rc" -eq 0 ]; then acc_bad=$((acc_bad+1)); echo "ACCEPT-BAD line=$ln occ=$OCC $base"; mkdir -p "$WORK/accept-bad-$acc_bad"; cp "$WORK/m/$base" "$WORK/accept-bad-$acc_bad/$base"
    elif [ "$rc" -eq 1 ]; then rej_good=$((rej_good+1)); echo "REJECT-GOOD line=$ln occ=$OCC $base"; mkdir -p "$WORK/reject-good-$rej_good"; cp "$WORK/m/$base" "$WORK/reject-good-$rej_good/$base"
    else other=$((other+1)); echo "OTHER rc=$rc oracle_rc=$orc line=$ln occ=$OCC $base"; mkdir -p "$WORK/other-$other"; cp "$WORK/m/$base" "$WORK/other-$other/$base"
    fi
  done
  rm -rf "$WORK/m"
done
echo "SUMMARY mutants=$total both-reject=$agree_rej both-accept=$agree_acc accept-bad=$acc_bad reject-good=$rej_good other=$other"

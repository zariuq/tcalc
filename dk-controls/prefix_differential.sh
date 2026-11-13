#!/bin/sh
# Every proper prefix of each file: a Dedukti checker against `dk check --type-lhs`.
#
# usage: prefix_differential.sh DK_TCALC DK_ORACLE WORKDIR FILE.dk...
#
# A file cut off at an arbitrary byte is sometimes still a valid file (the cut fell between
# two statements) and usually not.  The two checkers must agree on every prefix.  Files longer
# than MAX_BYTES (default 600) are skipped; every STEP-th length is tried (default 1).
set -u
BIN=$1; DK=$2; W=$3; shift 3
MAXB=${MAX_BYTES:-600}; STEP=${STEP:-1}
ulimit -c 0
total=0; agree=0; differ=0; signals=0; skipped=0
for f in "$@"; do
  size=$(wc -c < "$f")
  if [ "$size" -gt "$MAXB" ]; then skipped=$((skipped + 1)); continue; fi
  len=1
  while [ "$len" -lt "$size" ]; do
    head -c "$len" "$f" > "$W/prefix.dk"
    d=0; ( cd "$W" && timeout 20 "$DK" check --type-lhs prefix.dk >/dev/null 2>&1 ) || d=1
    ( timeout 20 "$BIN" "$W/prefix.dk" >/dev/null 2>&1 ); r=$?
    total=$((total + 1))
    if [ "$r" -gt 2 ]; then signals=$((signals + 1)); echo "SIGNAL-OR-TIMEOUT rc=$r $(basename "$f") prefix=$len"
    elif [ "$d" = "$r" ]; then agree=$((agree + 1))
    else
      differ=$((differ + 1))
      [ "$differ" -le 20 ] && echo "DIFFERENT $(basename "$f") prefix=$len: oracle=$d checker=$r, ends in [$(tail -c 24 "$W/prefix.dk" | tr '\n' ' ')]"
    fi
    len=$((len + STEP))
  done
done
rm -f "$W/prefix.dk"
echo "SUMMARY prefixes=$total agree=$agree different=$differ signals-or-timeouts=$signals files-skipped-as-too-long=$skipped"

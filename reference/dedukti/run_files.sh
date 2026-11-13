#!/bin/sh
# Files checked by dk_ref, by `dk` (upstream master) and by the fixed candidate, and classified.
#
# usage: run_files.sh DK_REF WORK DK DK_FIXED FILE.dk ...
#
# The expected verdict of a file is its first line's `(; expect N [flags] ;)` when it has one,
# otherwise the fixed candidate's verdict (0 accepted, 1 refused).  A path containing /eta/ or a
# known-differences eta file is checked with --eta; flags on the expect line are passed to all.
# Classes: AGREE, DK-MATCHER (dk_ref and the expectation agree, dk master differs), NOT-HOSTED
# (dk_ref gives no verdict), DIFFERENT (to be classified by a reader).
set -u
REF=$1; W=$2; DK=$3; FIX=$4; shift 4
mkdir -p "$W" || exit 2
ulimit -c 0
st() { [ "$1" = 0 ] && echo 0 || echo 1; }
agree=0; matcher=0; nothost=0; diff=0; total=0
for f in "$@"; do
  total=$((total + 1))
  line=$(head -n 1 "$f")
  want=$(echo "$line" | sed -n 's/^(; expect \([0-9]\).*/\1/p')
  flags=$(echo "$line" | sed -n 's/^(; expect [0-9]\(.*\);)$/\1/p')
  case "$f" in */eta/*) flags="$flags --eta" ;; esac
  base=$(basename "$f"); dir=$(dirname "$f")
  # shellcheck disable=SC2086
  ( cd "$dir" && timeout 60 "$DK" check $flags "$base" >/dev/null 2>&1 ); m=$(st $?)
  # shellcheck disable=SC2086
  ( cd "$dir" && timeout 60 "$FIX" check $flags "$base" >/dev/null 2>&1 ); x=$(st $?)
  # shellcheck disable=SC2086
  ( timeout 120 "$REF" -q $flags "$f" >/dev/null 2>"$W/ref.err" ); r=$?
  [ "$r" -gt 2 ] && r=2
  src=expect
  [ -z "$want" ] && want=$x && src=fixed
  why=$(head -c 160 "$W/ref.err" | tr '\n' ' ')
  if [ "$r" = 2 ]; then cls=NOT-HOSTED; nothost=$((nothost + 1))
  elif [ "$r" = "$want" ] && [ "$r" = "$m" ]; then cls=AGREE; agree=$((agree + 1))
  elif [ "$r" = "$want" ]; then cls=DK-MATCHER; matcher=$((matcher + 1))
  else cls=DIFFERENT; diff=$((diff + 1))
  fi
  printf '%-11s %s [%s] expected(%s)=%s dk_ref=%s dk=%s fixed=%s %s\n' "$cls" "$f" "$flags" "$src" "$want" "$r" "$m" "$x" \
    "$([ "$cls" != AGREE ] && echo "| $why")"
done
echo "SUMMARY files=$total agree=$agree dk-matcher=$matcher not-hosted=$nothost different=$diff"

#!/bin/sh
# Dedukti's own suite (tests/OK and tests/KO, as registered in tests/main.ml), checked by dk_ref,
# by `dk` (upstream master) and, when given, by the fixed candidate.
#
# usage: run_suite.sh DK_REF DEDUKTI_SRC WORK DK [DK_FIXED]
#
# Every registered file is copied to WORK and checked there with the flags its registration gives
# (Export, Import, Type_lhs, Eta, Left_linear, Sr_check, Standard).  Each line gives the verdicts
# (0 accepted, 1 refused, 2 no verdict; for dk any failure is 1) and a class:
#   AGREE        dk_ref gives the registered verdict, as the fixed candidate does
#   DK-MATCHER   dk_ref and the fixed candidate agree and dk (master) differs
#   NOT-HOSTED   dk_ref gives no verdict (a feature it does not host; the message says which)
#   DIFFERENT    anything else: to be classified by a reader
# The last line counts each class.
set -u
REF=$1; SRC=$2; W=$3; DK=$4; FIX=${5:-}
rm -rf "$W/tests" && mkdir -p "$W/tests" || exit 2
cp -r "$SRC/tests/OK" "$SRC/tests/KO" "$SRC/tests/LIB" "$W/tests/" || exit 2
ulimit -c 0
st() { [ "$1" = 0 ] && echo 0 || echo 1; }
agree=0; matcher=0; nothost=0; diff=0; total=0
awk '
/let filename = "tests\// { match($0, /"tests\/[^"]*"/); dir = substr($0, RSTART + 1, RLENGTH - 2) }
/^[ \t]*(ok|ko) ~/ {
  kind = ($0 ~ /^[ \t]*ok/) ? "ok" : "ko"
  match($0, /~basename:"[^"]*"/); base = substr($0, RSTART + 11, RLENGTH - 12)
  fl = $0; sub(/.*~basename:"[^"]*"[ \t]*\[/, "", fl); sub(/\].*/, "", fl)
  printf "%s\t%s\t%s\t%s\n", kind, dir, base, fl
}' "$SRC/tests/main.ml" > "$W/registered.tsv"
while IFS="$(printf '\t')" read -r kind dir base flags; do
  total=$((total + 1))
  d="$W/$dir"
  dkf=""; reff=""
  set --
  case "$flags" in *Type_lhs*) dkf="$dkf --type-lhs"; reff="$reff --type-lhs" ;; esac
  case "$flags" in *Eta*) dkf="$dkf --eta"; reff="$reff --eta" ;; esac
  case "$flags" in *Left_linear*) dkf="$dkf --ll"; reff="$reff --ll" ;; esac
  case "$flags" in *Standard*) dkf="$dkf --standard" ;; esac
  case "$flags" in *Export*) dkf="$dkf -e" ;; esac
  case "$flags" in *Sr_check*) n=$(echo "$flags" | sed 's/.*Sr_check \([0-9]*\).*/\1/'); dkf="$dkf --sr-check $n" ;; esac
  case "$flags" in *Import*)
    idir=$(echo "$flags" | sed 's/.*Import "\([^"]*\)".*/\1/')
    dkf="$dkf -I $idir"
    # dk_ref checks the modules this file names (m.x, {|m|}.x, #REQUIRE m, require m) first,
    # in the same run
    { grep -o -E '(#REQUIRE|require) +(\{\|[^|]*\|\}|[A-Za-z0-9_]+)' "$d/$base" | sed -E 's/^(#REQUIRE|require) +//; s/^\{\|//; s/\|\}$//'
      grep -o -E '(^|[^A-Za-z0-9_|])[A-Za-z0-9_]+\.[A-Za-z0-9_{]' "$d/$base" | sed -E 's/^[^A-Za-z0-9_]//; s/\..*//'
      grep -o -E '\{\|[^|]*\|\}\.' "$d/$base" | sed -E 's/^\{\|//; s/\|\}\.$//'; } | sort -u > "$W/mods.txt"
    while IFS= read -r mm; do
      [ -f "$W/$idir/$mm.dk" ] && [ "$mm.dk" != "$base" ] && set -- "$@" "$W/$idir/$mm.dk"
    done < "$W/mods.txt" ;;
  esac
  want=0; [ "$kind" = ko ] && want=1
  # shellcheck disable=SC2086
  ( cd "$W" && timeout 60 "$DK" check $dkf "$dir$base" >/dev/null 2>&1 ); m=$(st $?)
  f=-
  if [ -n "$FIX" ]; then
    # shellcheck disable=SC2086
    ( cd "$W" && timeout 60 "$FIX" check $(echo "$dkf" | sed 's/ -e//') "$dir$base" >/dev/null 2>&1 ); f=$(st $?)
  fi
  # shellcheck disable=SC2086
  ( cd "$d" && timeout 60 "$REF" -q $reff "$@" "$base" >/dev/null 2>"$W/ref.err" ); r=$?
  [ "$r" -gt 2 ] && r=2
  why=$(head -c 160 "$W/ref.err" | tr '\n' ' ')
  ref_want=$want; [ -n "$FIX" ] && ref_want=$f
  if [ "$r" = 2 ]; then cls=NOT-HOSTED; nothost=$((nothost + 1))
  elif [ "$r" = "$ref_want" ] && [ "$r" = "$m" ]; then cls=AGREE; agree=$((agree + 1))
  elif [ "$r" = "$ref_want" ]; then cls=DK-MATCHER; matcher=$((matcher + 1))
  else cls=DIFFERENT; diff=$((diff + 1))
  fi
  printf '%-11s %s/%s [%s] registered=%s dk_ref=%s dk=%s fixed=%s %s\n' "$cls" "$dir" "$base" "$flags" "$kind" "$r" "$m" "$f" \
    "$([ "$cls" != AGREE ] && echo "| $why")"
done < "$W/registered.tsv"
echo "SUMMARY registered=$total agree=$agree dk-matcher=$matcher not-hosted=$nothost different=$diff"

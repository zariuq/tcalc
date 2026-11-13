#!/bin/sh
# Each harness is first shown to catch planted faults.  For every fault (DK_FAULT, BL_FAULT) and
# every lie of the work order (DK_LIE), dk_ref runs again on the files of a classified run, and the
# files whose verdict changes are counted; a fault or lie that changes no verdict is NOT caught.
# A lie must also be refused by the step itself ("the step refused" in dk_ref's messages).
#
# usage: run_faults.sh DK_REF WORK CLASSIFIED.out ...
#   CLASSIFIED.out: outputs of run_files.sh (lines AGREE or DK-MATCHER: dk_ref was right there)
set -u
REF=$1; W=$2; shift 2
mkdir -p "$W" || exit 2
ulimit -c 0
cat "$@" | grep -E '^(AGREE|DK-MATCHER) ' | sed -E 's/^[A-Z-]+ +([^ ]+) \[([^]]*)\].* dk_ref=([0-9]).*/\1|\2|\3/' > "$W/right.txt"
n=$(wc -l < "$W/right.txt")
fail=0
for spec in DK_FAULT=1 DK_FAULT=3 DK_FAULT=4 DK_FAULT=6 BL_FAULT=1 BL_FAULT=5 DK_LIE=1 DK_LIE=2 DK_LIE=3 DK_LIE=4 DK_LIE=5; do
  changed=0; refused_by_step=0
  while IFS='|' read -r f flags want; do
    # shellcheck disable=SC2086
    ( env "$spec" timeout 60 "$REF" -q $flags "$f" >/dev/null 2>"$W/fault.err" ); r=$?
    [ "$r" -gt 2 ] && r=2
    [ "$r" != "$want" ] && changed=$((changed + 1))
    grep -q "the step refused" "$W/fault.err" && refused_by_step=$((refused_by_step + 1))
  done < "$W/right.txt"
  case "$spec" in
    DK_LIE=*) ok=$([ "$changed" -gt 0 ] && [ "$refused_by_step" -gt 0 ] && echo caught || echo "NOT caught") ;;
    *) ok=$([ "$changed" -gt 0 ] && echo caught || echo "NOT caught") ;;
  esac
  [ "$ok" = caught ] || fail=1
  echo "$spec: $ok: $changed of $n files change verdict; the step refused a lying firing in $refused_by_step"
done
rm -f "$W/fault.err"
exit $fail

#!/bin/sh
# Out-of-range numbers in lean4export NDJSON, run on a sanitizer build of lean_tcalc.
#
# usage: fuzz_numbers_san.sh SAN_LEAN_TCALC WORKDIR FILE.ndjson...
#
# On every STRIDE-th line (default 1) each number in turn (up to MAX_NUMS per line, default 4)
# is replaced by each of the values below.  The checker may accept, refuse or decline; what
# is looked for is a sanitizer report, a signal or a timeout.
set -u
BIN=$1; W=$2; shift 2
STRIDE=${STRIDE:-1}; MAXN=${MAX_NUMS:-4}
export ASAN_OPTIONS=detect_leaks=0:exitcode=99 UBSAN_OPTIONS=print_stacktrace=1:exitcode=98
ulimit -c 0
runs=0; reports=0; signals=0; accepted=0
for f in "$@"; do
  nl=$(wc -l < "$f"); ln=0
  while [ "$ln" -lt "$nl" ]; do
    ln=$((ln + 1))
    [ $((ln % STRIDE)) -eq 0 ] || continue
    k=0
    while [ "$k" -lt "$MAXN" ]; do
      k=$((k + 1))
      for v in 0 99999999 4294967295 4294967296 -1 18446744073709551616; do
        awk -v ln="$ln" -v k="$k" -v v="$v" '
          NR != ln { print; next }
          { line = $0; out = ""; seen = 0
            while (match(line, /[:\[,]-?[0-9]+/)) {
              seen++
              tok = substr(line, RSTART, RLENGTH)
              if (seen == k) tok = substr(tok, 1, 1) v
              out = out substr(line, 1, RSTART - 1) tok
              line = substr(line, RSTART + RLENGTH)
            }
            print out line
          }' "$f" > "$W/m.ndjson"
        cmp -s "$f" "$W/m.ndjson" && continue
        runs=$((runs + 1))
        timeout "${TMO:-4}" "$BIN" "$W/m.ndjson" > "$W/out.txt" 2> "$W/err.txt"; rc=$?
        if [ "$rc" -eq 98 ] || [ "$rc" -eq 99 ] || grep -q 'AddressSanitizer\|runtime error' "$W/err.txt"; then
          reports=$((reports + 1))
          sig=$(grep -m1 'runtime error\|ERROR: AddressSanitizer' "$W/err.txt" | sed 's/==[0-9]*==//; s/0x[0-9a-f]*/ADDR/g' | cut -c1-110)
          where=$(grep -m1 ' in lean_[a-z_0-9]* \| in json_[a-z_0-9]* ' "$W/err.txt" | sed 's/.* in \([a-z_0-9]*\) .*:\([0-9]*\).*/\1:\2/' | cut -c1-60)
          echo "REPORT $(basename "$f") line=$ln number=$k value=$v :: $sig @ $where"
          [ "$reports" -le 12 ] && cp "$W/m.ndjson" "$W/report-$reports.ndjson"
        elif [ "$rc" -gt 2 ]; then
          signals=$((signals + 1))
          [ "$signals" -le 6 ] && echo "SIGNAL-OR-TIMEOUT rc=$rc $(basename "$f") line=$ln number=$k value=$v" && cp "$W/m.ndjson" "$W/signal-$signals.ndjson"
        elif [ "$rc" -eq 0 ]; then
          accepted=$((accepted + 1))
          # With ORACLE set (the official kernel replay), an accepted mutant is judged by it.
          if [ -n "${ORACLE:-}" ] && ! timeout 60 "$ORACLE" "$W/m.ndjson" >/dev/null 2>&1; then
            acc_bad=$((${acc_bad:-0} + 1))
            echo "ACCEPT-BAD $(basename "$f") line=$ln number=$k value=$v"
            [ "$acc_bad" -le 12 ] && cp "$W/m.ndjson" "$W/accept-bad-$acc_bad.ndjson"
          fi
        fi
      done
    done
  done
done
rm -f "$W/m.ndjson" "$W/out.txt" "$W/err.txt"
echo "SUMMARY runs=$runs sanitizer-reports=$reports signals-or-timeouts=$signals accepted=$accepted accepted-and-refused-by-oracle=${acc_bad:-0}$([ -n "${ORACLE:-}" ] || echo ' (oracle NOT RUN)')"

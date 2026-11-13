#!/bin/sh
# Truncation sweep for a HOL replay stream: every proper prefix tried must be refused.
#
# usage: truncate_holr.sh HOL_TCALC REFERENCE_CMD WORKDIR STREAM.holr [POINTS]
#   REFERENCE_CMD  a second replay of the same format, e.g. "cetta --lang hol"; "-" for none
#
# Prefix lengths: every length in the last 96 bytes, and POINTS (default 200) lengths spread
# evenly over the rest.  ACCEPT lines name a prefix the checker accepted.
set -u
BIN=$1; REF=$2; W=$3; F=$4; POINTS=${5:-200}
ulimit -c 0
size=$(wc -c < "$F")
n=0; refused=0; accepted=0; ref_accepted=0; other=0
try() {
  head -c "$1" "$F" > "$W/prefix.holr"
  ( timeout 60 "$BIN" "$W/prefix.holr" >/dev/null 2>&1 ); rc=$?
  n=$((n + 1))
  if [ "$rc" -eq 1 ]; then refused=$((refused + 1))
  elif [ "$rc" -eq 0 ]; then accepted=$((accepted + 1)); echo "ACCEPT prefix of $1 bytes (of $size)"
  else other=$((other + 1)); echo "OTHER prefix of $1 bytes rc=$rc"
  fi
  if [ "$REF" != "-" ]; then
    ( timeout 60 $REF "$W/prefix.holr" >/dev/null 2>&1 ) && { ref_accepted=$((ref_accepted + 1)); echo "REFERENCE-ACCEPT prefix of $1 bytes"; }
  fi
}
step=$(( (size - 96) / POINTS )); [ "$step" -lt 1 ] && step=1
len=0
while [ "$len" -lt $((size - 96)) ]; do try "$len"; len=$((len + step)); done
len=$((size - 96)); [ "$len" -lt 0 ] && len=0
while [ "$len" -lt "$size" ]; do try "$len"; len=$((len + 1)); done
rm -f "$W/prefix.holr"
echo "SUMMARY file=$(basename "$F") prefixes=$n refused=$refused accepted=$accepted other=$other reference-accepted=$ref_accepted"

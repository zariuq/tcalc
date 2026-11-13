#!/bin/sh
# The core's test entry: builds with make, then runs the kernel controls, the step differential
# against the naive reference, and the Micromath differential against Micromath's own kernel.
# FUZZ sets the length of the Micromath random fuzz (default 20,000,000 operations) and THEORIES
# the number of random theories of the step differential (default 4,000).  With an unlimited
# address space the controls and both differentials run again under the address and
# undefined-behaviour sanitizers, in a temporary directory.
set -eu
cd "$(dirname "$0")"
make -s all
./controls
./diff_step "${THEORIES:-4000}"
./diff_micromath "${FUZZ:-20000000}"
if [ "$(ulimit -v)" = unlimited ]; then
  san=$(mktemp -d); trap 'rm -rf "$san"' EXIT
  flags="-O1 -g -std=c11 -fsanitize=address,undefined -fno-sanitize-recover=all -Wall -Wextra -Werror"
  ${CC:-gcc} $flags -I. test/controls.c tc0.c -o "$san/controls"
  ${CC:-gcc} $flags -I. test/diff_step.c tc0.c -o "$san/diff_step"
  ${CC:-gcc} $flags -D_GNU_SOURCE -I. -I../ref test/diff_micromath.c tc0.c micromath.c ../ref/kernel.c -o "$san/diff_micromath"
  "$san/controls" > /dev/null
  "$san/diff_step" 500
  "$san/diff_micromath" 200000 > "$san/micromath.out"
  head -1 "$san/micromath.out"
  echo "the same under -fsanitize=address,undefined: no report"
else
  echo "sanitizer runs: NOT RUN (the address space is capped: ulimit -v $(ulimit -v))"
fi

#!/bin/sh
# check.sh [BINARY...]: the native producers' bytes against their proved digests.
#
#  1. each image NAME.bin against SHA256SUMS, the digests that came with the proved images (their
#     lines name the images by path; matched here by file name);
#  2. in each linked BINARY, the 34 bytes at each symbol tisa_native_NAME (located through the symbol
#     table and the section headers) against the same digests.
#
# Exit status 0 when every digest matches; 1 on any mismatch or anything missing, which fails the
# build (the Makefile runs it after every link of tisa/native_alu.S) or the gate.
here=$(cd "$(dirname "$0")" && pwd)
sums=$here/SHA256SUMS
ops="add64 sub64 and64 or64 xor64"
fail=0
digest() { awk -v f="/$1.bin" '{ n = length($2) - length(f) + 1; if (n > 0 && substr($2, n) == f) { print $1; exit } }' "$sums"; }
for op in $ops; do
  want=$(digest "$op")
  got=$(sha256sum < "$here/$op.bin" 2>/dev/null | cut -d' ' -f1)
  if [ -z "$want" ] || [ "$got" != "$want" ]; then
    echo "native_alu: $op.bin does not match its proved digest in SHA256SUMS"; fail=1
  fi
done
for bin in "$@"; do
  for op in $ops; do
    want=$(digest "$op")
    # the symbol's value, size and section index; that section's address and file offset
    sym=$(readelf -Ws "$bin" 2>/dev/null | awk -v s="tisa_native_$op" '$8 == s && $4 == "FUNC" { print $2, $3, $7; exit }')
    value=$(echo "$sym" | cut -d' ' -f1); size=$(echo "$sym" | cut -d' ' -f2); ndx=$(echo "$sym" | cut -d' ' -f3)
    if [ "$size" != 34 ]; then echo "native_alu: $bin has no 34-byte function tisa_native_$op"; fail=1; continue; fi
    sec=$(readelf -WS "$bin" 2>/dev/null | sed -n 's/^ *\[ *\([0-9]*\)\] *[^ ]* *[^ ]* *\([0-9a-f]*\) *\([0-9a-f]*\) .*/\1 \2 \3/p' |
          awk -v n="$ndx" '$1 == n { print $2, $3; exit }')
    addr=$(echo "$sec" | cut -d' ' -f1); foff=$(echo "$sec" | cut -d' ' -f2)
    if [ -z "$addr" ] || [ -z "$foff" ]; then echo "native_alu: $bin: no section $ndx for tisa_native_$op"; fail=1; continue; fi
    off=$(( 0x$value - 0x$addr + 0x$foff ))
    got=$(dd if="$bin" bs=1 skip="$off" count=34 2>/dev/null | sha256sum | cut -d' ' -f1)
    if [ "$got" != "$want" ]; then echo "native_alu: the 34 bytes at tisa_native_$op in $bin do not match SHA256SUMS"; fail=1; fi
  done
done
exit $fail

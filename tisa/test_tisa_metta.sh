#!/usr/bin/env bash
# test_tisa_metta.sh -- tisa_x86.metta against tisa_x86.c on the exported p1
# corpora: every program's image bytes and spans must be identical.
#
#   test_tisa_metta.sh [SHARDS]
#
# The data directory (TISA_METTA_DATA) holds each corpus NAME.sexpr with the C
# images NAME.sexpr.images. Each corpus is split over SHARDS CeTTa processes
# (default 8) running test_tisa_metta.metta in parallel. Prints every
# mismatch, then for each corpus the counts, the wall time and the
# throughput. Exit status 0 iff every program of every corpus is identical.
set -u
here=$(cd "$(dirname "$0")" && pwd)
cetta=${CETTA:-$here/../../hyperon/CeTTa/cetta}
data=${TISA_METTA_DATA:?set TISA_METTA_DATA to the p1 MeTTa data directory}
shards=${1:-8}

status=0
for name in consumers random_s7; do
    corpus=$data/$name.sexpr
    programs=$(wc -l < "$corpus")
    n=$(( shards < programs ? shards : programs ))
    start=$(date +%s%N)
    output=$(for (( i = 0; i < n; i++ )); do
                 "$cetta" --no-results "$here/test_tisa_metta.metta" "$corpus" "$corpus.images" "$i" "$n" &
             done
             wait)
    end=$(date +%s%N)
    printf '%s\n' "$output" | grep '^MISMATCH'
    printf '%s\n' "$output" | awk -v name="$name" -v programs="$programs" -v shards="$n" -v ns=$(( end - start )) '
        /^RESULT / { for (f = 2; f <= NF; f++) { split($f, kv, "="); sum[kv[1]] += kv[2] }; reported++ }
        END {
            wall = ns / 1e9
            printf "%s: %d/%d programs identical in bytes and spans, %d mismatched", name, sum["identical"], programs, sum["mismatched"]
            if (reported < shards || sum["checked"] != programs)
                printf " (only %d of %d shards reported, %d programs checked)", reported, shards, sum["checked"]
            printf "; %d shards, wall %.2f s, %.0f programs/s; harness time summed over shards %.2f s\n", shards, wall, programs / wall, sum["ms"] / 1000
            exit !(reported == shards && sum["checked"] == programs && sum["identical"] == programs)
        }' || status=1
done
exit $status

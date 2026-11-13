#!/bin/bash
# run_callbacks_evidence.sh OUTDIR
#
# Evidence for the five binary callbacks (add64 sub64 and64 or64 xor64),
# 34 bytes each, proved against s2n-bignum's x86 model:
#   1. the artifacts' SHA256SUMS, and the bytes of every image record;
#   2. in a fresh HOL Light process on s2n-bignum's base: callbacks.ml (the
#      CORE and CONTRACT theorems), callbacks_controls.ml (the mutant
#      controls), the audit (hypotheses of every theorem, the axioms, the
#      statements) and evidence_gate.ml (every loaded file with its digest),
#      then evidence_check.py on the log;
#   3. the s2n instruction gate (census:gate-exit) on each image record, and
#      on a negative record that must fail;
#   4. the C harness (test_callbacks) on the artifacts.
# OUTDIR must not exist.
set -uo pipefail
out=${1:?usage: run_callbacks_evidence.sh OUTDIR}
here=$(cd "$(dirname "$0")" && pwd)
export TCALC_DIR=$(cd "$here/../.." && pwd)
art=$here/binary-callbacks
hol=${HOLDIR:?set HOLDIR to a HOL Light checkout}
s2n=${S2N:?set S2N to an s2n-bignum checkout}
gate_ml=$TCALC_DIR/native/hol/evidence_gate.ml
check_py=$TCALC_DIR/native/hol/evidence_check.py
census=$TCALC_DIR/native/census/x86_census.metta
names="add64 sub64 and64 or64 xor64"
[ -e "$out" ] && { echo "refusing to overwrite $out" >&2; exit 2; }


mkdir -p "$out/sources" "$out/gate"; out=$(realpath "$out")
srcs=("$here/callbacks.ml" "$here/callbacks_controls.ml" "$here/add64.hol" "$here/sub64.hol"
      "$here/and64.hol" "$here/or64.hol" "$here/xor64.hol" "$here/cb_probe.S"
      "$here/test_callbacks.c" "$here/run_callbacks_evidence.sh" "$gate_ml")
{
  sha256sum "${srcs[@]}"
  echo "hol-light $(git -C "$hol" rev-parse HEAD), working tree diff sha256 $(git -C "$hol" diff | sha256sum | cut -d' ' -f1)"
  echo "s2n-bignum $(git -C "$s2n" rev-parse HEAD), working tree diff sha256 $(git -C "$s2n" diff | sha256sum | cut -d' ' -f1)"
  git -C "$s2n" status --short | sed 's/^/  s2n status: /'
} > "$out/inputs.sha256"
cp "${srcs[@]}" "$out/sources/"
git -C "$s2n" diff > "$out/sources/s2n-working-tree.diff"

# 1. The artifacts and the records.
{
  echo "== SHA256SUMS of the artifacts"
  (cd "$art" && sha256sum -c SHA256SUMS) 2>&1
  echo "== the bytes proved, per image (sha256 of the 34 bytes)"
  for nm in $names; do
    rec=$(grep -o '"[0-9a-f]\{68\}"' "$here/$nm.hol" | tr -d '"')
    bin=$(xxd -p "$art/$nm.bin" | tr -d '\n')
    [ "$rec" = "$bin" ] && same=same || same=DIFFERENT
    echo "$nm: $(sha256sum "$art/$nm.bin" | cut -d' ' -f1)  record $same as .bin: $bin"
  done
} > "$out/bytes.txt" 2>&1

# 2. HOL, fresh process.
thms="ADD64_CORE SUB64_CORE AND64_CORE OR64_CORE XOR64_CORE
      ADD64_CONTRACT SUB64_CONTRACT AND64_CONTRACT OR64_CONTRACT XOR64_CONTRACT
      CB_ADD_ARITH CB_SUB_ARITH CB_AND_BITS CB_OR_BITS CB_XOR_BITS CB_TRACE_INBOUNDS
      ADD64_MUT_IS_SUB64 CB_DECODE_F0 CB_DECODE_NIL CB_READ_BYTES8 CB_STUCK
      CB_EVENTUALLY_JOIN CB_ENSURES_DISJOINT CB_W_COMPONENTS CB_W_BYTE
      CB_BYTES_LOADED_CONS CB_W_LOADED CB_READ_BYTES64 CB_W_WORDS CB_W_SEP CB_AREA_LOW
      CB_W_ENTRY CB_READ_WRITE_ORTH CB_W_ORTH CB_W_FRAME ADD64_MUT_CONTRACT_FALSE"
main="ADD64_CONTRACT SUB64_CONTRACT AND64_CONTRACT OR64_CONTRACT XOR64_CONTRACT
      ADD64_CORE SUB64_CORE AND64_CORE OR64_CORE XOR64_CORE ADD64_MUT_CONTRACT_FALSE"
defs="cb_entry cb_area cb_canonical add64_mc sub64_mc and64_mc or64_mc xor64_mc add64_mut_mc
      cb_wmem cb_wstate"
{
  printf 'loadt "%s";;\n' "$TCALC_DIR/native/hol/roots.ml" "$here/callbacks.ml" "$here/callbacks_controls.ml"
  for t in $thms; do printf 'Printf.printf "AUDIT %s: %%d hyps\\n%%!" (length(hyp %s));;\n' "$t" "$t"; done
  for d in $defs; do printf 'print_endline ("DEFINITION %s: " ^ string_of_thm %s);;\n' "$d" "$d"; done
  for t in $main; do printf 'print_endline ("THEOREM %s: " ^ string_of_thm %s);;\n' "$t" "$t"; done
  printf 'let ax = axioms() in Printf.printf "AXIOMS %%d:\\n%%!" (length ax); List.iter (fun th -> Printf.printf "  %%s\\n%%!" (string_of_term (concl th))) ax;;\n'
  printf 'print_endline "AUDIT DONE";;\n'
  printf 'loadt "%s";;\n' "$gate_ml"
} > "$out/hol.in"
start=$(date +%s)
: > "$out/hol.log"
# The HOL process runs in its own process group (hol.pid), so a watcher can
# stop it alone.
setsid bash -c "cd '$s2n' && LINE_EDITOR=env '$hol/hol.sh' < '$out/hol.in' > '$out/hol.log' 2>&1" &
hpid=$!; echo "$hpid" > "$out/hol.pid"
wait "$hpid" || true
rm -f "$out/hol.pid"
hol_seconds=$(( $(date +%s) - start ))
python3 -I "$check_py" "$out/hol.log" > "$out/evidence_check.txt" 2>&1; check_status=$?

# 3. The s2n instruction gate.
work=$(mktemp -d "$out/gate/work.XXXX")
neg="$out/gate/add64-fs-store.hol"
# add64 with an FS segment prefix on the store (64 48 89 86 ...): outside s2n's decoder.
printf '(* control: add64 with an FS prefix on the store; must fail the gate *)\ncb_image "add64_fs" "%s";;\n' \
  "f30f1efa488b8700000000488b97080000004801d06448898600000000b801000000c3" > "$neg"
gate_status=0
for img in $(for nm in $names; do echo "$here/$nm.hol"; done) "$neg"; do
  b=$(basename "$img" .hol)
  printf '!(import! &self "%s")\n!(census:gate-exit "%s")\n' "$census" "$img" > "$work/gate-$b.metta"
  ( TMPDIR="$work" timeout 300 cetta "$work/gate-$b.metta" ) > "$out/gate/$b.out" 2>&1
  st=$?
  line=$(grep -a '^gate ' "$out/gate/$b.out" | head -1)
  echo "$b: status $st: $line" >> "$out/gate/summary.txt"
  if [ "$img" = "$neg" ]; then
    case "$line" in "gate FAIL "*) [ $st -ne 0 ] || gate_status=1;; *) gate_status=1;; esac
  else
    case "$line" in "gate pass "*) [ $st -eq 0 ] || gate_status=1;; *) gate_status=1;; esac
  fi
done
rm -f "$work"/gate-*.metta; rmdir "$work" 2>/dev/null

# 4. The C harness.
mkdir -p "$out/build"
gcc -O2 -Wall -Wextra -o "$out/build/test_callbacks" "$here/test_callbacks.c" "$here/cb_probe.S" \
  > "$out/harness.txt" 2>&1
{
  echo "== default: 200000 random pairs per image, seed 0x5EED"
  ( timeout 300 "$out/build/test_callbacks" "$art" ); echo "EXIT $?"
  echo "== 1000000 random pairs per image, seed 0xC0FFEE"
  ( timeout 300 "$out/build/test_callbacks" "$art" 1000000 0xC0FFEE ); echo "EXIT $?"
} >> "$out/harness.txt" 2>&1

# Summary.
{
  echo "== bytes"; grep -a 'OK\|FAIL\|: [0-9a-f]\{64\}' "$out/bytes.txt"
  echo "== HOL ($hol_seconds s)"
  grep -a -o 'BYTES [a-z0-9]\+: 34 bytes.*' "$out/hol.log"
  grep -a -o 'CONTROL [^:]*: .*' "$out/hol.log"
  grep -a -o 'AUDIT [A-Za-z_0-9]*: [0-9]* hyps' "$out/hol.log"
  echo "theorems audited: $(grep -a -c 'AUDIT [A-Za-z_0-9]*: [0-9]* hyps' "$out/hol.log") of $(echo $thms | wc -w)"
  echo "with hypotheses: $(grep -a 'AUDIT [A-Za-z_0-9]*: [0-9]* hyps' "$out/hol.log" | grep -vc ': 0 hyps')"
  grep -a -A4 'AXIOMS [0-9]' "$out/hol.log" | sed -r 's/\x1B\[[0-9;]*m//g; s/^# //' | head -5
  grep -a -o 'AUDIT DONE' "$out/hol.log" || echo "AUDIT NOT DONE"
  echo "load errors: $(grep -a -c 'Error in included file\|^\(# *\)*Exception\|Sys_error\|^Error' "$out/hol.log")"
  echo "new_axiom, mk_thm or CHEAT_TAC in the sources: $(cat "$here/callbacks.ml" "$here/callbacks_controls.ml" | grep -c 'new_axiom\|mk_thm\|CHEAT_TAC')"
  echo "evidence gate: $(grep -a -o 'EVIDENCE-BEGIN [0-9]* files' "$out/hol.log")"
  tail -1 "$out/evidence_check.txt"; echo "evidence_check exit $check_status"
  echo "== s2n instruction gate"; cat "$out/gate/summary.txt"; echo "gate verdict: $([ $gate_status -eq 0 ] && echo as expected || echo UNEXPECTED)"
  echo "== harness"; grep -a 'cet:\|probe control\|inputs\|control add64\|TOTAL\|EXIT\|FAIL\|error' "$out/harness.txt"
} > "$out/result.txt"
sha256sum "$out/hol.log" >> "$out/result.txt"
cat "$out/result.txt"

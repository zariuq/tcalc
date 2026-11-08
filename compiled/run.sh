#!/bin/sh
# Compile Micromath's theory into Cesta units, check their ownership, and run them in
# lockstep through tcalc-tier0's harness: Micromath's own kernel, the compiled units in
# the tcalc column, and tcalc's schema specializer (micromath_tcalc_gen.h). The leaves,
# whose machine code is proved, are built as their own object; the gate checks that the
# object has no relocations and no calls, and that the linked binary carries its bytes
# unchanged. Then check that mis-compiled units and theories outside the class are refused.
#   CETTA:  the CeTTa binary (the compiler runs on its PeTTa lane)
#   CESTA:  the Cesta binary
#   TCALC:  tcalc-tier0: micromath_tcalc.h, micromath_tcalc_gen.h, diff_micromath.c, ref/
set -e
cd "$(dirname "$0")"
if [ -z "${CETTA:-}" ]; then
  if [ -x ../../hyperon/CeTTa/cetta ]; then CETTA=../../hyperon/CeTTa/cetta; else CETTA=../../../hyperon/CeTTa/cetta; fi
fi
if [ -z "${CESTA:-}" ]; then
  if [ -x ../../cesta/build/cesta ]; then CESTA=../../cesta/build/cesta; else CESTA=../../../cesta/build/cesta; fi
fi
if [ -z "${TCALC:-}" ]; then
  if [ -f ../diff_micromath.c ]; then TCALC=..; else TCALC=../tcalc-tier0; fi
fi
CFLAGS="-O2 -Wall -Wextra -Werror -D_GNU_SOURCE -I$TCALC/ref -I$TCALC"
# The leaf object is the one the machine-code proof reads; these flags are part of it:
# integer registers only and no alignment padding keep it inside the proof's x86 model.
LEAF_CFLAGS="-O2 -mgeneral-regs-only -fno-align-functions -fno-align-jumps -fno-align-labels -fno-align-loops -ffunction-sections -Wall -Wextra -Werror -fno-asynchronous-unwind-tables -I$TCALC"
LEAVES="mm_sub1_leaf mm_sub2_leaf"
W=build
rm -rf ./build
mkdir -p ./build

gcc -O2 -D_GNU_SOURCE -c "$TCALC/ref/kernel.c" -I"$TCALC/ref" -o "$W/micromath_kernel.o"

# emit THEORY COMPILER MODE OUT
emit() {
  "$CETTA" --lang petta --no-results "$1" "emit_$3.metta" "$2" > "$4"
  if grep -q '^#error' "$4"; then grep '^#error' "$4" >&2; return 1; fi
}

# compile THEORY COMPILER NAME: theory -> header, leaf and main units -> checked C -> lockstep binary
compile() {
  d="$W/$3"; mkdir -p "$d"
  emit "$1" "$2" header "$d/micromath_leaf.h"
  emit "$1" "$2" leaf "$d/micromath_leaf.cesta"
  emit "$1" "$2" main "$d/micromath_compiled.cesta"
  "$CESTA" export-c --std=c11 -o "$d/micromath_leaf.c" "$d/micromath_leaf.cesta" -- -I"$d" -I"$TCALC"
  "$CESTA" export-c --std=c11 -o "$d/micromath_compiled.c" "$d/micromath_compiled.cesta" -- -I"$d" -I"$TCALC"
  gcc $LEAF_CFLAGS -I"$d" -c "$d/micromath_leaf.c" -o "$d/micromath_leaf.o"
  gcc $CFLAGS -I"$d" "$TCALC/diff_micromath.c" "$d/micromath_compiled.c" "$d/micromath_leaf.o" harness_hooks.c "$W/micromath_kernel.o" -o "$d/diff"
}

# leaf_bytes OBJECT-OR-BINARY FUNCTION: the function's bytes, one hex pair per line
leaf_bytes() {
  objdump -d --disassemble="$2" "$1" | awk -F'\t' '/^ *[0-9a-f]+:\t/ { n = split($2, b, " "); for (i = 1; i <= n; i++) print b[i] }'
}

compile micromath.theory.metta tcalc_compile.metta micromath
for f in micromath_leaf.h micromath_leaf.cesta micromath_compiled.cesta; do
  cmp -s "$W/micromath/$f" "$f" || { echo "checked-in $f is stale"; exit 1; }
done
# Each leaf gets an object of its own (its section, renamed .text): the object the proof reads.
for fn in $LEAVES; do
  o="$W/micromath/$fn.o"
  objcopy -j ".text.$fn" --rename-section ".text.$fn=.text" "$W/micromath/micromath_leaf.o" "$o"
  if objdump -r "$o" | grep -q 'R_X86_64'; then echo "$fn has relocations"; exit 1; fi
  if objdump -d "$o" | grep -q '[[:space:]]call'; then echo "$fn makes calls"; exit 1; fi
  leaf_bytes "$o" $fn > "$W/$fn.obj.bytes"
  leaf_bytes "$W/micromath/diff" $fn > "$W/$fn.bin.bytes"
  [ -s "$W/$fn.obj.bytes" ] && cmp -s "$W/$fn.obj.bytes" "$W/$fn.bin.bytes" || { echo "$fn: linked bytes differ from the object"; exit 1; }
  cmp -s "$o" "$fn.o" || { echo "checked-in $fn.o differs from the build"; exit 1; }
  echo "$fn: $(wc -l < "$W/$fn.obj.bytes") bytes, no relocations, no calls, linked unchanged"
done
echo "harness $(sha256sum "$TCALC/diff_micromath.c" | cut -c1-16); tcalc-runtime and tcalc-arena-gen columns = the compiled units"
"$W/micromath/diff"

# Mutants: a wrong theory or a wrong compiler must fail the lockstep.
mutant() {  # NAME FILE SED-EXPRESSION
  m="$W/mut-$1"; cp micromath.theory.metta "$m.theory.metta"; cp tcalc_compile.metta "$m.compile.metta"
  case "$2" in theory) f="$m.theory.metta";; *) f="$m.compile.metta";; esac
  sed -i "$3" "$f"
  cmp -s "$f" "$( [ "$2" = theory ] && echo micromath.theory.metta || echo tcalc_compile.metta )" && { echo "mutant $1 did not apply"; exit 1; }
  # The mutant must compile and pass the ownership check, so that the lockstep kills it.
  compile "$m.theory.metta" "$m.compile.metta" "mut-$1" || { echo "mutant $1 did not compile"; exit 1; }
  if "$W/mut-$1/diff" > "$m.out" 2>&1; then echo "MUTANT SURVIVED: $1"; exit 1; fi
  echo "mutant killed by the lockstep: $1: $(grep -m1 DIVERGENCE "$m.out" | cut -c1-80)"
}
mutant sub1-conclusion-swapped theory 's/(EQ x1 t u1 w1))$/(EQ x1 t w1 u1))/'
mutant sub2-repeat-dropped     theory 's/(EQ x1 t u1 w1)) (EQ x1 x a b))/(EQ x1 t u1 w2)) (EQ x1 x a b))/'
mutant proj2-constant-wrong    theory 's/(rule proj2 () (EQ a Y x a))/(rule proj2 () (EQ a X x a))/'
mutant one-guard-dropped       compiler 's/(tc-join " | " (paren-all (tc-rev \$guards)))/(tc-join " | " (paren-all (cdr-atom (tc-rev $guards))))/'
mutant premise-slots-permuted  compiler 's/"\*p{} = k{} < n ? \&sl\[k{}\] : u" (\$i \$i \$i)/"*p{} = k{} < n ? \&sl[k{}] : u" ($i (- 3 $i) (- 3 $i))/'
mutant fresh-inputs-unchecked  compiler 's/"i{} > last"/"i{} > UINT64_MAX - 1"/'

# Theories outside the compiled class are refused with their reason, never compiled.
outside() {  # NAME SED-EXPRESSION REASON
  m="$W/out-$1"; cp micromath.theory.metta "$m.theory.metta"; sed -i "$2" "$m.theory.metta"
  cmp -s "$m.theory.metta" micromath.theory.metta && { echo "control $1 did not apply"; exit 1; }
  if compile "$m.theory.metta" tcalc_compile.metta "out-$1" 2> "$m.err"; then echo "OUT-OF-CLASS THEORY COMPILED: $1"; exit 1; fi
  grep -q "$3" "$m.err" || { echo "control $1 refused for another reason:"; cat "$m.err"; exit 1; }
  echo "refused, outside the class: $1: $(grep -m1 "$3" "$m.err" | cut -c8-100)"
}
outside nested-premise      's/(rule sub1 ((EQ x t u w)/(rule sub1 ((EQ x (t u) u w)/' 'rule sub1: every premise'
outside short-board         's/(rule refl () (EQ a a X Y))/(rule refl () (EQ a a X))/' 'rule refl: every premise'
outside other-constructor   's/(rule proj1 () (EQ x X x a))/(rule proj1 () (EQ2 x X x a))/' 'rule proj1: every premise'
outside input-missing       's/(rule proj2 () (EQ a Y x a))/(rule proj2 () (EQ a Y x c))/' 'mm_proj2: a conclusion hole'
outside premise-missing     's/(EQ x1 t u1 w1)) (EQ x1 x a b))/(EQ x1 t u1 w1)) (EQ x1 x a z))/' 'mm_sub2: a conclusion hole'
outside keeps-no-premises   's/(entry mm_sub1 (keeps sub1))/(entry mm_sub1 (keeps def))/' 'keeps rule def'
outside fresh-also-input    's/(fresh def x1 (t u w))/(fresh def x1 (x1 u w))/' 'also an input'
rm -rf ./build

# With PROOF=1, also check the machine-code proofs of the leaf objects (HOL Light and
# s2n-bignum; see proofs/check.sh).
if [ -n "$PROOF" ]; then proofs/check.sh; fi

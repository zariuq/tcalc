#!/bin/sh
# Checksummed one-way synchronization of Mettapedia/MettaKernel/tcalc-compiled (owned by w10)
# into this repository's compiled/ and Mettapedia/MettaKernel/tcalc-tier0 -> this repository.
set -eu
cd "$(dirname "$0")"
SRC_COMP="../Mettapedia/MettaKernel/tcalc-compiled"
DST_COMP="compiled"

mkdir -p "$DST_COMP/proofs"
for f in emit_header.metta emit_leaf.metta emit_main.metta flat_fire.S flat_fire.h \
         harness_hooks.c micromath.theory.metta micromath_compiled.c micromath_compiled.cesta \
         micromath_leaf.c micromath_leaf.cesta micromath_leaf.h mm_sub1_leaf.o mm_sub2_leaf.o \
         ordinary_flat_adapter.c ordinary_flat_adapter.h ordinary_flat_linked.elf \
         ordinary_flat_linked.text ordinary_flat_runtime.S test_ordinary_flat_adapter.c \
         tcalc.cesta ordinary_flat_adapter.cesta cesta_failure.S \
         ordinary_flat_cesta_runtime.S ordinary_flat_cesta_linked.text \
         test_tcalc_cesta.c test_ordinary_flat_cesta_adapter.c \
         tcalc_compile.metta test_flat_fire.c proofs/check.sh proofs/flat_fire.ml \
         proofs/mm_sub1_leaf.ml proofs/ordinary_adapter.ml proofs/ordinary_flat.ml \
         proofs/cesta_pack_core.ml proofs/cesta_pack.ml proofs/cesta_adapter.ml; do
  if [ -f "$SRC_COMP/$f" ]; then
    cp "$SRC_COMP/$f" "$DST_COMP/$f"
    s1=$(sha256sum "$SRC_COMP/$f" | awk '{print $1}')
    s2=$(sha256sum "$DST_COMP/$f" | awk '{print $1}')
    if [ "$s1" != "$s2" ]; then
      echo "CHECKSUM MISMATCH on $f: $s1 != $s2" >&2
      exit 1
    fi
  fi
done
for f in tcalc_cesta.h tcalc_cesta.c tcalc_cesta.plan \
         ordinary_flat_cesta.h ordinary_flat_cesta.c ordinary_flat_cesta.plan \
         ordinary_flat_cesta.contract.json; do
  if [ -f "$SRC_COMP/build-cesta/$f" ]; then
    cp "$SRC_COMP/build-cesta/$f" "$DST_COMP/$f"
    s1=$(sha256sum "$SRC_COMP/build-cesta/$f" | awk '{print $1}')
    s2=$(sha256sum "$DST_COMP/$f" | awk '{print $1}')
    if [ "$s1" != "$s2" ]; then
      echo "CHECKSUM MISMATCH on generated $f: $s1 != $s2" >&2
      exit 1
    fi
  fi
done
printf "sync_compiled.sh: verified sha256 match on all tcalc-compiled artifacts (flat_fire.S=%s, flat_fire.ml=%s)\n" \
  "$(sha256sum "$DST_COMP/flat_fire.S" | cut -c1-12)" \
  "$(sha256sum "$DST_COMP/proofs/flat_fire.ml" | cut -c1-12)"

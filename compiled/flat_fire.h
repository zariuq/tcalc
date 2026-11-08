#pragma once
#include <stdint.h>

/* A flat rule over a word arena. Rows are word offsets into fields. A guard packs
   i, j, i0, j0 into successive bytes and compares fields[rows[i]+j] with
   fields[rows[i0]+j0]. A make entry packs i, j in its low two bytes.
   The caller admits all indices and supplies arity words at dest and scratch.
   Returns 1 after writing the selected conclusion, or 0 without writing when
   any guard fails. Scratch makes destination/premise aliasing safe. */
uint64_t flat_fire(const uint32_t *fields, const uint32_t *rows,
                   const uint32_t *guards, uint64_t nguards,
                   const uint32_t *make, uint64_t arity,
                   uint32_t *dest, uint32_t *scratch);

#pragma once
/* Micromath as a theory over tc0, with the slot interface of Micromath's own C kernel, so that one
   script can drive both.  A theorem (out f x y) says out(A,B) = f(x(A,B), y(A,B)); symbols 0 and 1
   are the projections X and Y. */
#include <stdbool.h>
#include <stdint.h>

typedef struct { uint64_t out, f, x, y; } MmBody;
enum { MM_ENT_INPUTS, MM_ENT_KEEPS, MM_ENT_FRESH };
typedef struct { const char *name; int kind, rule, nholes; uint8_t holes[3]; } MmEntry;
extern MmEntry mm_entries[6];                /* the theory's entry points, for the specializer */

bool     mm_init(void);
uint64_t mm_new_opaque(void);                /* 0 on failure */
uint64_t mm_new_def(uint64_t f, uint64_t x, uint64_t y, uint64_t slot);
bool     mm_set(uint64_t out, uint64_t f, uint64_t x, uint64_t y, uint64_t slot);   /* an axiom */
MmBody   mm_get(uint64_t slot);
bool     mm_proj1(uint64_t x, uint64_t y, uint64_t slot);
bool     mm_proj2(uint64_t x, uint64_t y, uint64_t slot);
bool     mm_refl(uint64_t a, uint64_t slot);
bool     mm_sub1(uint64_t m, uint64_t u, uint64_t v, uint64_t x, uint64_t dest);
bool     mm_sub2(uint64_t m, uint64_t u, uint64_t v, uint64_t x, uint64_t dest);

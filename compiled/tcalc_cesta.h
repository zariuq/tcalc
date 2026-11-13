#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <limits.h>

#ifndef CESTA_CHECKED_HINTS_DEFINED
#define CESTA_CHECKED_HINTS_DEFINED
#ifndef CESTA_CHECKED_OPTIMIZE
#define CESTA_CHECKED_OPTIMIZE 0
#endif
#if CESTA_CHECKED_OPTIMIZE != 0 && CESTA_CHECKED_OPTIMIZE != 1
#error "CESTA_CHECKED_OPTIMIZE must be 0 or 1"
#endif
#if CESTA_CHECKED_OPTIMIZE && (defined(__GNUC__) || defined(__clang__))
#define CESTA_CHECKED_COLD __attribute__((cold, noinline))
#define CESTA_CHECKED_ALLOC_SIZE __attribute__((alloc_size(1)))
#else
#define CESTA_CHECKED_COLD
#define CESTA_CHECKED_ALLOC_SIZE
#endif
#endif

_Static_assert(CHAR_BIT == 8 && sizeof(size_t) * CHAR_BIT == 64 &&
               PTRDIFF_MAX == SIZE_MAX / 2,
               "checked module word-bits disagrees with the C target");

#ifdef ordinary_flat_failure
#error "checked identifier is a preprocessor macro"
#endif
#ifdef ordinary_flat_pack
#error "checked identifier is a preprocessor macro"
#endif
#ifdef source
#error "checked identifier is a preprocessor macro"
#endif
#ifdef premises
#error "checked identifier is a preprocessor macro"
#endif
#ifdef constants
#error "checked identifier is a preprocessor macro"
#endif
#ifdef fields
#error "checked identifier is a preprocessor macro"
#endif
#ifdef rows
#error "checked identifier is a preprocessor macro"
#endif
#ifdef cesta_result
#error "checked identifier is a preprocessor macro"
#endif
#ifdef field_count
#error "checked identifier is a preprocessor macro"
#endif
#ifdef index
#error "checked identifier is a preprocessor macro"
#endif
#ifdef offset
#error "checked identifier is a preprocessor macro"
#endif
#ifdef base
#error "checked identifier is a preprocessor macro"
#endif
#ifdef column
#error "checked identifier is a preprocessor macro"
#endif
#ifdef cesta_ordinary_flat_read
#error "checked identifier is a preprocessor macro"
#endif
#ifdef cesta_ordinary_flat_write
#error "checked identifier is a preprocessor macro"
#endif
#ifdef cesta_ordinary_flat_add
#error "checked identifier is a preprocessor macro"
#endif
#ifdef cesta_ordinary_flat_sub
#error "checked identifier is a preprocessor macro"
#endif
#ifdef cesta_ordinary_flat_mul
#error "checked identifier is a preprocessor macro"
#endif
#ifdef cesta_ordinary_flat_fail
#error "checked identifier is a preprocessor macro"
#endif
#ifdef cesta_ordinary_flat_read_u32
#error "checked identifier is a preprocessor macro"
#endif
#ifdef cesta_ordinary_flat_write_u32
#error "checked identifier is a preprocessor macro"
#endif

#ifndef CESTA_CHECKED_BYTE_VIEWS_DEFINED
#define CESTA_CHECKED_BYTE_VIEWS_DEFINED
typedef struct { const uint8_t *data; size_t len; } cesta_read_bytes;
typedef struct { uint8_t *data; size_t len; } cesta_write_bytes;
typedef struct { uint8_t *data; size_t len; } cesta_owned_bytes;
#endif

#ifndef CESTA_CHECKED_u32_SPANS_DEFINED
#define CESTA_CHECKED_u32_SPANS_DEFINED
_Static_assert(sizeof(uint32_t) * CHAR_BIT == 32, "checked span element width disagrees with C target");
typedef struct { const uint32_t *data; size_t len; } cesta_read_u32_span;
typedef struct { uint32_t *data; size_t len; } cesta_write_u32_span;
typedef struct { uint32_t *data; size_t len; } cesta_owned_u32_span;
#endif

void ordinary_flat_failure(void);
bool ordinary_flat_pack(cesta_read_u32_span, cesta_read_u32_span, cesta_read_u32_span, cesta_write_u32_span, cesta_write_u32_span);


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
#ifdef flat_fire
#error "checked identifier is a preprocessor macro"
#endif
#ifdef ordinary_flat_adapter
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
#ifdef guards
#error "checked identifier is a preprocessor macro"
#endif
#ifdef makes
#error "checked identifier is a preprocessor macro"
#endif
#ifdef fields
#error "checked identifier is a preprocessor macro"
#endif
#ifdef rows
#error "checked identifier is a preprocessor macro"
#endif
#ifdef dest
#error "checked identifier is a preprocessor macro"
#endif
#ifdef scratch
#error "checked identifier is a preprocessor macro"
#endif
#ifdef cesta_result
#error "checked identifier is a preprocessor macro"
#endif
#ifdef packed
#error "checked identifier is a preprocessor macro"
#endif
#ifdef cesta_ordinary_flat_fail
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
uint64_t flat_fire(const uint32_t *, const uint32_t *, const uint32_t *, size_t, const uint32_t *, size_t, uint32_t *, uint32_t *);
uint64_t ordinary_flat_adapter(cesta_read_u32_span, cesta_read_u32_span, cesta_read_u32_span, cesta_read_u32_span, cesta_read_u32_span, cesta_write_u32_span, cesta_write_u32_span, cesta_write_u32_span, cesta_write_u32_span);
bool ordinary_flat_pack(cesta_read_u32_span, cesta_read_u32_span, cesta_read_u32_span, cesta_write_u32_span, cesta_write_u32_span);

static CESTA_CHECKED_COLD _Noreturn void cesta_ordinary_flat_fail(void)
{
    ordinary_flat_failure();
    for (;;) {}
}

uint64_t ordinary_flat_adapter(cesta_read_u32_span source, cesta_read_u32_span premises, cesta_read_u32_span constants, cesta_read_u32_span guards, cesta_read_u32_span makes, cesta_write_u32_span fields, cesta_write_u32_span rows, cesta_write_u32_span dest, cesta_write_u32_span scratch)
{
    (void)source;
    if ((source.len && !source.data) || source.len > (size_t)PTRDIFF_MAX / sizeof(uint32_t) ||
        (source.len && (uintptr_t)source.data % _Alignof(uint32_t)))
        cesta_ordinary_flat_fail();
    (void)premises;
    if ((premises.len && !premises.data) || premises.len > (size_t)PTRDIFF_MAX / sizeof(uint32_t) ||
        (premises.len && (uintptr_t)premises.data % _Alignof(uint32_t)))
        cesta_ordinary_flat_fail();
    (void)constants;
    if ((constants.len && !constants.data) || constants.len > (size_t)PTRDIFF_MAX / sizeof(uint32_t) ||
        (constants.len && (uintptr_t)constants.data % _Alignof(uint32_t)))
        cesta_ordinary_flat_fail();
    (void)guards;
    if ((guards.len && !guards.data) || guards.len > (size_t)PTRDIFF_MAX / sizeof(uint32_t) ||
        (guards.len && (uintptr_t)guards.data % _Alignof(uint32_t)))
        cesta_ordinary_flat_fail();
    (void)makes;
    if ((makes.len && !makes.data) || makes.len > (size_t)PTRDIFF_MAX / sizeof(uint32_t) ||
        (makes.len && (uintptr_t)makes.data % _Alignof(uint32_t)))
        cesta_ordinary_flat_fail();
    (void)fields;
    if ((fields.len && !fields.data) || fields.len > (size_t)PTRDIFF_MAX / sizeof(uint32_t) ||
        (fields.len && (uintptr_t)fields.data % _Alignof(uint32_t)))
        cesta_ordinary_flat_fail();
    (void)rows;
    if ((rows.len && !rows.data) || rows.len > (size_t)PTRDIFF_MAX / sizeof(uint32_t) ||
        (rows.len && (uintptr_t)rows.data % _Alignof(uint32_t)))
        cesta_ordinary_flat_fail();
    (void)dest;
    if ((dest.len && !dest.data) || dest.len > (size_t)PTRDIFF_MAX / sizeof(uint32_t) ||
        (dest.len && (uintptr_t)dest.data % _Alignof(uint32_t)))
        cesta_ordinary_flat_fail();
    (void)scratch;
    if ((scratch.len && !scratch.data) || scratch.len > (size_t)PTRDIFF_MAX / sizeof(uint32_t) ||
        (scratch.len && (uintptr_t)scratch.data % _Alignof(uint32_t)))
        cesta_ordinary_flat_fail();
    if ((guards.len) > (((size_t)UINT64_C(32)))) {
        uint64_t cesta_result = ((uint64_t)UINT64_C(2));
        return cesta_result;
    } else {
    }
    if ((makes.len) > (((size_t)UINT64_C(32)))) {
        uint64_t cesta_result = ((uint64_t)UINT64_C(2));
        return cesta_result;
    } else {
    }
    if ((makes.len) > (dest.len)) {
        uint64_t cesta_result = ((uint64_t)UINT64_C(2));
        return cesta_result;
    } else {
    }
    if ((makes.len) > (scratch.len)) {
        uint64_t cesta_result = ((uint64_t)UINT64_C(2));
        return cesta_result;
    } else {
    }
    const bool packed = ordinary_flat_pack((cesta_read_u32_span){source.data, source.len}, (cesta_read_u32_span){premises.data, premises.len}, (cesta_read_u32_span){constants.data, constants.len}, (cesta_write_u32_span){fields.data, fields.len}, (cesta_write_u32_span){rows.data, rows.len});
    (void)packed;
    if ((!(packed))) {
        uint64_t cesta_result = ((uint64_t)UINT64_C(2));
        return cesta_result;
    } else {
    }
    uint64_t cesta_result = flat_fire(fields.data, rows.data, guards.data, guards.len, makes.data, makes.len, dest.data, scratch.data);
    return cesta_result;
}


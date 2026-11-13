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

static CESTA_CHECKED_COLD _Noreturn void cesta_ordinary_flat_fail(void)
{
    ordinary_flat_failure();
    for (;;) {}
}

static inline uint32_t cesta_ordinary_flat_read_u32(const uint32_t *data, size_t len, size_t index)
{
    if (index >= len) cesta_ordinary_flat_fail();
    return data[index];
}

static inline void cesta_ordinary_flat_write_u32(uint32_t *data, size_t len, size_t index, uint32_t value)
{
    if (index >= len) cesta_ordinary_flat_fail();
    data[index] = value;
}

static inline uint64_t cesta_ordinary_flat_add(uint64_t a, uint64_t b, uint64_t limit)
{
    if (b > limit || a > limit - b) cesta_ordinary_flat_fail();
    return a + b;
}

static inline uint64_t cesta_ordinary_flat_sub(uint64_t a, uint64_t b, uint64_t limit)
{
    if (a > limit || a < b) cesta_ordinary_flat_fail();
    return a - b;
}

static inline uint64_t cesta_ordinary_flat_mul(uint64_t a, uint64_t b, uint64_t limit)
{
    if (a > limit || b > limit || (b && a > limit / b)) cesta_ordinary_flat_fail();
    return a * b;
}

bool ordinary_flat_pack(cesta_read_u32_span source, cesta_read_u32_span premises, cesta_read_u32_span constants, cesta_write_u32_span fields, cesta_write_u32_span rows)
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
    (void)fields;
    if ((fields.len && !fields.data) || fields.len > (size_t)PTRDIFF_MAX / sizeof(uint32_t) ||
        (fields.len && (uintptr_t)fields.data % _Alignof(uint32_t)))
        cesta_ordinary_flat_fail();
    (void)rows;
    if ((rows.len && !rows.data) || rows.len > (size_t)PTRDIFF_MAX / sizeof(uint32_t) ||
        (rows.len && (uintptr_t)rows.data % _Alignof(uint32_t)))
        cesta_ordinary_flat_fail();
    if ((premises.len) > (((size_t)UINT64_C(24)))) {
        bool cesta_result = false;
        return cesta_result;
    } else {
    }
    if ((constants.len) > (((size_t)UINT64_C(32)))) {
        bool cesta_result = false;
        return cesta_result;
    } else {
    }
    const size_t field_count = ((size_t)cesta_ordinary_flat_add((uint64_t)(((size_t)cesta_ordinary_flat_mul((uint64_t)(premises.len), (uint64_t)(((size_t)UINT64_C(4))), UINT64_C(18446744073709551615)))), (uint64_t)(constants.len), UINT64_C(18446744073709551615)));
    (void)field_count;
    if ((field_count) > (fields.len)) {
        bool cesta_result = false;
        return cesta_result;
    } else {
    }
    if ((((size_t)cesta_ordinary_flat_add((uint64_t)(premises.len), (uint64_t)(((size_t)UINT64_C(1))), UINT64_C(18446744073709551615)))) > (rows.len)) {
        bool cesta_result = false;
        return cesta_result;
    } else {
    }
    for (size_t index = 0; index < premises.len; ++index) {
        const size_t offset = ((size_t)(cesta_ordinary_flat_read_u32(premises.data, premises.len, index)));
        (void)offset;
        if ((offset) > (source.len)) {
            bool cesta_result = false;
            return cesta_result;
        } else {
        }
        if ((((size_t)UINT64_C(4))) > (((size_t)cesta_ordinary_flat_sub((uint64_t)(source.len), (uint64_t)(offset), UINT64_C(18446744073709551615))))) {
            bool cesta_result = false;
            return cesta_result;
        } else {
        }
    }
    for (size_t index = 0; index < premises.len; ++index) {
        const size_t base = ((size_t)cesta_ordinary_flat_mul((uint64_t)(index), (uint64_t)(((size_t)UINT64_C(4))), UINT64_C(18446744073709551615)));
        (void)base;
        const size_t offset = ((size_t)(cesta_ordinary_flat_read_u32(premises.data, premises.len, index)));
        (void)offset;
        cesta_ordinary_flat_write_u32(rows.data, rows.len, index, ((uint32_t)(base)));
        size_t column = ((size_t)UINT64_C(0));
        (void)column;
        while ((column) < (((size_t)UINT64_C(4)))) {
            cesta_ordinary_flat_write_u32(fields.data, fields.len, ((size_t)cesta_ordinary_flat_add((uint64_t)(base), (uint64_t)(column), UINT64_C(18446744073709551615))), cesta_ordinary_flat_read_u32(source.data, source.len, ((size_t)cesta_ordinary_flat_add((uint64_t)(offset), (uint64_t)(column), UINT64_C(18446744073709551615)))));
            column = ((size_t)cesta_ordinary_flat_add((uint64_t)(column), (uint64_t)(((size_t)UINT64_C(1))), UINT64_C(18446744073709551615)));
        }
    }
    cesta_ordinary_flat_write_u32(rows.data, rows.len, premises.len, ((uint32_t)(((size_t)cesta_ordinary_flat_mul((uint64_t)(premises.len), (uint64_t)(((size_t)UINT64_C(4))), UINT64_C(18446744073709551615))))));
    for (size_t index = 0; index < constants.len; ++index) {
        cesta_ordinary_flat_write_u32(fields.data, fields.len, ((size_t)cesta_ordinary_flat_add((uint64_t)(((size_t)cesta_ordinary_flat_mul((uint64_t)(premises.len), (uint64_t)(((size_t)UINT64_C(4))), UINT64_C(18446744073709551615)))), (uint64_t)(index), UINT64_C(18446744073709551615))), cesta_ordinary_flat_read_u32(constants.data, constants.len, index));
    }
    bool cesta_result = true;
    return cesta_result;
}


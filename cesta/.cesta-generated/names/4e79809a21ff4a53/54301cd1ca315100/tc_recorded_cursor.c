#ifndef CESTA_OWNERSHIP_ABI_PROFILE
#define CESTA_OWNERSHIP_ABI_PROFILE 1
#if defined(__aarch64__) && defined(__ARM_PCS_AAPCS64)
_Static_assert(__SIZEOF_POINTER__ == 8 && __SIZEOF_LONG__ == 8 && __SIZEOF_LONG_DOUBLE__ == 16 && __LDBL_MANT_DIG__ == 113 && (char)-1 > 0, "ownership ABI profile requires AArch64 AAPCS64");
#else
#if defined(__SIZEOF_POINTER__) && defined(__SIZEOF_LONG__)
_Static_assert(__SIZEOF_POINTER__ == 8 && __SIZEOF_LONG__ == 8, "ownership ABI profile requires x86_64 SysV");
#endif
_Static_assert((char)-1 < 0, "ownership ABI profile requires signed x86 plain char");
#endif
_Static_assert((unsigned char)256 == 0 && sizeof(void *) == 8 && sizeof(long) == 8 && sizeof(int) == 4 && sizeof(short) == 2 && sizeof(long long) == 8 && sizeof(float) == 4 && sizeof(double) == 8 && sizeof(long double) == 16 && sizeof(enum { __cesta_ownership_abi_enum = 1 }) == 4 && _Alignof(void *) == 8 && _Alignof(long) == 8 && _Alignof(long double) == 16 && sizeof(struct { char a; long b; }) == 16 && sizeof(struct { char a; long double b; }) == 32, "ownership ABI profile requires a supported LP64 target");
#endif

#include "bridge/tc_cetta_bridge.h"

typedef struct {
  const TcPreparedStep *candidate;
  size_t position, limit;
} TcCettaCandidateState;
typedef const TcPreparedStep *(*TcCettaRecordedNext)(TcCettaCandidateState *);

static const TcPreparedStep *tc_cetta_recorded_read(TcCettaCandidateState *state) {
  if (!state->candidate || state->position >= state->limit) return NULL;
  ++state->position;
  return state->candidate;
}


#if 0
#error Cesta_macro_name_is_a_preprocessor_macro
#endif

#if 0
#error Cesta_macro_name_is_a_preprocessor_macro
#endif

#if 0
#error Cesta_macro_name_is_a_preprocessor_macro
#endif

#if 0
#error Cesta_macro_name_is_a_preprocessor_macro
#endif

#if 0
#error Cesta_macro_name_is_a_preprocessor_macro
#endif

#if 0
#error Cesta_macro_name_is_a_preprocessor_macro
#endif
typedef struct TcCettaBorrowCursor {
  TcCettaCandidateState ctx;
  TcCettaRecordedNext next;
}
TcCettaBorrowCursor;
static inline const TcPreparedStep *tc_cetta_borrow_cursor_next(TcCettaBorrowCursor *self) {
  _Static_assert(_Generic(self, struct TcCettaBorrowCursor *: 1, const struct TcCettaBorrowCursor *: 1, volatile struct TcCettaBorrowCursor *: 1, volatile const struct TcCettaBorrowCursor *: 1, default: 0), "record member receiver has its declared owner");
  return self->next(&self->ctx);
}

const TcPreparedStep *tc_cetta_cursor_advance(const TcPreparedStep *input,
                                            size_t *position, size_t limit) {
  if (!position) return NULL;
  TcCettaBorrowCursor cursor = {{input, *position, limit}, tc_cetta_recorded_read};
  const TcPreparedStep *candidate = tc_cetta_borrow_cursor_next(&cursor);
  *position = cursor.ctx.position;
  return candidate;
}



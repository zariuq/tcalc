#pragma once
/* gslt_syntax.h — Self-contained SyntaxGSLT Packet, Catalogue, Source Replay,
 * Prolog/CHR Reader, and Exact Arbitrary-Precision Integer Module for tcalc.
 *
 * Implements the authoritative Lean / MeTTa frontend contracts:
 *   - Exact arbitrary-precision signed integer arithmetic (C0BigInt) for
 *     +, -, *, truncating // (quotient) and rem (remainder), and divisor-sign
 *     mod (modulo), matching Mettapedia/Languages/CHR/Syntax.lean and
 *     hyperon/cetta-prime-nik-20260811/langdef/lang/chr/machine.metta without
 *     signed C overflow UB or silent wraparound.
 *   - Arbitrary-length byte strings (GsltByteStr) preserving embedded NULs
 *     and long atoms (> 1000 bytes) without fixed-buffer truncation.
 *   - SyntaxGSLT packet & SourceValuesV1 catalogue decoding with codepoint
 *     scalar validation, pair/nil spine checking, multi-packet ambiguity
 *     agreement, and per-packet provenance retention.
 *   - Generated 72-operator table from CHRPrologSyntax.profile.operators
 *     (emit_chr_reader_tables.lean) and layout predicates for D0 and C0.
 *   - Complete C0 packet lowerer (chr:program / pl:sentence / pl:apply:N) and
 *     direct Prolog/CHR source lexer & operator-precedence parser producing
 *     the same PlTerm AST. */

#include <ctype.h>
#include <inttypes.h>
#include <limits.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* =========================================================================
 * 1. Exact Arbitrary-Precision Signed Integer (C0BigInt)
 * =========================================================================
 * Base 10^9 limbs in little-endian order:
 *   sign ==  0 : value is 0 (nlimbs == 0)
 *   sign == +1 : positive
 *   sign == -1 : negative
 * Up to C0_BIGINT_MAX_LIMBS (32 limbs = 288 decimal digits, ~956 bits).
 * Operations check limb capacity and return false on overflow rather than
 * wrapping or invoking signed C overflow UB.
 */
#define C0_BIGINT_BASE      1000000000ULL
#define C0_BIGINT_MAX_LIMBS 32

typedef struct {
  int8_t   sign;
  uint8_t  nlimbs;
  uint32_t limbs[C0_BIGINT_MAX_LIMBS];
} C0BigInt;

static inline void c0_bigint_zero(C0BigInt *a) {
  memset(a, 0, sizeof(*a));
}

static inline void c0_bigint_normalize(C0BigInt *a) {
  while (a->nlimbs > 0 && a->limbs[a->nlimbs - 1] == 0) {
    a->nlimbs--;
  }
  if (a->nlimbs == 0) {
    a->sign = 0;
  }
}

static inline void c0_bigint_from_u64(C0BigInt *out, uint64_t v) {
  c0_bigint_zero(out);
  if (v == 0) return;
  out->sign = 1;
  while (v > 0 && out->nlimbs < C0_BIGINT_MAX_LIMBS) {
    out->limbs[out->nlimbs++] = (uint32_t)(v % C0_BIGINT_BASE);
    v /= C0_BIGINT_BASE;
  }
}

static inline void c0_bigint_from_i64(C0BigInt *out, int64_t v) {
  if (v == 0) {
    c0_bigint_zero(out);
    return;
  }
  uint64_t mag = (v < 0) ? ((uint64_t)(-(v + 1)) + 1ULL) : (uint64_t)v;
  c0_bigint_from_u64(out, mag);
  out->sign = (v < 0) ? -1 : 1;
}

static inline bool c0_bigint_to_i64(const C0BigInt *a, int64_t *out) {
  if (a->sign == 0 || a->nlimbs == 0) {
    *out = 0;
    return true;
  }
  if (a->nlimbs > 3) return false;
  __uint128_t mag = 0;
  for (int i = (int)a->nlimbs - 1; i >= 0; i--) {
    mag = mag * C0_BIGINT_BASE + a->limbs[i];
  }
  if (a->sign > 0) {
    if (mag > (__uint128_t)INT64_MAX) return false;
    *out = (int64_t)mag;
    return true;
  } else {
    __uint128_t lim = (__uint128_t)INT64_MAX + 1ULL;
    if (mag > lim) return false;
    if (mag == lim) {
      *out = INT64_MIN;
    } else {
      *out = -(int64_t)mag;
    }
    return true;
  }
}

static inline bool c0_bigint_to_u64(const C0BigInt *a, uint64_t *out) {
  if (a->sign < 0) return false;
  if (a->sign == 0 || a->nlimbs == 0) {
    *out = 0;
    return true;
  }
  if (a->nlimbs > 3) return false;
  __uint128_t mag = 0;
  for (int i = (int)a->nlimbs - 1; i >= 0; i--) {
    mag = mag * C0_BIGINT_BASE + a->limbs[i];
  }
  if (mag > (__uint128_t)UINT64_MAX) return false;
  *out = (uint64_t)mag;
  return true;
}

static inline int c0_bigint_cmp_abs(const C0BigInt *a, const C0BigInt *b) {
  if (a->nlimbs != b->nlimbs) {
    return (a->nlimbs < b->nlimbs) ? -1 : 1;
  }
  for (int i = (int)a->nlimbs - 1; i >= 0; i--) {
    if (a->limbs[i] != b->limbs[i]) {
      return (a->limbs[i] < b->limbs[i]) ? -1 : 1;
    }
  }
  return 0;
}

static inline int c0_bigint_cmp(const C0BigInt *a, const C0BigInt *b) {
  if (a->sign != b->sign) {
    return (a->sign < b->sign) ? -1 : 1;
  }
  if (a->sign == 0) return 0;
  int c = c0_bigint_cmp_abs(a, b);
  return (a->sign > 0) ? c : -c;
}

static inline bool c0_bigint_eq(const C0BigInt *a, const C0BigInt *b) {
  return c0_bigint_cmp(a, b) == 0;
}

static inline bool c0_bigint_add_abs(const C0BigInt *a, const C0BigInt *b, C0BigInt *out) {
  C0BigInt res;
  c0_bigint_zero(&res);
  uint32_t max_n = (a->nlimbs > b->nlimbs) ? a->nlimbs : b->nlimbs;
  uint64_t carry = 0;
  for (uint32_t i = 0; i < max_n; i++) {
    uint64_t av = (i < a->nlimbs) ? a->limbs[i] : 0;
    uint64_t bv = (i < b->nlimbs) ? b->limbs[i] : 0;
    uint64_t sum = av + bv + carry;
    if (i >= C0_BIGINT_MAX_LIMBS) return false;
    res.limbs[i] = (uint32_t)(sum % C0_BIGINT_BASE);
    carry = sum / C0_BIGINT_BASE;
  }
  res.nlimbs = (uint8_t)max_n;
  if (carry > 0) {
    if (res.nlimbs >= C0_BIGINT_MAX_LIMBS) return false;
    res.limbs[res.nlimbs++] = (uint32_t)carry;
  }
  c0_bigint_normalize(&res);
  *out = res;
  return true;
}

/* Precondition: |a| >= |b| */
static inline void c0_bigint_sub_abs(const C0BigInt *a, const C0BigInt *b, C0BigInt *out) {
  C0BigInt res;
  c0_bigint_zero(&res);
  int64_t borrow = 0;
  for (uint32_t i = 0; i < a->nlimbs; i++) {
    int64_t av = (int64_t)a->limbs[i];
    int64_t bv = (i < b->nlimbs) ? (int64_t)b->limbs[i] : 0;
    int64_t diff = av - bv - borrow;
    if (diff < 0) {
      diff += (int64_t)C0_BIGINT_BASE;
      borrow = 1;
    } else {
      borrow = 0;
    }
    res.limbs[i] = (uint32_t)diff;
  }
  res.nlimbs = a->nlimbs;
  c0_bigint_normalize(&res);
  *out = res;
}

static inline bool c0_bigint_add(const C0BigInt *a, const C0BigInt *b, C0BigInt *out) {
  if (a->sign == 0) { *out = *b; return true; }
  if (b->sign == 0) { *out = *a; return true; }
  if (a->sign == b->sign) {
    int8_t s = a->sign;
    if (!c0_bigint_add_abs(a, b, out)) return false;
    out->sign = (out->nlimbs > 0) ? s : 0;
    return true;
  }
  int cmp = c0_bigint_cmp_abs(a, b);
  if (cmp == 0) {
    c0_bigint_zero(out);
    return true;
  } else if (cmp > 0) {
    int8_t s = a->sign;
    c0_bigint_sub_abs(a, b, out);
    out->sign = (out->nlimbs > 0) ? s : 0;
    return true;
  } else {
    int8_t s = b->sign;
    c0_bigint_sub_abs(b, a, out);
    out->sign = (out->nlimbs > 0) ? s : 0;
    return true;
  }
}

static inline bool c0_bigint_sub(const C0BigInt *a, const C0BigInt *b, C0BigInt *out) {
  C0BigInt nb = *b;
  nb.sign = (int8_t)(-nb.sign);
  return c0_bigint_add(a, &nb, out);
}

static inline bool c0_bigint_mul(const C0BigInt *a, const C0BigInt *b, C0BigInt *out) {
  if (a->sign == 0 || b->sign == 0) {
    c0_bigint_zero(out);
    return true;
  }
  uint64_t tmp[C0_BIGINT_MAX_LIMBS * 2];
  memset(tmp, 0, sizeof(tmp));
  for (uint32_t i = 0; i < a->nlimbs; i++) {
    uint64_t carry = 0;
    for (uint32_t j = 0; j < b->nlimbs; j++) {
      uint64_t cur = tmp[i + j] + (uint64_t)a->limbs[i] * (uint64_t)b->limbs[j] + carry;
      tmp[i + j] = cur % C0_BIGINT_BASE;
      carry = cur / C0_BIGINT_BASE;
    }
    uint32_t k = i + b->nlimbs;
    while (carry > 0) {
      uint64_t cur = tmp[k] + carry;
      tmp[k] = cur % C0_BIGINT_BASE;
      carry = cur / C0_BIGINT_BASE;
      k++;
    }
  }
  uint32_t top = a->nlimbs + b->nlimbs;
  while (top > 0 && tmp[top - 1] == 0) top--;
  if (top > C0_BIGINT_MAX_LIMBS) return false;
  C0BigInt res;
  c0_bigint_zero(&res);
  res.nlimbs = (uint8_t)top;
  for (uint32_t i = 0; i < top; i++) {
    res.limbs[i] = (uint32_t)tmp[i];
  }
  res.sign = (a->sign == b->sign) ? 1 : -1;
  c0_bigint_normalize(&res);
  *out = res;
  return true;
}

static inline bool c0_bigint_mul_u32_add(C0BigInt *a, uint32_t m, uint32_t add) {
  uint64_t carry = add;
  for (uint32_t i = 0; i < a->nlimbs; i++) {
    uint64_t cur = (uint64_t)a->limbs[i] * (uint64_t)m + carry;
    a->limbs[i] = (uint32_t)(cur % C0_BIGINT_BASE);
    carry = cur / C0_BIGINT_BASE;
  }
  while (carry > 0) {
    if (a->nlimbs >= C0_BIGINT_MAX_LIMBS) return false;
    a->limbs[a->nlimbs++] = (uint32_t)(carry % C0_BIGINT_BASE);
    carry /= C0_BIGINT_BASE;
  }
  if (a->nlimbs > 0 && a->sign == 0) a->sign = 1;
  c0_bigint_normalize(a);
  return true;
}

/* Exact recursive doubling division on magnitudes (matching machine.metta's
 * gslt:chr-machine:divide: for n >= 0, d > 0 -> n = q * d + r, 0 <= r < d). */
static inline bool c0_bigint_divrem_abs(const C0BigInt *n, const C0BigInt *d,
                                        C0BigInt *out_q, C0BigInt *out_r) {
  if (c0_bigint_cmp_abs(n, d) < 0) {
    c0_bigint_zero(out_q);
    *out_r = *n;
    if (out_r->nlimbs > 0) out_r->sign = 1;
    return true;
  }
  /* Build power-of-two multiples of d up to n */
  C0BigInt multiples[C0_BIGINT_MAX_LIMBS * 32];
  uint32_t nmult = 0;
  C0BigInt cur = *d;
  cur.sign = 1;
  while (c0_bigint_cmp_abs(&cur, n) <= 0) {
    if (nmult >= (uint32_t)(sizeof(multiples) / sizeof(multiples[0]))) return false;
    multiples[nmult++] = cur;
    C0BigInt next_d;
    if (!c0_bigint_add_abs(&cur, &cur, &next_d)) break;
    next_d.sign = 1;
    if (c0_bigint_cmp_abs(&next_d, n) > 0) break;
    cur = next_d;
  }
  C0BigInt q, r;
  c0_bigint_zero(&q);
  r = *n;
  r.sign = (r.nlimbs > 0) ? 1 : 0;
  for (int i = (int)nmult - 1; i >= 0; i--) {
    C0BigInt q2;
    if (!c0_bigint_add_abs(&q, &q, &q2)) return false;
    q = q2;
    if (q.nlimbs > 0) q.sign = 1;
    if (c0_bigint_cmp_abs(&r, &multiples[i]) >= 0) {
      C0BigInt r_sub;
      c0_bigint_sub_abs(&r, &multiples[i], &r_sub);
      r = r_sub;
      if (r.nlimbs > 0) r.sign = 1;
      if (!c0_bigint_mul_u32_add(&q, 1, 1)) return false;
    }
  }
  c0_bigint_normalize(&q);
  c0_bigint_normalize(&r);
  *out_q = q;
  *out_r = r;
  return true;
}

/* Truncating toward zero quotient (//) and remainder (rem), plus divisor-sign
 * modulo (mod), matching Lean's CHR.IntOperator.eval in Syntax.lean. */
static inline bool c0_bigint_divrem_trunc(const C0BigInt *a, const C0BigInt *b,
                                          C0BigInt *out_q, C0BigInt *out_r,
                                          bool *out_div_zero) {
  *out_div_zero = false;
  if (b->sign == 0 || b->nlimbs == 0) {
    *out_div_zero = true;
    return false;
  }
  if (a->sign == 0 || a->nlimbs == 0) {
    if (out_q) c0_bigint_zero(out_q);
    if (out_r) c0_bigint_zero(out_r);
    return true;
  }
  C0BigInt q, r;
  if (!c0_bigint_divrem_abs(a, b, &q, &r)) return false;
  if (q.nlimbs > 0) {
    q.sign = (a->sign == b->sign) ? 1 : -1;
  }
  if (r.nlimbs > 0) {
    r.sign = a->sign;
  }
  if (out_q) *out_q = q;
  if (out_r) *out_r = r;
  return true;
}

static inline bool c0_bigint_modulo(const C0BigInt *a, const C0BigInt *b,
                                    C0BigInt *out_m, bool *out_div_zero) {
  C0BigInt q, r;
  if (!c0_bigint_divrem_trunc(a, b, &q, &r, out_div_zero)) return false;
  if (r.sign != 0 && r.sign != b->sign) {
    return c0_bigint_add(&r, b, out_m);
  }
  *out_m = r;
  return true;
}

static inline bool c0_bigint_parse_radix(const char *s, size_t len, uint32_t radix, C0BigInt *out) {
  c0_bigint_zero(out);
  if (!s || len == 0) return false;
  size_t pos = 0;
  int8_t sign = 1;
  if (s[pos] == '+' || s[pos] == '-') {
    if (s[pos] == '-') sign = -1;
    pos++;
  }
  if (pos >= len) return false;
  for (; pos < len; pos++) {
    char c = s[pos];
    uint32_t d = 0;
    if (c >= '0' && c <= '9') d = (uint32_t)(c - '0');
    else if (c >= 'a' && c <= 'f') d = 10u + (uint32_t)(c - 'a');
    else if (c >= 'A' && c <= 'F') d = 10u + (uint32_t)(c - 'A');
    else return false;
    if (d >= radix) return false;
    if (!c0_bigint_mul_u32_add(out, radix, d)) return false;
  }
  if (out->nlimbs > 0) out->sign = sign;
  return true;
}

static inline bool c0_bigint_parse_dec(const char *s, size_t len, C0BigInt *out) {
  return c0_bigint_parse_radix(s, len, 10, out);
}

static inline bool c0_bigint_format_dec(const C0BigInt *a, char *buf, size_t cap) {
  if (!buf || cap < 2) return false;
  if (a->sign == 0 || a->nlimbs == 0) {
    buf[0] = '0';
    buf[1] = '\0';
    return true;
  }
  size_t pos = 0;
  if (a->sign < 0) {
    buf[pos++] = '-';
  }
  int top = (int)a->nlimbs - 1;
  int n = snprintf(buf + pos, cap - pos, "%u", a->limbs[top]);
  if (n < 0 || (size_t)n >= cap - pos) return false;
  pos += (size_t)n;
  for (int i = top - 1; i >= 0; i--) {
    n = snprintf(buf + pos, cap - pos, "%09u", a->limbs[i]);
    if (n < 0 || (size_t)n >= cap - pos) return false;
    pos += (size_t)n;
  }
  return true;
}

static inline uint64_t c0_bigint_hash(const C0BigInt *a) {
  uint64_t h = 1469598103934665603ULL;
  h = (h ^ (uint64_t)(uint8_t)a->sign) * 1099511628211ULL;
  h = (h ^ (uint64_t)a->nlimbs) * 1099511628211ULL;
  for (uint32_t i = 0; i < a->nlimbs; i++) {
    h = (h ^ (uint64_t)a->limbs[i]) * 1099511628211ULL;
  }
  return h;
}

/* =========================================================================
 * 2. Arbitrary-Length Byte String & Arena (GsltByteStr, GsltArena)
 * =========================================================================
 * Preserves embedded NUL bytes ('\0') and long strings without truncation.
 */
typedef struct {
  const char *bytes;
  uint32_t    len;
} GsltByteStr;

typedef struct GsltChunk {
  struct GsltChunk *next;
  size_t            cap;
  size_t            used;
  uint8_t           data[];
} GsltChunk;

typedef struct {
  GsltChunk *head;
} GsltArena;

static inline void gslt_arena_init(GsltArena *a) {
  a->head = NULL;
}

static inline void gslt_arena_free(GsltArena *a) {
  GsltChunk *c = a->head;
  while (c) {
    GsltChunk *next = c->next;
    free(c);
    c = next;
  }
  a->head = NULL;
}

static inline void *gslt_arena_alloc(GsltArena *a, size_t size) {
  size_t aligned = (size + 7u) & ~7u;
  if (!a->head || a->head->used + aligned > a->head->cap) {
    size_t cap = (aligned > 65536u) ? aligned * 2u : 65536u;
    GsltChunk *c = (GsltChunk *)calloc(1, sizeof(GsltChunk) + cap);
    if (!c) return NULL;
    c->cap = cap;
    c->used = 0;
    c->next = a->head;
    a->head = c;
  }
  void *ptr = a->head->data + a->head->used;
  a->head->used += aligned;
  return ptr;
}

static inline GsltByteStr gslt_str_intern(GsltArena *a, const char *bytes, size_t len) {
  GsltByteStr out = { "", 0 };
  char *dst = (char *)gslt_arena_alloc(a, len + 1);
  if (!dst) return out;
  if (len > 0 && bytes) memcpy(dst, bytes, len);
  dst[len] = '\0';
  out.bytes = dst;
  out.len = (uint32_t)len;
  return out;
}

static inline GsltByteStr gslt_str_from_cstr(GsltArena *a, const char *s) {
  return gslt_str_intern(a, s, s ? strlen(s) : 0);
}

static inline bool gslt_str_eq(GsltByteStr a, GsltByteStr b) {
  if (a.len != b.len) return false;
  if (a.len == 0) return true;
  return memcmp(a.bytes, b.bytes, a.len) == 0;
}

static inline bool gslt_str_eq_cstr(GsltByteStr a, const char *s) {
  size_t slen = s ? strlen(s) : 0;
  if (a.len != slen) return false;
  if (slen == 0) return true;
  return memcmp(a.bytes, s, slen) == 0;
}

static inline uint64_t gslt_str_hash(GsltByteStr s) {
  uint64_t h = 1469598103934665603ULL;
  h = (h ^ (uint64_t)s.len) * 1099511628211ULL;
  for (uint32_t i = 0; i < s.len; i++) {
    h = (h ^ (uint8_t)s.bytes[i]) * 1099511628211ULL;
  }
  return h;
}

/* Encode a Unicode scalar value (0 .. 0x10FFFF, excluding surrogates) as UTF-8. */
static inline bool gslt_unicode_is_scalar(uint64_t cp) {
  return cp <= 0x10FFFFULL && !(cp >= 0xD800ULL && cp <= 0xDFFFULL);
}

static inline size_t gslt_utf8_encode(uint32_t cp, char out[4]) {
  if (cp <= 0x7Fu) {
    out[0] = (char)cp;
    return 1;
  } else if (cp <= 0x7FFu) {
    out[0] = (char)(0xC0u | (cp >> 6));
    out[1] = (char)(0x80u | (cp & 0x3Fu));
    return 2;
  } else if (cp <= 0xFFFFu) {
    out[0] = (char)(0xE0u | (cp >> 12));
    out[1] = (char)(0x80u | ((cp >> 6) & 0x3Fu));
    out[2] = (char)(0x80u | (cp & 0x3Fu));
    return 3;
  } else {
    out[0] = (char)(0xF0u | (cp >> 18));
    out[1] = (char)(0x80u | ((cp >> 12) & 0x3Fu));
    out[2] = (char)(0x80u | ((cp >> 6) & 0x3Fu));
    out[3] = (char)(0x80u | (cp & 0x3Fu));
    return 4;
  }
}

/* Decode one UTF-8 codepoint starting at s[0..len-1]. Returns bytes consumed (0 on invalid). */
static inline size_t gslt_utf8_decode(const char *s, size_t len, uint32_t *out_cp) {
  if (len == 0) return 0;
  uint8_t b0 = (uint8_t)s[0];
  if (b0 < 0x80u) {
    *out_cp = b0;
    return 1;
  } else if ((b0 & 0xE0u) == 0xC0u) {
    if (len < 2) return 0;
    uint8_t b1 = (uint8_t)s[1];
    if ((b1 & 0xC0u) != 0x80u) return 0;
    uint32_t cp = ((uint32_t)(b0 & 0x1Fu) << 6) | (uint32_t)(b1 & 0x3Fu);
    if (cp < 0x80u) return 0;
    *out_cp = cp;
    return 2;
  } else if ((b0 & 0xF0u) == 0xE0u) {
    if (len < 3) return 0;
    uint8_t b1 = (uint8_t)s[1], b2 = (uint8_t)s[2];
    if ((b1 & 0xC0u) != 0x80u || (b2 & 0xC0u) != 0x80u) return 0;
    uint32_t cp = ((uint32_t)(b0 & 0x0Fu) << 12) | ((uint32_t)(b1 & 0x3Fu) << 6) | (uint32_t)(b2 & 0x3Fu);
    if (cp < 0x800u || !gslt_unicode_is_scalar(cp)) return 0;
    *out_cp = cp;
    return 3;
  } else if ((b0 & 0xF8u) == 0xF0u) {
    if (len < 4) return 0;
    uint8_t b1 = (uint8_t)s[1], b2 = (uint8_t)s[2], b3 = (uint8_t)s[3];
    if ((b1 & 0xC0u) != 0x80u || (b2 & 0xC0u) != 0x80u || (b3 & 0xC0u) != 0x80u) return 0;
    uint32_t cp = ((uint32_t)(b0 & 0x07u) << 18) | ((uint32_t)(b1 & 0x3Fu) << 12) |
                  ((uint32_t)(b2 & 0x3Fu) << 6) | (uint32_t)(b3 & 0x3Fu);
    if (cp < 0x10000u || !gslt_unicode_is_scalar(cp)) return 0;
    *out_cp = cp;
    return 4;
  }
  return 0;
}

/* =========================================================================
 * 3. Generic S-Expression & SyntaxGSLT Packet / Catalogue Reader
 * ========================================================================= */
typedef enum {
  GSLT_SEXPR_SYM  = 1,
  GSLT_SEXPR_STR  = 2,
  GSLT_SEXPR_INT  = 3,
  GSLT_SEXPR_LIST = 4
} GsltSexprKind;

typedef struct GsltSexpr {
  GsltSexprKind      kind;
  GsltByteStr        text;     /* symbol or string or integer digits */
  C0BigInt           int_val;  /* populated when kind == GSLT_SEXPR_INT */
  uint32_t           nitems;
  struct GsltSexpr **items;
} GsltSexpr;

typedef struct {
  const char *src;
  size_t      len;
  size_t      pos;
  GsltArena  *arena;
  char        err[256];
} GsltSexprParser;

static inline void gslt_sexpr_skip_ws(GsltSexprParser *p) {
  while (p->pos < p->len) {
    char c = p->src[p->pos];
    if (c == ' ' || c == '\t' || c == '\n' || c == '\r') {
      p->pos++;
    } else if (c == ';') {
      while (p->pos < p->len && p->src[p->pos] != '\n') p->pos++;
    } else {
      break;
    }
  }
}

static GsltSexpr *gslt_sexpr_parse_one(GsltSexprParser *p) {
  gslt_sexpr_skip_ws(p);
  if (p->pos >= p->len) {
    snprintf(p->err, sizeof(p->err), "unexpected EOF in S-expression");
    return NULL;
  }
  char c = p->src[p->pos];
  if (c == '(' || c == '[') {
    char close_ch = (c == '(') ? ')' : ']';
    p->pos++;
    uint32_t cap = 8, count = 0;
    GsltSexpr **items = (GsltSexpr **)gslt_arena_alloc(p->arena, cap * sizeof(GsltSexpr *));
    if (!items) return NULL;
    while (true) {
      gslt_sexpr_skip_ws(p);
      if (p->pos >= p->len) {
        snprintf(p->err, sizeof(p->err), "unterminated '%c' in S-expression", c);
        return NULL;
      }
      if (p->src[p->pos] == close_ch) {
        p->pos++;
        break;
      }
      GsltSexpr *child = gslt_sexpr_parse_one(p);
      if (!child) return NULL;
      if (count >= cap) {
        uint32_t new_cap = cap * 2;
        GsltSexpr **new_items = (GsltSexpr **)gslt_arena_alloc(p->arena, new_cap * sizeof(GsltSexpr *));
        if (!new_items) return NULL;
        memcpy(new_items, items, count * sizeof(GsltSexpr *));
        items = new_items;
        cap = new_cap;
      }
      items[count++] = child;
    }
    GsltSexpr *node = (GsltSexpr *)gslt_arena_alloc(p->arena, sizeof(GsltSexpr));
    if (!node) return NULL;
    node->kind = GSLT_SEXPR_LIST;
    node->nitems = count;
    node->items = items;
    return node;
  } else if (c == ')' || c == ']') {
    snprintf(p->err, sizeof(p->err), "unexpected '%c' in S-expression", c);
    return NULL;
  } else if (c == '"') {
    p->pos++;
    size_t cap = 64, blen = 0;
    char *buf = (char *)gslt_arena_alloc(p->arena, cap);
    if (!buf) return NULL;
    while (p->pos < p->len && p->src[p->pos] != '"') {
      char ch = p->src[p->pos++];
      if (ch == '\\') {
        if (p->pos >= p->len) {
          snprintf(p->err, sizeof(p->err), "unterminated string escape in S-expression");
          return NULL;
        }
        char esc = p->src[p->pos++];
        switch (esc) {
          case '"': ch = '"'; break;
          case '\\': ch = '\\'; break;
          case 'n': ch = '\n'; break;
          case 'r': ch = '\r'; break;
          case 't': ch = '\t'; break;
          case 'a': ch = '\a'; break;
          case 'b': ch = '\b'; break;
          case 'v': ch = '\v'; break;
          case 'f': ch = '\f'; break;
          case '0': ch = '\0'; break;
          case 'x': {
            if (p->pos + 2 <= p->len && isxdigit((unsigned char)p->src[p->pos]) &&
                isxdigit((unsigned char)p->src[p->pos + 1])) {
              char hex[3] = { p->src[p->pos], p->src[p->pos + 1], '\0' };
              ch = (char)strtoul(hex, NULL, 16);
              p->pos += 2;
            } else {
              ch = esc;
            }
            break;
          }
          default: ch = esc; break;
        }
      }
      if (blen + 1 >= cap) {
        size_t new_cap = cap * 2;
        char *new_buf = (char *)gslt_arena_alloc(p->arena, new_cap);
        if (!new_buf) return NULL;
        memcpy(new_buf, buf, blen);
        buf = new_buf;
        cap = new_cap;
      }
      buf[blen++] = ch;
    }
    if (p->pos >= p->len || p->src[p->pos] != '"') {
      snprintf(p->err, sizeof(p->err), "unterminated string literal in S-expression");
      return NULL;
    }
    p->pos++;
    buf[blen] = '\0';
    GsltSexpr *node = (GsltSexpr *)gslt_arena_alloc(p->arena, sizeof(GsltSexpr));
    if (!node) return NULL;
    node->kind = GSLT_SEXPR_STR;
    node->text.bytes = buf;
    node->text.len = (uint32_t)blen;
    return node;
  } else {
    size_t start = p->pos;
    while (p->pos < p->len) {
      char ch = p->src[p->pos];
      if (ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r' ||
          ch == '(' || ch == ')' || ch == '[' || ch == ']' || ch == ';') {
        break;
      }
      p->pos++;
    }
    size_t tlen = p->pos - start;
    GsltSexpr *node = (GsltSexpr *)gslt_arena_alloc(p->arena, sizeof(GsltSexpr));
    if (!node) return NULL;
    node->text = gslt_str_intern(p->arena, p->src + start, tlen);
    /* Check if token is a signed/unsigned decimal integer */
    C0BigInt bval;
    bool is_int = false;
    if (tlen > 0) {
      size_t idx = (p->src[start] == '-' || p->src[start] == '+') ? 1 : 0;
      if (idx < tlen) {
        is_int = true;
        for (size_t i = idx; i < tlen; i++) {
          if (p->src[start + i] < '0' || p->src[start + i] > '9') {
            is_int = false;
            break;
          }
        }
      }
    }
    if (is_int && c0_bigint_parse_dec(node->text.bytes, node->text.len, &bval)) {
      node->kind = GSLT_SEXPR_INT;
      node->int_val = bval;
    } else {
      node->kind = GSLT_SEXPR_SYM;
    }
    return node;
  }
}

static inline GsltSexpr *gslt_sexpr_parse_all(GsltArena *arena, const char *src, size_t len,
                                              char *err, size_t err_cap) {
  GsltSexprParser p;
  p.src = src;
  p.len = len;
  p.pos = 0;
  p.arena = arena;
  p.err[0] = '\0';
  GsltSexpr *root = gslt_sexpr_parse_one(&p);
  if (!root) {
    if (err && err_cap > 0) snprintf(err, err_cap, "%s", p.err[0] ? p.err : "invalid S-expression");
    return NULL;
  }
  gslt_sexpr_skip_ws(&p);
  if (p.pos != p.len) {
    if (err && err_cap > 0) snprintf(err, err_cap, "trailing tokens after S-expression at byte %zu", p.pos);
    return NULL;
  }
  return root;
}

/* ---- SyntaxGSLT Packet Helpers: (node label fields), (pair a b), nil, (cp n) ---- */
static inline bool gslt_packet_is_node(const GsltSexpr *s, GsltByteStr *out_label, const GsltSexpr **out_fields) {
  if (!s || s->kind != GSLT_SEXPR_LIST || s->nitems != 3) return false;
  if (s->items[0]->kind != GSLT_SEXPR_SYM || !gslt_str_eq_cstr(s->items[0]->text, "node")) return false;
  if (s->items[1]->kind != GSLT_SEXPR_SYM && s->items[1]->kind != GSLT_SEXPR_STR) return false;
  if (out_label) *out_label = s->items[1]->text;
  if (out_fields) *out_fields = s->items[2];
  return true;
}

static inline bool gslt_packet_node_label_eq(const GsltSexpr *s, const char *label) {
  GsltByteStr lbl;
  if (!gslt_packet_is_node(s, &lbl, NULL)) return false;
  return gslt_str_eq_cstr(lbl, label);
}

/* Extract children from a pair/nil spine. Refuses truncated/malformed spines. */
static inline bool gslt_packet_fields(GsltArena *arena, const GsltSexpr *fields,
                                      const GsltSexpr ***out_children, uint32_t *out_count) {
  uint32_t cap = 8, count = 0;
  const GsltSexpr **arr = (const GsltSexpr **)gslt_arena_alloc(arena, cap * sizeof(const GsltSexpr *));
  if (!arr) return false;
  const GsltSexpr *cur = fields;
  while (cur) {
    if (cur->kind == GSLT_SEXPR_SYM && gslt_str_eq_cstr(cur->text, "nil")) {
      *out_children = arr;
      *out_count = count;
      return true;
    }
    if (cur->kind == GSLT_SEXPR_LIST && cur->nitems == 3 &&
        cur->items[0]->kind == GSLT_SEXPR_SYM && gslt_str_eq_cstr(cur->items[0]->text, "pair")) {
      if (count >= cap) {
        uint32_t new_cap = cap * 2;
        const GsltSexpr **new_arr = (const GsltSexpr **)gslt_arena_alloc(arena, new_cap * sizeof(const GsltSexpr *));
        if (!new_arr) return false;
        memcpy(new_arr, arr, count * sizeof(const GsltSexpr *));
        arr = new_arr;
        cap = new_cap;
      }
      arr[count++] = cur->items[1];
      cur = cur->items[2];
    } else {
      return false;
    }
  }
  return false;
}

/* Extract scalar codepoint from (node <label> (cp <n>)). Validates Unicode scalar range. */
static inline bool gslt_packet_scalar_cp(const GsltSexpr *s, uint32_t *out_cp) {
  GsltByteStr lbl;
  const GsltSexpr *fields = NULL;
  if (!gslt_packet_is_node(s, &lbl, &fields)) return false;
  if (!fields || fields->kind != GSLT_SEXPR_LIST || fields->nitems != 2) return false;
  if (fields->items[0]->kind != GSLT_SEXPR_SYM || !gslt_str_eq_cstr(fields->items[0]->text, "cp")) return false;
  if (fields->items[1]->kind != GSLT_SEXPR_INT) return false;
  uint64_t v = 0;
  if (!c0_bigint_to_u64(&fields->items[1]->int_val, &v)) return false;
  if (!gslt_unicode_is_scalar(v)) return false;
  *out_cp = (uint32_t)v;
  return true;
}

/* Unwrap (result <tree> nil) */
static inline const GsltSexpr *gslt_packet_unwrap_result(const GsltSexpr *pkt) {
  if (!pkt || pkt->kind != GSLT_SEXPR_LIST || pkt->nitems != 3) return NULL;
  if (pkt->items[0]->kind != GSLT_SEXPR_SYM || !gslt_str_eq_cstr(pkt->items[0]->text, "result")) return NULL;
  if (pkt->items[2]->kind != GSLT_SEXPR_SYM || !gslt_str_eq_cstr(pkt->items[2]->text, "nil")) return NULL;
  return pkt->items[1];
}

/* Reconstruct the exact concatenated source bytes from all (cp <n>) leaves of a packet tree,
 * while counting structural nodes and scalar leaves and validating spine integrity. */
typedef struct {
  uint32_t    packet_index;
  GsltByteStr root_label;
  uint32_t    node_count;
  uint32_t    cp_count;
  GsltByteStr replayed_source;
} GsltPacketProvenance;

static inline bool gslt_packet_replay_walk(GsltArena *arena, const GsltSexpr *tree,
                                           char **buf, size_t *len, size_t *cap,
                                           uint32_t *nodes, uint32_t *cps) {
  GsltByteStr lbl;
  const GsltSexpr *fields = NULL;
  if (!gslt_packet_is_node(tree, &lbl, &fields)) return false;
  (*nodes)++;
  /* Check if fields is (cp <n>) */
  if (fields && fields->kind == GSLT_SEXPR_LIST && fields->nitems == 2 &&
      fields->items[0]->kind == GSLT_SEXPR_SYM && gslt_str_eq_cstr(fields->items[0]->text, "cp")) {
    uint32_t cp = 0;
    if (!gslt_packet_scalar_cp(tree, &cp)) return false;
    (*cps)++;
    char utf8[4];
    size_t ulen = gslt_utf8_encode(cp, utf8);
    if (*len + ulen + 1 >= *cap) {
      size_t new_cap = (*cap) * 2;
      char *new_buf = (char *)gslt_arena_alloc(arena, new_cap);
      if (!new_buf) return false;
      memcpy(new_buf, *buf, *len);
      *buf = new_buf;
      *cap = new_cap;
    }
    memcpy(*buf + *len, utf8, ulen);
    *len += ulen;
    (*buf)[*len] = '\0';
    return true;
  }
  const GsltSexpr **children = NULL;
  uint32_t nchildren = 0;
  if (!gslt_packet_fields(arena, fields, &children, &nchildren)) return false;
  for (uint32_t i = 0; i < nchildren; i++) {
    if (!gslt_packet_replay_walk(arena, children[i], buf, len, cap, nodes, cps)) return false;
  }
  return true;
}

static inline bool gslt_packet_inspect(GsltArena *arena, const GsltSexpr *tree,
                                       uint32_t idx, GsltPacketProvenance *out_prov) {
  GsltByteStr lbl;
  const GsltSexpr *fields = NULL;
  if (!gslt_packet_is_node(tree, &lbl, &fields)) return false;
  size_t cap = 256, len = 0;
  char *buf = (char *)gslt_arena_alloc(arena, cap);
  if (!buf) return false;
  buf[0] = '\0';
  uint32_t nodes = 0, cps = 0;
  if (!gslt_packet_replay_walk(arena, tree, &buf, &len, &cap, &nodes, &cps)) return false;
  out_prov->packet_index = idx;
  out_prov->root_label = lbl;
  out_prov->node_count = nodes;
  out_prov->cp_count = cps;
  out_prov->replayed_source.bytes = buf;
  out_prov->replayed_source.len = (uint32_t)len;
  return true;
}

/* =========================================================================
 * 4. Generated C0 Operator Table (72 Operators from CHRPrologSyntax.lean)
 * ========================================================================= */
typedef enum {
  GSLT_OP_FX  = 1,
  GSLT_OP_FY  = 2,
  GSLT_OP_XF  = 3,
  GSLT_OP_YF  = 4,
  GSLT_OP_XFX = 5,
  GSLT_OP_XFY = 6,
  GSLT_OP_YFX = 7
} GsltOpSpec;

typedef struct {
  const char *name;
  GsltOpSpec  spec;
  uint16_t    priority;
} GsltPrologOp;

enum { GSLT_C0_NUM_OPERATORS = 72 };

static const GsltPrologOp GSLT_C0_OPERATORS[GSLT_C0_NUM_OPERATORS] = {
  /*  0 */ { "<=>",                   GSLT_OP_XFX, 1180 },
  /*  1 */ { "==>",                   GSLT_OP_XFX, 1180 },
  /*  2 */ { "\\",                    GSLT_OP_XFX, 1100 },
  /*  3 */ { "@",                     GSLT_OP_XFX, 1200 },
  /*  4 */ { "chr_constraint",        GSLT_OP_FX,  1150 },
  /*  5 */ { "$",                     GSLT_OP_FX,     1 },
  /*  6 */ { ".",                     GSLT_OP_YFX,  100 },
  /*  7 */ { "+",                     GSLT_OP_FY,   200 },
  /*  8 */ { "-",                     GSLT_OP_FY,   200 },
  /*  9 */ { "\\",                    GSLT_OP_FY,   200 },
  /* 10 */ { "**",                    GSLT_OP_XFX,  200 },
  /* 11 */ { "^",                     GSLT_OP_XFY,  200 },
  /* 12 */ { "*",                     GSLT_OP_YFX,  400 },
  /* 13 */ { "/",                     GSLT_OP_YFX,  400 },
  /* 14 */ { "//",                    GSLT_OP_YFX,  400 },
  /* 15 */ { "<<",                    GSLT_OP_YFX,  400 },
  /* 16 */ { ">>",                    GSLT_OP_YFX,  400 },
  /* 17 */ { "div",                   GSLT_OP_YFX,  400 },
  /* 18 */ { "mod",                   GSLT_OP_YFX,  400 },
  /* 19 */ { "rdiv",                  GSLT_OP_YFX,  400 },
  /* 20 */ { "rem",                   GSLT_OP_YFX,  400 },
  /* 21 */ { "xor",                   GSLT_OP_YFX,  400 },
  /* 22 */ { "+",                     GSLT_OP_YFX,  500 },
  /* 23 */ { "-",                     GSLT_OP_YFX,  500 },
  /* 24 */ { "/\\",                   GSLT_OP_YFX,  500 },
  /* 25 */ { "\\/",                   GSLT_OP_YFX,  500 },
  /* 26 */ { ":",                     GSLT_OP_XFY,  600 },
  /* 27 */ { ":<",                    GSLT_OP_XFX,  700 },
  /* 28 */ { "<",                     GSLT_OP_XFX,  700 },
  /* 29 */ { "=",                     GSLT_OP_XFX,  700 },
  /* 30 */ { "=..",                   GSLT_OP_XFX,  700 },
  /* 31 */ { "=:=",                   GSLT_OP_XFX,  700 },
  /* 32 */ { "=<",                    GSLT_OP_XFX,  700 },
  /* 33 */ { "==",                    GSLT_OP_XFX,  700 },
  /* 34 */ { "=@=",                   GSLT_OP_XFX,  700 },
  /* 35 */ { "=\\=",                  GSLT_OP_XFX,  700 },
  /* 36 */ { ">",                     GSLT_OP_XFX,  700 },
  /* 37 */ { ">:<",                   GSLT_OP_XFX,  700 },
  /* 38 */ { ">=",                    GSLT_OP_XFX,  700 },
  /* 39 */ { "@<",                    GSLT_OP_XFX,  700 },
  /* 40 */ { "@=<",                   GSLT_OP_XFX,  700 },
  /* 41 */ { "@>",                    GSLT_OP_XFX,  700 },
  /* 42 */ { "@>=",                   GSLT_OP_XFX,  700 },
  /* 43 */ { "\\=",                   GSLT_OP_XFX,  700 },
  /* 44 */ { "\\==",                  GSLT_OP_XFX,  700 },
  /* 45 */ { "\\=@=",                 GSLT_OP_XFX,  700 },
  /* 46 */ { "as",                    GSLT_OP_XFX,  700 },
  /* 47 */ { "is",                    GSLT_OP_XFX,  700 },
  /* 48 */ { ":=",                    GSLT_OP_XFX,  800 },
  /* 49 */ { "\\+",                   GSLT_OP_FY,   900 },
  /* 50 */ { ",",                     GSLT_OP_XFY, 1000 },
  /* 51 */ { "*->",                   GSLT_OP_XFY, 1050 },
  /* 52 */ { "->",                    GSLT_OP_XFY, 1050 },
  /* 53 */ { ";",                     GSLT_OP_XFY, 1100 },
  /* 54 */ { "|",                     GSLT_OP_XFY, 1105 },
  /* 55 */ { "discontiguous",         GSLT_OP_FX,  1150 },
  /* 56 */ { "dynamic",               GSLT_OP_FX,  1150 },
  /* 57 */ { "initialization",        GSLT_OP_FX,  1150 },
  /* 58 */ { "meta_predicate",        GSLT_OP_FX,  1150 },
  /* 59 */ { "module_transparent",    GSLT_OP_FX,  1150 },
  /* 60 */ { "multifile",             GSLT_OP_FX,  1150 },
  /* 61 */ { "public",                GSLT_OP_FX,  1150 },
  /* 62 */ { "table",                 GSLT_OP_FX,  1150 },
  /* 63 */ { "thread_initialization", GSLT_OP_FX,  1150 },
  /* 64 */ { "thread_local",          GSLT_OP_FX,  1150 },
  /* 65 */ { "volatile",              GSLT_OP_FX,  1150 },
  /* 66 */ { ":-",                    GSLT_OP_FX,  1200 },
  /* 67 */ { "?-",                    GSLT_OP_FX,  1200 },
  /* 68 */ { "-->",                   GSLT_OP_XFX, 1200 },
  /* 69 */ { ":-",                    GSLT_OP_XFX, 1200 },
  /* 70 */ { "==>",                   GSLT_OP_XFX, 1200 },
  /* 71 */ { "=>",                    GSLT_OP_XFX, 1200 }
};

static inline bool gslt_c0_is_layout(GsltByteStr label) {
  return gslt_str_eq_cstr(label, "pl:layout-empty") ||
         gslt_str_eq_cstr(label, "pl:layout-space") ||
         gslt_str_eq_cstr(label, "pl:layout-line") ||
         gslt_str_eq_cstr(label, "pl:layout-line-end") ||
         gslt_str_eq_cstr(label, "pl:layout-block");
}

static inline bool gslt_d0_is_layout(GsltByteStr label) {
  return gslt_str_eq_cstr(label, "dl-src:trivia-empty") ||
         gslt_str_eq_cstr(label, "dl-src:trivia-space") ||
         gslt_str_eq_cstr(label, "dl-src:trivia-line-comment") ||
         gslt_str_eq_cstr(label, "dl-src:trivia-line-comment-eof") ||
         gslt_str_eq_cstr(label, "dl-src:trivia-block-comment") ||
         gslt_str_eq_cstr(label, "dl-src:directive-space");
}

/* =========================================================================
 * 5. Prolog Term AST (GsltPlTerm) & C0 Packet Reader (reader.metta)
 * ========================================================================= */
typedef enum {
  GSLT_PL_VAR      = 1,
  GSLT_PL_FRESH    = 2,
  GSLT_PL_INT      = 3,
  GSLT_PL_ATOM     = 4,
  GSLT_PL_COMPOUND = 5
} GsltPlTermKind;

typedef struct GsltPlTerm {
  GsltPlTermKind      kind;
  GsltByteStr         name;   /* variable spelling or atom/functor name */
  C0BigInt            ival;   /* integer value when kind == GSLT_PL_INT */
  uint32_t            nargs;
  struct GsltPlTerm **args;
} GsltPlTerm;

static inline GsltPlTerm *gslt_pl_make_var(GsltArena *a, GsltByteStr spelling) {
  GsltPlTerm *t = (GsltPlTerm *)gslt_arena_alloc(a, sizeof(GsltPlTerm));
  if (!t) return NULL;
  if (gslt_str_eq_cstr(spelling, "_")) {
    t->kind = GSLT_PL_FRESH;
  } else {
    t->kind = GSLT_PL_VAR;
    t->name = spelling;
  }
  return t;
}

static inline GsltPlTerm *gslt_pl_make_int(GsltArena *a, const C0BigInt *v) {
  GsltPlTerm *t = (GsltPlTerm *)gslt_arena_alloc(a, sizeof(GsltPlTerm));
  if (!t) return NULL;
  t->kind = GSLT_PL_INT;
  t->ival = *v;
  return t;
}

static inline GsltPlTerm *gslt_pl_make_atom(GsltArena *a, GsltByteStr name) {
  GsltPlTerm *t = (GsltPlTerm *)gslt_arena_alloc(a, sizeof(GsltPlTerm));
  if (!t) return NULL;
  t->kind = GSLT_PL_ATOM;
  t->name = name;
  return t;
}

static inline GsltPlTerm *gslt_pl_make_compound(GsltArena *a, GsltByteStr name,
                                                uint32_t nargs, GsltPlTerm **args) {
  GsltPlTerm *t = (GsltPlTerm *)gslt_arena_alloc(a, sizeof(GsltPlTerm));
  if (!t) return NULL;
  t->kind = GSLT_PL_COMPOUND;
  t->name = name;
  t->nargs = nargs;
  if (nargs > 0) {
    t->args = (GsltPlTerm **)gslt_arena_alloc(a, nargs * sizeof(GsltPlTerm *));
    if (!t->args) return NULL;
    memcpy(t->args, args, nargs * sizeof(GsltPlTerm *));
  }
  return t;
}

/* ---- C0 Packet Reader (matches hyperon/cetta-prime-nik-20260811/langdef/lang/chr/reader.metta) ---- */
static inline bool gslt_c0_pkt_digits_str(GsltArena *a, const GsltSexpr *node,
                                          char **buf, size_t *len, size_t *cap) {
  GsltByteStr lbl;
  const GsltSexpr *fields = NULL;
  if (!gslt_packet_is_node(node, &lbl, &fields)) return false;
  uint32_t cp = 0;
  if (gslt_packet_scalar_cp(node, &cp)) {
    char u[4];
    size_t ulen = gslt_utf8_encode(cp, u);
    if (*len + ulen + 1 >= *cap) {
      size_t ncap = (*cap) * 2;
      char *nbuf = (char *)gslt_arena_alloc(a, ncap);
      if (!nbuf) return false;
      memcpy(nbuf, *buf, *len);
      *buf = nbuf;
      *cap = ncap;
    }
    memcpy(*buf + *len, u, ulen);
    *len += ulen;
    (*buf)[*len] = '\0';
    return true;
  }
  const GsltSexpr **ch = NULL;
  uint32_t nch = 0;
  if (!gslt_packet_fields(a, fields, &ch, &nch)) return false;
  for (uint32_t i = 0; i < nch; i++) {
    if (!gslt_c0_pkt_digits_str(a, ch[i], buf, len, cap)) return false;
  }
  return true;
}

static inline bool gslt_c0_pkt_text_of(GsltArena *a, const GsltSexpr *node, GsltByteStr *out) {
  size_t cap = 64, len = 0;
  char *buf = (char *)gslt_arena_alloc(a, cap);
  if (!buf) return false;
  buf[0] = '\0';
  if (!gslt_c0_pkt_digits_str(a, node, &buf, &len, &cap)) return false;
  out->bytes = buf;
  out->len = (uint32_t)len;
  return true;
}

static inline bool gslt_c0_pkt_read_escape(GsltArena *a, const GsltSexpr *node,
                                           uint32_t *out_cp, char *err, size_t err_cap) {
  GsltByteStr lbl;
  const GsltSexpr *fields = NULL;
  if (!gslt_packet_is_node(node, &lbl, &fields)) {
    snprintf(err, err_cap, "the source reader met an unexpected term");
    return false;
  }
  const GsltSexpr **ch = NULL;
  uint32_t nch = 0;
  if (!gslt_packet_fields(a, fields, &ch, &nch) || nch == 0) {
    snprintf(err, err_cap, "the source reader met an unexpected term");
    return false;
  }
  if (gslt_str_eq_cstr(lbl, "pl:escape-named")) {
    uint32_t cp = 0;
    if (!gslt_packet_scalar_cp(ch[0], &cp)) {
      snprintf(err, err_cap, "the source reader met an unexpected term");
      return false;
    }
    switch (cp) {
      case 'a': *out_cp = 7; return true;
      case 'b': *out_cp = 8; return true;
      case 't': *out_cp = 9; return true;
      case 'n': *out_cp = 10; return true;
      case 'v': *out_cp = 11; return true;
      case 'f': *out_cp = 12; return true;
      case 'r': *out_cp = 13; return true;
      case 'e': *out_cp = 27; return true;
      case 's': *out_cp = 32; return true;
      case 'd': *out_cp = 127; return true;
      case '\\': *out_cp = '\\'; return true;
      case '\'': *out_cp = '\''; return true;
      case '"': *out_cp = '"'; return true;
      case '`': *out_cp = '`'; return true;
      default:
        snprintf(err, err_cap, "the source holds an escape the reader does not define");
        return false;
    }
  }
  uint32_t radix = 0;
  if (gslt_str_eq_cstr(lbl, "pl:escape-hex") ||
      gslt_str_eq_cstr(lbl, "pl:escape-open-hex") ||
      gslt_str_eq_cstr(lbl, "pl:escape-u4") ||
      gslt_str_eq_cstr(lbl, "pl:escape-u8")) {
    radix = 16;
  } else if (gslt_str_eq_cstr(lbl, "pl:escape-oct") ||
             gslt_str_eq_cstr(lbl, "pl:escape-open-oct")) {
    radix = 8;
  } else {
    snprintf(err, err_cap, "the source reader met an unexpected term");
    return false;
  }
  GsltByteStr digits;
  if (!gslt_c0_pkt_text_of(a, node, &digits)) {
    snprintf(err, err_cap, "the source reader met an unexpected term");
    return false;
  }
  C0BigInt val;
  if (!c0_bigint_parse_radix(digits.bytes, digits.len, radix, &val)) {
    snprintf(err, err_cap, "a character code escape names no Unicode scalar value");
    return false;
  }
  uint64_t uval = 0;
  if (!c0_bigint_to_u64(&val, &uval) || !gslt_unicode_is_scalar(uval)) {
    snprintf(err, err_cap, "a character code escape names no Unicode scalar value");
    return false;
  }
  *out_cp = (uint32_t)uval;
  return true;
}

static inline bool gslt_c0_pkt_read_quoted_body(GsltArena *a, const GsltSexpr *node,
                                                char **buf, size_t *len, size_t *cap,
                                                char *err, size_t err_cap) {
  GsltByteStr lbl;
  const GsltSexpr *fields = NULL;
  if (!gslt_packet_is_node(node, &lbl, &fields)) {
    snprintf(err, err_cap, "the source reader met an unexpected term");
    return false;
  }
  if (gslt_str_eq_cstr(lbl, "pl:single-empty") ||
      gslt_str_eq_cstr(lbl, "pl:double-empty") ||
      gslt_str_eq_cstr(lbl, "pl:back-empty")) {
    return true;
  }
  const GsltSexpr **ch = NULL;
  uint32_t nch = 0;
  if (!gslt_packet_fields(a, fields, &ch, &nch)) {
    snprintf(err, err_cap, "the source reader met an unexpected term");
    return false;
  }
  if ((gslt_str_eq_cstr(lbl, "pl:single-quote") ||
       gslt_str_eq_cstr(lbl, "pl:double-quote") ||
       gslt_str_eq_cstr(lbl, "pl:back-quote")) && nch == 1) {
    char q = gslt_str_eq_cstr(lbl, "pl:single-quote") ? '\'' :
             (gslt_str_eq_cstr(lbl, "pl:double-quote") ? '"' : '`');
    if (*len + 2 >= *cap) {
      size_t ncap = (*cap) * 2;
      char *nbuf = (char *)gslt_arena_alloc(a, ncap);
      if (!nbuf) return false;
      memcpy(nbuf, *buf, *len);
      *buf = nbuf;
      *cap = ncap;
    }
    (*buf)[(*len)++] = q;
    (*buf)[*len] = '\0';
    return gslt_c0_pkt_read_quoted_body(a, ch[0], buf, len, cap, err, err_cap);
  }
  if ((gslt_str_eq_cstr(lbl, "pl:single-line") ||
       gslt_str_eq_cstr(lbl, "pl:double-line") ||
       gslt_str_eq_cstr(lbl, "pl:back-line")) && nch == 1) {
    return gslt_c0_pkt_read_quoted_body(a, ch[0], buf, len, cap, err, err_cap);
  }
  if ((gslt_str_eq_cstr(lbl, "pl:single-more") ||
       gslt_str_eq_cstr(lbl, "pl:double-more") ||
       gslt_str_eq_cstr(lbl, "pl:back-more")) && nch == 2) {
    uint32_t cp = 0;
    if (!gslt_packet_scalar_cp(ch[0], &cp)) {
      snprintf(err, err_cap, "a character code escape names no Unicode scalar value");
      return false;
    }
    char u[4];
    size_t ulen = gslt_utf8_encode(cp, u);
    if (*len + ulen + 1 >= *cap) {
      size_t ncap = (*cap) * 2;
      char *nbuf = (char *)gslt_arena_alloc(a, ncap);
      if (!nbuf) return false;
      memcpy(nbuf, *buf, *len);
      *buf = nbuf;
      *cap = ncap;
    }
    memcpy(*buf + *len, u, ulen);
    *len += ulen;
    (*buf)[*len] = '\0';
    return gslt_c0_pkt_read_quoted_body(a, ch[1], buf, len, cap, err, err_cap);
  }
  if ((gslt_str_eq_cstr(lbl, "pl:single-escape") ||
       gslt_str_eq_cstr(lbl, "pl:double-escape") ||
       gslt_str_eq_cstr(lbl, "pl:back-escape")) && nch == 2) {
    uint32_t cp = 0;
    if (!gslt_c0_pkt_read_escape(a, ch[0], &cp, err, err_cap)) return false;
    char u[4];
    size_t ulen = gslt_utf8_encode(cp, u);
    if (*len + ulen + 1 >= *cap) {
      size_t ncap = (*cap) * 2;
      char *nbuf = (char *)gslt_arena_alloc(a, ncap);
      if (!nbuf) return false;
      memcpy(nbuf, *buf, *len);
      *buf = nbuf;
      *cap = ncap;
    }
    memcpy(*buf + *len, u, ulen);
    *len += ulen;
    (*buf)[*len] = '\0';
    return gslt_c0_pkt_read_quoted_body(a, ch[1], buf, len, cap, err, err_cap);
  }
  snprintf(err, err_cap, "the source reader met an unexpected term");
  return false;
}

static inline bool gslt_c0_pkt_read_atom_node(GsltArena *a, const GsltSexpr *node,
                                              GsltByteStr *out_name, char *err, size_t err_cap) {
  GsltByteStr lbl;
  const GsltSexpr *fields = NULL;
  if (!gslt_packet_is_node(node, &lbl, &fields)) {
    snprintf(err, err_cap, "the source reader met an unexpected term");
    return false;
  }
  if (gslt_str_eq_cstr(lbl, "pl:atom-cut")) {
    *out_name = gslt_str_from_cstr(a, "!");
    return true;
  }
  if (gslt_str_eq_cstr(lbl, "pl:atom-semicolon")) {
    *out_name = gslt_str_from_cstr(a, ";");
    return true;
  }
  const GsltSexpr **ch = NULL;
  uint32_t nch = 0;
  if (!gslt_packet_fields(a, fields, &ch, &nch) || nch != 1) {
    snprintf(err, err_cap, "the source reader met an unexpected term");
    return false;
  }
  if (gslt_str_eq_cstr(lbl, "pl:atom-quoted")) {
    size_t cap = 64, len = 0;
    char *buf = (char *)gslt_arena_alloc(a, cap);
    if (!buf) return false;
    buf[0] = '\0';
    if (!gslt_c0_pkt_read_quoted_body(a, ch[0], &buf, &len, &cap, err, err_cap)) return false;
    out_name->bytes = buf;
    out_name->len = (uint32_t)len;
    return true;
  }
  if (gslt_str_eq_cstr(lbl, "pl:atom-word") || gslt_str_eq_cstr(lbl, "pl:atom-graphic")) {
    return gslt_c0_pkt_text_of(a, ch[0], out_name);
  }
  snprintf(err, err_cap, "the source reader met an unexpected term");
  return false;
}

static inline bool gslt_c0_pkt_read_number_node(GsltArena *a, const GsltSexpr *node,
                                                C0BigInt *out_val, char *err, size_t err_cap) {
  GsltByteStr lbl;
  const GsltSexpr *fields = NULL;
  if (!gslt_packet_is_node(node, &lbl, &fields)) {
    snprintf(err, err_cap, "the source reader met an unexpected term");
    return false;
  }
  const GsltSexpr **ch = NULL;
  uint32_t nch = 0;
  if (!gslt_packet_fields(a, fields, &ch, &nch) || nch != 1) {
    snprintf(err, err_cap, "the source holds a number form the reader does not define");
    return false;
  }
  if (gslt_str_eq_cstr(lbl, "pl:number-decimal") ||
      gslt_str_eq_cstr(lbl, "pl:number-hex") ||
      gslt_str_eq_cstr(lbl, "pl:number-oct") ||
      gslt_str_eq_cstr(lbl, "pl:number-bin")) {
    uint32_t radix = gslt_str_eq_cstr(lbl, "pl:number-decimal") ? 10 :
                     (gslt_str_eq_cstr(lbl, "pl:number-hex") ? 16 :
                     (gslt_str_eq_cstr(lbl, "pl:number-oct") ? 8 : 2));
    GsltByteStr digits;
    if (!gslt_c0_pkt_text_of(a, ch[0], &digits) ||
        !c0_bigint_parse_radix(digits.bytes, digits.len, radix, out_val)) {
      snprintf(err, err_cap, "the source holds a number form the reader does not define");
      return false;
    }
    return true;
  }
  if (gslt_str_eq_cstr(lbl, "pl:number-char")) {
    GsltByteStr clbl;
    const GsltSexpr *cfields = NULL;
    if (!gslt_packet_is_node(ch[0], &clbl, &cfields)) {
      snprintf(err, err_cap, "the source reader met an unexpected term");
      return false;
    }
    if (gslt_str_eq_cstr(clbl, "pl:code-quote")) {
      c0_bigint_from_u64(out_val, 39);
      return true;
    }
    const GsltSexpr **cch = NULL;
    uint32_t ncch = 0;
    if (!gslt_packet_fields(a, cfields, &cch, &ncch) || ncch != 1) {
      snprintf(err, err_cap, "the source reader met an unexpected term");
      return false;
    }
    if (gslt_str_eq_cstr(clbl, "pl:code-escape")) {
      uint32_t cp = 0;
      if (!gslt_c0_pkt_read_escape(a, cch[0], &cp, err, err_cap)) return false;
      c0_bigint_from_u64(out_val, cp);
      return true;
    }
    if (gslt_str_eq_cstr(clbl, "pl:code-char")) {
      uint32_t cp = 0;
      if (!gslt_packet_scalar_cp(cch[0], &cp)) {
        snprintf(err, err_cap, "a character code escape names no Unicode scalar value");
        return false;
      }
      c0_bigint_from_u64(out_val, cp);
      return true;
    }
  }
  snprintf(err, err_cap, "the source holds a number form the reader does not define");
  return false;
}

static GsltPlTerm *gslt_c0_pkt_read_term(GsltArena *a, const GsltSexpr *node,
                                         char *err, size_t err_cap);

static inline bool gslt_c0_pkt_read_arguments(GsltArena *a, const GsltSexpr *node,
                                              GsltPlTerm ***out_args, uint32_t *out_nargs,
                                              char *err, size_t err_cap) {
  uint32_t cap = 8, count = 0;
  GsltPlTerm **arr = (GsltPlTerm **)gslt_arena_alloc(a, cap * sizeof(GsltPlTerm *));
  if (!arr) return false;
  const GsltSexpr *cur = node;
  while (true) {
    GsltByteStr lbl;
    const GsltSexpr *fields = NULL;
    if (!gslt_packet_is_node(cur, &lbl, &fields)) {
      snprintf(err, err_cap, "the source reader met an unexpected term");
      return false;
    }
    const GsltSexpr **ch = NULL;
    uint32_t nch = 0;
    if (!gslt_packet_fields(a, fields, &ch, &nch)) {
      snprintf(err, err_cap, "the source reader met an unexpected term");
      return false;
    }
    /* Filter non-layout children */
    const GsltSexpr *non_layout[8];
    uint32_t nnl = 0;
    for (uint32_t i = 0; i < nch; i++) {
      GsltByteStr clbl;
      if (gslt_packet_is_node(ch[i], &clbl, NULL) && gslt_c0_is_layout(clbl)) continue;
      if (nnl < 8) non_layout[nnl++] = ch[i];
    }
    if (gslt_str_eq_cstr(lbl, "pl:arguments-one") && nnl == 1) {
      GsltPlTerm *t = gslt_c0_pkt_read_term(a, non_layout[0], err, err_cap);
      if (!t) return false;
      if (count >= cap) {
        uint32_t ncap = cap * 2;
        GsltPlTerm **narr = (GsltPlTerm **)gslt_arena_alloc(a, ncap * sizeof(GsltPlTerm *));
        if (!narr) return false;
        memcpy(narr, arr, count * sizeof(GsltPlTerm *));
        arr = narr;
        cap = ncap;
      }
      arr[count++] = t;
      break;
    } else if (gslt_str_eq_cstr(lbl, "pl:arguments-more") && nnl == 2) {
      GsltPlTerm *t = gslt_c0_pkt_read_term(a, non_layout[0], err, err_cap);
      if (!t) return false;
      if (count >= cap) {
        uint32_t ncap = cap * 2;
        GsltPlTerm **narr = (GsltPlTerm **)gslt_arena_alloc(a, ncap * sizeof(GsltPlTerm *));
        if (!narr) return false;
        memcpy(narr, arr, count * sizeof(GsltPlTerm *));
        arr = narr;
        cap = ncap;
      }
      arr[count++] = t;
      cur = non_layout[1];
    } else {
      snprintf(err, err_cap, "the source reader met an unexpected term");
      return false;
    }
  }
  *out_args = arr;
  *out_nargs = count;
  return true;
}

static inline GsltPlTerm *gslt_c0_pkt_fold_list(GsltArena *a, GsltPlTerm **items,
                                                uint32_t nitems, GsltPlTerm *tail) {
  GsltPlTerm *cur = tail;
  GsltByteStr dot = gslt_str_from_cstr(a, ".");
  for (int i = (int)nitems - 1; i >= 0; i--) {
    GsltPlTerm *pair[2] = { items[i], cur };
    cur = gslt_pl_make_compound(a, dot, 2, pair);
  }
  return cur;
}

static GsltPlTerm *gslt_c0_pkt_read_term(GsltArena *a, const GsltSexpr *node,
                                         char *err, size_t err_cap) {
  GsltByteStr lbl;
  const GsltSexpr *fields = NULL;
  if (!gslt_packet_is_node(node, &lbl, &fields)) {
    snprintf(err, err_cap, "the source reader met an unexpected term");
    return NULL;
  }
  if (gslt_str_eq_cstr(lbl, "pl:list-empty")) {
    return gslt_pl_make_atom(a, gslt_str_from_cstr(a, "[]"));
  }
  const GsltSexpr **ch = NULL;
  uint32_t nch = 0;
  if (!gslt_packet_fields(a, fields, &ch, &nch)) {
    snprintf(err, err_cap, "the source reader met an unexpected term");
    return NULL;
  }
  const GsltSexpr *non_layout[16];
  uint32_t nnl = 0;
  for (uint32_t i = 0; i < nch; i++) {
    GsltByteStr clbl;
    if (gslt_packet_is_node(ch[i], &clbl, NULL) && gslt_c0_is_layout(clbl)) continue;
    if (nnl < 16) non_layout[nnl++] = ch[i];
  }
  if ((gslt_str_eq_cstr(lbl, "pl:parenthesized") ||
       (lbl.len >= 7 && memcmp(lbl.bytes, "pl:sub:", 7) == 0)) && nnl == 1) {
    return gslt_c0_pkt_read_term(a, non_layout[0], err, err_cap);
  }
  if (gslt_str_eq_cstr(lbl, "pl:curly") && nnl == 1) {
    GsltPlTerm *inner = gslt_c0_pkt_read_term(a, non_layout[0], err, err_cap);
    if (!inner) return NULL;
    return gslt_pl_make_compound(a, gslt_str_from_cstr(a, "{}"), 1, &inner);
  }
  if (gslt_str_eq_cstr(lbl, "pl:variable") && nnl == 1) {
    GsltByteStr vname;
    if (!gslt_c0_pkt_text_of(a, non_layout[0], &vname)) return NULL;
    return gslt_pl_make_var(a, vname);
  }
  if (gslt_str_eq_cstr(lbl, "pl:atom") && nnl == 1) {
    GsltByteStr aname;
    if (!gslt_c0_pkt_read_atom_node(a, non_layout[0], &aname, err, err_cap)) return NULL;
    return gslt_pl_make_atom(a, aname);
  }
  if (gslt_str_eq_cstr(lbl, "pl:double") && nnl == 1) {
    size_t cap = 64, len = 0;
    char *buf = (char *)gslt_arena_alloc(a, cap);
    if (!buf) return NULL;
    buf[0] = '\0';
    if (!gslt_c0_pkt_read_quoted_body(a, non_layout[0], &buf, &len, &cap, err, err_cap)) return NULL;
    GsltByteStr dstr = { buf, (uint32_t)len };
    return gslt_pl_make_atom(a, dstr);
  }
  if (gslt_str_eq_cstr(lbl, "pl:back") && nnl == 1) {
    size_t cap = 64, len = 0;
    char *buf = (char *)gslt_arena_alloc(a, cap);
    if (!buf) return NULL;
    buf[0] = '\0';
    if (!gslt_c0_pkt_read_quoted_body(a, non_layout[0], &buf, &len, &cap, err, err_cap)) return NULL;
    snprintf(err, err_cap, "the source holds a number form the reader does not define");
    return NULL;
  }
  if (gslt_str_eq_cstr(lbl, "pl:number") && nnl == 1) {
    C0BigInt ival;
    if (!gslt_c0_pkt_read_number_node(a, non_layout[0], &ival, err, err_cap)) return NULL;
    return gslt_pl_make_int(a, &ival);
  }
  if (gslt_str_eq_cstr(lbl, "pl:compound") && nnl == 2) {
    GsltByteStr fname;
    if (!gslt_c0_pkt_read_atom_node(a, non_layout[0], &fname, err, err_cap)) return NULL;
    GsltPlTerm **args = NULL;
    uint32_t nargs = 0;
    if (!gslt_c0_pkt_read_arguments(a, non_layout[1], &args, &nargs, err, err_cap)) return NULL;
    return gslt_pl_make_compound(a, fname, nargs, args);
  }
  if (gslt_str_eq_cstr(lbl, "pl:list") && nnl == 1) {
    GsltPlTerm **items = NULL;
    uint32_t nitems = 0;
    if (!gslt_c0_pkt_read_arguments(a, non_layout[0], &items, &nitems, err, err_cap)) return NULL;
    GsltPlTerm *empty = gslt_pl_make_atom(a, gslt_str_from_cstr(a, "[]"));
    return gslt_c0_pkt_fold_list(a, items, nitems, empty);
  }
  if (gslt_str_eq_cstr(lbl, "pl:list-tail") && nnl == 2) {
    GsltPlTerm **items = NULL;
    uint32_t nitems = 0;
    if (!gslt_c0_pkt_read_arguments(a, non_layout[0], &items, &nitems, err, err_cap)) return NULL;
    GsltPlTerm *tail = gslt_c0_pkt_read_term(a, non_layout[1], err, err_cap);
    if (!tail) return NULL;
    return gslt_c0_pkt_fold_list(a, items, nitems, tail);
  }
  if (lbl.len > 9 && memcmp(lbl.bytes, "pl:apply:", 9) == 0) {
    unsigned long op_idx = strtoul(lbl.bytes + 9, NULL, 10);
    if (op_idx >= GSLT_C0_NUM_OPERATORS) {
      snprintf(err, err_cap, "the source reader met an unexpected term");
      return NULL;
    }
    const GsltPrologOp *op = &GSLT_C0_OPERATORS[op_idx];
    if (op->spec == GSLT_OP_FX || op->spec == GSLT_OP_FY) {
      /* In reader.metta: raw fields of pl:apply:N are (operator, layout, operand) */
      if (nch != 3) {
        snprintf(err, err_cap, "the source reader met an unexpected term");
        return NULL;
      }
      GsltPlTerm *arg = gslt_c0_pkt_read_term(a, ch[2], err, err_cap);
      if (!arg) return NULL;
      if (strcmp(op->name, "-") == 0 && gslt_packet_node_label_eq(ch[1], "pl:layout-empty") &&
          arg->kind == GSLT_PL_INT) {
        C0BigInt neg = arg->ival;
        neg.sign = (int8_t)(-neg.sign);
        return gslt_pl_make_int(a, &neg);
      }
      return gslt_pl_make_compound(a, gslt_str_from_cstr(a, op->name), 1, &arg);
    } else if (op->spec == GSLT_OP_XF || op->spec == GSLT_OP_YF) {
      if (nnl != 2) {
        snprintf(err, err_cap, "the source reader met an unexpected term");
        return NULL;
      }
      GsltPlTerm *arg = gslt_c0_pkt_read_term(a, non_layout[0], err, err_cap);
      if (!arg) return NULL;
      return gslt_pl_make_compound(a, gslt_str_from_cstr(a, op->name), 1, &arg);
    } else {
      if (nnl != 3) {
        snprintf(err, err_cap, "the source reader met an unexpected term");
        return NULL;
      }
      GsltPlTerm *left = gslt_c0_pkt_read_term(a, non_layout[0], err, err_cap);
      if (!left) return NULL;
      GsltPlTerm *right = gslt_c0_pkt_read_term(a, non_layout[2], err, err_cap);
      if (!right) return NULL;
      GsltPlTerm *pair[2] = { left, right };
      return gslt_pl_make_compound(a, gslt_str_from_cstr(a, op->name), 2, pair);
    }
  }
  snprintf(err, err_cap, "the source reader met an unexpected term");
  return NULL;
}

static inline bool gslt_c0_packet_to_sentences(GsltArena *a, const GsltSexpr *result_pkt,
                                               GsltPlTerm ***out_sentences, uint32_t *out_count,
                                               char *err, size_t err_cap) {
  const GsltSexpr *tree = gslt_packet_unwrap_result(result_pkt);
  if (!tree) {
    /* Also allow passing the inner (node chr:program ...) directly */
    if (gslt_packet_node_label_eq(result_pkt, "chr:program")) {
      tree = result_pkt;
    } else {
      snprintf(err, err_cap, "expected an explicitly selected whole-input parser result");
      return false;
    }
  }
  GsltByteStr lbl;
  const GsltSexpr *fields = NULL;
  if (!gslt_packet_is_node(tree, &lbl, &fields) || !gslt_str_eq_cstr(lbl, "chr:program")) {
    snprintf(err, err_cap, "expected an explicitly selected whole-input parser result");
    return false;
  }
  const GsltSexpr **ch = NULL;
  uint32_t nch = 0;
  if (!gslt_packet_fields(a, fields, &ch, &nch) || nch != 1) {
    snprintf(err, err_cap, "expected an explicitly selected whole-input parser result");
    return false;
  }
  uint32_t cap = 16, count = 0;
  GsltPlTerm **sentences = (GsltPlTerm **)gslt_arena_alloc(a, cap * sizeof(GsltPlTerm *));
  if (!sentences) return false;
  const GsltSexpr *cur = ch[0];
  while (true) {
    GsltByteStr slbl;
    const GsltSexpr *sfields = NULL;
    if (!gslt_packet_is_node(cur, &slbl, &sfields)) {
      snprintf(err, err_cap, "the source reader met an unexpected term");
      return false;
    }
    if (gslt_str_eq_cstr(slbl, "chr:sentences-empty")) {
      break;
    }
    const GsltSexpr **sch = NULL;
    uint32_t nsch = 0;
    if (!gslt_str_eq_cstr(slbl, "chr:sentences-more") ||
        !gslt_packet_fields(a, sfields, &sch, &nsch) || nsch != 2) {
      snprintf(err, err_cap, "the source reader met an unexpected term");
      return false;
    }
    /* sch[0] is (node pl:sentence <fields>) */
    GsltByteStr plbl;
    const GsltSexpr *pfields = NULL;
    if (!gslt_packet_is_node(sch[0], &plbl, &pfields) || !gslt_str_eq_cstr(plbl, "pl:sentence")) {
      snprintf(err, err_cap, "the source reader met an unexpected term");
      return false;
    }
    const GsltSexpr **pch = NULL;
    uint32_t npch = 0;
    if (!gslt_packet_fields(a, pfields, &pch, &npch)) {
      snprintf(err, err_cap, "the source reader met an unexpected term");
      return false;
    }
    const GsltSexpr *term_node = NULL;
    for (uint32_t i = 0; i < npch; i++) {
      GsltByteStr clbl;
      if (gslt_packet_is_node(pch[i], &clbl, NULL) && gslt_c0_is_layout(clbl)) continue;
      term_node = pch[i];
      break;
    }
    if (!term_node) {
      snprintf(err, err_cap, "the source reader met an unexpected term");
      return false;
    }
    GsltPlTerm *sterm = gslt_c0_pkt_read_term(a, term_node, err, err_cap);
    if (!sterm) return false;
    if (count >= cap) {
      uint32_t ncap = cap * 2;
      GsltPlTerm **narr = (GsltPlTerm **)gslt_arena_alloc(a, ncap * sizeof(GsltPlTerm *));
      if (!narr) return false;
      memcpy(narr, sentences, count * sizeof(GsltPlTerm *));
      sentences = narr;
      cap = ncap;
    }
    sentences[count++] = sterm;
    cur = sch[1];
  }
  *out_sentences = sentences;
  *out_count = count;
  return true;
}

/* =========================================================================
 * 6. Direct Prolog/CHR Source Lexer & Precedence Parser -> GsltPlTerm
 * =========================================================================
 * Implements the exact lexical & operator rules of CHRPrologSyntax.lean:
 *   - % line comments and slash-star block comments (// is NEVER a comment!)
 *   - ASCII whitespace (32, 9, 10, 13, 11, 12); non-ASCII unquoted whitespace
 *     such as U+3000 is rejected.
 *   - Unquoted words, graphic words, variables, anonymous '_', single-quoted
 *     atoms, double-quoted atoms (as atoms in C0), and arbitrary-precision
 *     integers (decimal, 0x, 0o, 0b, 0'<char>).
 *   - Tracks preceding_layout per token so prefix '-' with empty layout before
 *     an integer literal folds to a negative integer literal, and functor '('
 *     with empty layout parses as compound term application.
 */
typedef enum {
  GSLT_PLTOK_EOF    = 0,
  GSLT_PLTOK_ATOM   = 1,
  GSLT_PLTOK_VAR    = 2,
  GSLT_PLTOK_INT    = 3,
  GSLT_PLTOK_LPAREN = 4,
  GSLT_PLTOK_RPAREN = 5,
  GSLT_PLTOK_LBRACK = 6,
  GSLT_PLTOK_RBRACK = 7,
  GSLT_PLTOK_LBRACE = 8,
  GSLT_PLTOK_RBRACE = 9,
  GSLT_PLTOK_COMMA  = 10,
  GSLT_PLTOK_BAR    = 11,
  GSLT_PLTOK_DOT    = 12
} GsltPlTokKind;

typedef struct {
  GsltPlTokKind kind;
  GsltByteStr   text;
  C0BigInt      ival;
  bool          had_layout_before;
  bool          quoted;
} GsltPlToken;

static inline bool gslt_pl_is_graphic(char c) {
  return c == '#' || c == '$' || c == '&' || c == '*' || c == '+' ||
         c == '-' || c == '.' || c == '/' || c == ':' || c == '<' ||
         c == '=' || c == '>' || c == '?' || c == '@' || c == '\\' ||
         c == '^' || c == '~';
}

static inline bool gslt_pl_is_space(char c) {
  return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\v' || c == '\f';
}

static inline bool gslt_pl_parse_escape_seq(const char *src, size_t len, size_t *pos,
                                            uint32_t *out_cp, bool *out_ignored_newline,
                                            char *err, size_t err_cap) {
  *out_ignored_newline = false;
  if (*pos >= len) {
    snprintf(err, err_cap, "unterminated escape sequence in Prolog/CHR source");
    return false;
  }
  char c = src[(*pos)++];
  if (c == '\n') {
    *out_ignored_newline = true;
    return true;
  }
  if (c == '\r') {
    if (*pos < len && src[*pos] == '\n') (*pos)++;
    *out_ignored_newline = true;
    return true;
  }
  switch (c) {
    case 'a': *out_cp = 7; return true;
    case 'b': *out_cp = 8; return true;
    case 't': *out_cp = 9; return true;
    case 'n': *out_cp = 10; return true;
    case 'v': *out_cp = 11; return true;
    case 'f': *out_cp = 12; return true;
    case 'r': *out_cp = 13; return true;
    case 'e': *out_cp = 27; return true;
    case 's': *out_cp = 32; return true;
    case 'd': *out_cp = 127; return true;
    case '\\': *out_cp = '\\'; return true;
    case '\'': *out_cp = '\''; return true;
    case '"': *out_cp = '"'; return true;
    case '`': *out_cp = '`'; return true;
    case 'x': {
      size_t start = *pos;
      while (*pos < len && isxdigit((unsigned char)src[*pos])) (*pos)++;
      size_t dlen = *pos - start;
      if (dlen == 0) {
        snprintf(err, err_cap, "the source holds an escape the reader does not define");
        return false;
      }
      if (*pos < len && src[*pos] == '\\') (*pos)++;
      C0BigInt val;
      uint64_t uval = 0;
      if (!c0_bigint_parse_radix(src + start, dlen, 16, &val) ||
          !c0_bigint_to_u64(&val, &uval) || !gslt_unicode_is_scalar(uval)) {
        snprintf(err, err_cap, "a character code escape names no Unicode scalar value");
        return false;
      }
      *out_cp = (uint32_t)uval;
      return true;
    }
    case 'u':
    case 'U': {
      size_t need = (c == 'u') ? 4 : 8;
      if (*pos + need > len) {
        snprintf(err, err_cap, "the source holds an escape the reader does not define");
        return false;
      }
      for (size_t i = 0; i < need; i++) {
        if (!isxdigit((unsigned char)src[*pos + i])) {
          snprintf(err, err_cap, "the source holds an escape the reader does not define");
          return false;
        }
      }
      C0BigInt val;
      uint64_t uval = 0;
      if (!c0_bigint_parse_radix(src + *pos, need, 16, &val) ||
          !c0_bigint_to_u64(&val, &uval) || !gslt_unicode_is_scalar(uval)) {
        snprintf(err, err_cap, "a character code escape names no Unicode scalar value");
        return false;
      }
      *pos += need;
      *out_cp = (uint32_t)uval;
      return true;
    }
    default:
      if (c >= '0' && c <= '7') {
        size_t start = *pos - 1;
        while (*pos < len && src[*pos] >= '0' && src[*pos] <= '7') (*pos)++;
        size_t dlen = *pos - start;
        if (*pos < len && src[*pos] == '\\') (*pos)++;
        C0BigInt val;
        uint64_t uval = 0;
        if (!c0_bigint_parse_radix(src + start, dlen, 8, &val) ||
            !c0_bigint_to_u64(&val, &uval) || !gslt_unicode_is_scalar(uval)) {
          snprintf(err, err_cap, "a character code escape names no Unicode scalar value");
          return false;
        }
        *out_cp = (uint32_t)uval;
        return true;
      }
      snprintf(err, err_cap, "the source holds an escape the reader does not define");
      return false;
  }
}

static inline bool gslt_pl_tokenize(GsltArena *a, const char *src, size_t len,
                                    GsltPlToken **out_toks, uint32_t *out_ntoks,
                                    char *err, size_t err_cap) {
  uint32_t cap = 64, count = 0;
  GsltPlToken *toks = (GsltPlToken *)gslt_arena_alloc(a, cap * sizeof(GsltPlToken));
  if (!toks) return false;
  size_t pos = 0;
  while (pos < len) {
    bool had_layout = false;
    while (pos < len) {
      if (gslt_pl_is_space(src[pos])) {
        had_layout = true;
        pos++;
      } else if (src[pos] == '%') {
        had_layout = true;
        pos++;
        while (pos < len && src[pos] != '\n') {
          uint32_t cp = 0;
          size_t adv = gslt_utf8_decode(src + pos, len - pos, &cp);
          if (adv == 0 || cp == 0) {
            snprintf(err, err_cap, "invalid character in Prolog line comment");
            return false;
          }
          pos += adv;
        }
        if (pos < len && src[pos] == '\n') pos++;
      } else if (pos + 1 < len && src[pos] == '/' && src[pos + 1] == '*') {
        had_layout = true;
        pos += 2;
        bool closed = false;
        while (pos + 1 < len) {
          if (src[pos] == '*' && src[pos + 1] == '/') {
            pos += 2;
            closed = true;
            break;
          }
          uint32_t cp = 0;
          size_t adv = gslt_utf8_decode(src + pos, len - pos, &cp);
          if (adv == 0 || cp == 0) {
            snprintf(err, err_cap, "invalid character in Prolog block comment");
            return false;
          }
          pos += adv;
        }
        if (!closed) {
          snprintf(err, err_cap, "unterminated /* ... */ comment in Prolog/CHR source");
          return false;
        }
      } else {
        break;
      }
    }
    if (pos >= len) break;

    if (count >= cap) {
      uint32_t ncap = cap * 2;
      GsltPlToken *ntoks = (GsltPlToken *)gslt_arena_alloc(a, ncap * sizeof(GsltPlToken));
      if (!ntoks) return false;
      memcpy(ntoks, toks, count * sizeof(GsltPlToken));
      toks = ntoks;
      cap = ncap;
    }

    char c = src[pos];
    /* Single-character punctuation */
    if (c == '(' || c == ')' || c == '[' || c == ']' || c == '{' || c == '}' || c == ',') {
      GsltPlToken *tk = &toks[count++];
      memset(tk, 0, sizeof(*tk));
      tk->had_layout_before = had_layout;
      tk->text = gslt_str_intern(a, &src[pos], 1);
      switch (c) {
        case '(': tk->kind = GSLT_PLTOK_LPAREN; break;
        case ')': tk->kind = GSLT_PLTOK_RPAREN; break;
        case '[': tk->kind = GSLT_PLTOK_LBRACK; break;
        case ']': tk->kind = GSLT_PLTOK_RBRACK; break;
        case '{': tk->kind = GSLT_PLTOK_LBRACE; break;
        case '}': tk->kind = GSLT_PLTOK_RBRACE; break;
        case ',': tk->kind = GSLT_PLTOK_COMMA; break;
      }
      pos++;
      continue;
    }
    if (c == '|') {
      GsltPlToken *tk = &toks[count++];
      memset(tk, 0, sizeof(*tk));
      tk->had_layout_before = had_layout;
      tk->kind = GSLT_PLTOK_BAR;
      tk->text = gslt_str_from_cstr(a, "|");
      pos++;
      continue;
    }
    if (c == '!' || c == ';') {
      GsltPlToken *tk = &toks[count++];
      memset(tk, 0, sizeof(*tk));
      tk->had_layout_before = had_layout;
      tk->kind = GSLT_PLTOK_ATOM;
      tk->text = gslt_str_intern(a, &src[pos], 1);
      pos++;
      continue;
    }
    /* Quoted atom ('...' or "...") or back-quoted (`...`) */
    if (c == '\'' || c == '"' || c == '`') {
      char quote = c;
      pos++;
      size_t bcap = 64, blen = 0;
      char *buf = (char *)gslt_arena_alloc(a, bcap);
      if (!buf) return false;
      buf[0] = '\0';
      bool closed = false;
      while (pos < len) {
        if (src[pos] == quote) {
          if (pos + 1 < len && src[pos + 1] == quote) {
            /* Doubled quote */
            if (blen + 2 >= bcap) {
              size_t ncap = bcap * 2;
              char *nbuf = (char *)gslt_arena_alloc(a, ncap);
              if (!nbuf) return false;
              memcpy(nbuf, buf, blen);
              buf = nbuf;
              bcap = ncap;
            }
            buf[blen++] = quote;
            buf[blen] = '\0';
            pos += 2;
            continue;
          }
          pos++;
          closed = true;
          break;
        }
        if (src[pos] == '\\') {
          pos++;
          uint32_t cp = 0;
          bool ign = false;
          if (!gslt_pl_parse_escape_seq(src, len, &pos, &cp, &ign, err, err_cap)) return false;
          if (ign) continue;
          char u[4];
          size_t ulen = gslt_utf8_encode(cp, u);
          if (blen + ulen + 1 >= bcap) {
            size_t ncap = bcap * 2;
            char *nbuf = (char *)gslt_arena_alloc(a, ncap);
            if (!nbuf) return false;
            memcpy(nbuf, buf, blen);
            buf = nbuf;
            bcap = ncap;
          }
          memcpy(buf + blen, u, ulen);
          blen += ulen;
          buf[blen] = '\0';
          continue;
        }
        if (src[pos] == '\n' || src[pos] == '\r') {
          snprintf(err, err_cap, "unescaped newline inside quoted literal");
          return false;
        }
        uint32_t cp = 0;
        size_t adv = gslt_utf8_decode(src + pos, len - pos, &cp);
        if (adv == 0 || cp == 0) {
          snprintf(err, err_cap, "invalid UTF-8 scalar in quoted literal");
          return false;
        }
        if (blen + adv + 1 >= bcap) {
          size_t ncap = bcap * 2;
          char *nbuf = (char *)gslt_arena_alloc(a, ncap);
          if (!nbuf) return false;
          memcpy(nbuf, buf, blen);
          buf = nbuf;
          bcap = ncap;
        }
        memcpy(buf + blen, src + pos, adv);
        blen += adv;
        buf[blen] = '\0';
        pos += adv;
      }
      if (!closed) {
        snprintf(err, err_cap, "unterminated quoted literal in Prolog/CHR source");
        return false;
      }
      if (quote == '`') {
        snprintf(err, err_cap, "the source holds a number form the reader does not define");
        return false;
      }
      GsltPlToken *tk = &toks[count++];
      memset(tk, 0, sizeof(*tk));
      tk->had_layout_before = had_layout;
      tk->kind = GSLT_PLTOK_ATOM;
      tk->quoted = true;
      tk->text.bytes = buf;
      tk->text.len = (uint32_t)blen;
      continue;
    }
    /* Numbers: 0'char, 0x..., 0o..., 0b..., or decimal digits */
    if (c >= '0' && c <= '9') {
      GsltPlToken *tk = &toks[count++];
      memset(tk, 0, sizeof(*tk));
      tk->had_layout_before = had_layout;
      tk->kind = GSLT_PLTOK_INT;
      if (c == '0' && pos + 1 < len && src[pos + 1] == '\'') {
        pos += 2;
        if (pos >= len) {
          snprintf(err, err_cap, "incomplete 0' character code literal");
          return false;
        }
        uint32_t cp = 0;
        if (src[pos] == '\'') {
          if (pos + 1 < len && src[pos + 1] == '\'') {
            cp = '\'';
            pos += 2;
          } else {
            snprintf(err, err_cap, "invalid single quote in 0' character code literal");
            return false;
          }
        } else if (src[pos] == '\\') {
          pos++;
          bool ign = false;
          if (!gslt_pl_parse_escape_seq(src, len, &pos, &cp, &ign, err, err_cap) || ign) {
            snprintf(err, err_cap, "a character code escape names no Unicode scalar value");
            return false;
          }
        } else {
          size_t adv = gslt_utf8_decode(src + pos, len - pos, &cp);
          if (adv == 0 || cp < 32) {
            snprintf(err, err_cap, "invalid scalar in 0' character code literal");
            return false;
          }
          pos += adv;
        }
        c0_bigint_from_u64(&tk->ival, cp);
        continue;
      }
      if (c == '0' && pos + 2 <= len &&
          (src[pos + 1] == 'x' || src[pos + 1] == 'X' ||
           src[pos + 1] == 'o' || src[pos + 1] == 'O' ||
           src[pos + 1] == 'b' || src[pos + 1] == 'B')) {
        char mode = (char)tolower((unsigned char)src[pos + 1]);
        uint32_t radix = (mode == 'x') ? 16 : ((mode == 'o') ? 8 : 2);
        pos += 2;
        size_t start = pos;
        while (pos < len) {
          char d = src[pos];
          bool ok = (radix == 16) ? isxdigit((unsigned char)d) :
                    ((radix == 8) ? (d >= '0' && d <= '7') : (d == '0' || d == '1'));
          if (!ok) break;
          pos++;
        }
        if (pos == start || !c0_bigint_parse_radix(src + start, pos - start, radix, &tk->ival)) {
          snprintf(err, err_cap, "invalid radix integer literal");
          return false;
        }
        continue;
      }
      size_t start = pos;
      while (pos < len && src[pos] >= '0' && src[pos] <= '9') pos++;
      /* Reject floats or radix notation N'xxx in C0 (UnknownNumber) */
      if (pos + 1 < len && src[pos] == '.' && src[pos + 1] >= '0' && src[pos + 1] <= '9') {
        snprintf(err, err_cap, "the source holds a number form the reader does not define");
        return false;
      }
      if (pos < len && src[pos] == '\'') {
        snprintf(err, err_cap, "the source holds a number form the reader does not define");
        return false;
      }
      /* Reject immediate identifier tail attached to digits (e.g. 12abc) */
      if (pos < len && (isalpha((unsigned char)src[pos]) || src[pos] == '_')) {
        snprintf(err, err_cap, "invalid token after numeric literal");
        return false;
      }
      if (!c0_bigint_parse_dec(src + start, pos - start, &tk->ival)) {
        snprintf(err, err_cap, "numeric literal exceeds maximum supported precision");
        return false;
      }
      tk->text = gslt_str_intern(a, src + start, pos - start);
      continue;
    }
    /* Unquoted atom word: [a-z][a-zA-Z0-9_]* */
    if (c >= 'a' && c <= 'z') {
      size_t start = pos++;
      while (pos < len && (isalnum((unsigned char)src[pos]) || src[pos] == '_')) pos++;
      /* Check if followed immediately by non-ASCII byte (like 'café' or U+3000) */
      if (pos < len && (unsigned char)src[pos] >= 0x80u) {
        snprintf(err, err_cap, "unquoted Prolog identifiers must be ASCII");
        return false;
      }
      GsltPlToken *tk = &toks[count++];
      memset(tk, 0, sizeof(*tk));
      tk->had_layout_before = had_layout;
      tk->kind = GSLT_PLTOK_ATOM;
      tk->text = gslt_str_intern(a, src + start, pos - start);
      continue;
    }
    /* Variable: [A-Z_][a-zA-Z0-9_]* */
    if ((c >= 'A' && c <= 'Z') || c == '_') {
      size_t start = pos++;
      while (pos < len && (isalnum((unsigned char)src[pos]) || src[pos] == '_')) pos++;
      if (pos < len && (unsigned char)src[pos] >= 0x80u) {
        snprintf(err, err_cap, "unquoted Prolog variable names must be ASCII");
        return false;
      }
      GsltPlToken *tk = &toks[count++];
      memset(tk, 0, sizeof(*tk));
      tk->had_layout_before = had_layout;
      tk->kind = GSLT_PLTOK_VAR;
      tk->text = gslt_str_intern(a, src + start, pos - start);
      continue;
    }
    /* Graphic token: maximal sequence of graphic characters (#$&*+-./:<=>?@\^~) */
    if (gslt_pl_is_graphic(c)) {
      size_t start = pos;
      while (pos < len && gslt_pl_is_graphic(src[pos])) {
        /* Note: don't swallow slash-star start of block comment into a graphic token */
        if (pos > start && pos + 1 < len && src[pos] == '/' && src[pos + 1] == '*') break;
        pos++;
      }
      size_t glen = pos - start;
      GsltPlToken *tk = &toks[count++];
      memset(tk, 0, sizeof(*tk));
      tk->had_layout_before = had_layout;
      tk->text = gslt_str_intern(a, src + start, glen);
      /* Sentence period: a single '.' followed by EOF, whitespace, or comment */
      if (glen == 1 && src[start] == '.') {
        bool at_end = (pos >= len) || gslt_pl_is_space(src[pos]) || src[pos] == '%' ||
                      (pos + 1 < len && src[pos] == '/' && src[pos + 1] == '*');
        tk->kind = at_end ? GSLT_PLTOK_DOT : GSLT_PLTOK_ATOM;
      } else {
        tk->kind = GSLT_PLTOK_ATOM;
      }
      continue;
    }
    snprintf(err, err_cap, "unexpected character 0x%02x in Prolog/CHR source", (unsigned char)c);
    return false;
  }
  if (count >= cap) {
    GsltPlToken *ntoks = (GsltPlToken *)gslt_arena_alloc(a, (cap + 1) * sizeof(GsltPlToken));
    if (!ntoks) return false;
    memcpy(ntoks, toks, count * sizeof(GsltPlToken));
    toks = ntoks;
  }
  memset(&toks[count], 0, sizeof(GsltPlToken));
  toks[count].kind = GSLT_PLTOK_EOF;
  *out_toks = toks;
  *out_ntoks = count;
  return true;
}

/* Operator lookup helpers */
static inline const GsltPrologOp *gslt_c0_find_prefix_op(GsltByteStr name) {
  for (int i = 0; i < GSLT_C0_NUM_OPERATORS; i++) {
    if ((GSLT_C0_OPERATORS[i].spec == GSLT_OP_FX || GSLT_C0_OPERATORS[i].spec == GSLT_OP_FY) &&
        gslt_str_eq_cstr(name, GSLT_C0_OPERATORS[i].name)) {
      return &GSLT_C0_OPERATORS[i];
    }
  }
  return NULL;
}

static inline const GsltPrologOp *gslt_c0_find_infix_op(GsltByteStr name, uint16_t max_prio) {
  const GsltPrologOp *best = NULL;
  for (int i = 0; i < GSLT_C0_NUM_OPERATORS; i++) {
    GsltOpSpec sp = GSLT_C0_OPERATORS[i].spec;
    if ((sp == GSLT_OP_XFX || sp == GSLT_OP_XFY || sp == GSLT_OP_YFX) &&
        GSLT_C0_OPERATORS[i].priority <= max_prio &&
        gslt_str_eq_cstr(name, GSLT_C0_OPERATORS[i].name)) {
      /* Prefer the operator matching max_prio range (e.g. ==> at 1180 in CHR) */
      if (!best || GSLT_C0_OPERATORS[i].priority < best->priority) {
        best = &GSLT_C0_OPERATORS[i];
      }
    }
  }
  return best;
}

typedef struct {
  GsltArena         *arena;
  const GsltPlToken *toks;
  uint32_t           ntoks;
  uint32_t           pos;
  char               err[256];
} GsltPlParser;

static GsltPlTerm *gslt_pl_parse_expr(GsltPlParser *p, uint16_t max_prio);

static GsltPlTerm *gslt_pl_parse_arg_list(GsltPlParser *p, GsltPlTerm ***out_args, uint32_t *out_nargs) {
  uint32_t cap = 8, count = 0;
  GsltPlTerm **args = (GsltPlTerm **)gslt_arena_alloc(p->arena, cap * sizeof(GsltPlTerm *));
  if (!args) return NULL;
  while (true) {
    GsltPlTerm *arg = gslt_pl_parse_expr(p, 999);
    if (!arg) return NULL;
    if (count >= cap) {
      uint32_t ncap = cap * 2;
      GsltPlTerm **nargs = (GsltPlTerm **)gslt_arena_alloc(p->arena, ncap * sizeof(GsltPlTerm *));
      if (!nargs) return NULL;
      memcpy(nargs, args, count * sizeof(GsltPlTerm *));
      args = nargs;
      cap = ncap;
    }
    args[count++] = arg;
    if (p->toks[p->pos].kind == GSLT_PLTOK_COMMA) {
      p->pos++;
    } else {
      break;
    }
  }
  *out_args = args;
  *out_nargs = count;
  return args[0];
}

static GsltPlTerm *gslt_pl_parse_prefix_or_atom(GsltPlParser *p, uint16_t max_prio) {
  const GsltPlToken *tk = &p->toks[p->pos];
  if (tk->kind == GSLT_PLTOK_EOF) {
    snprintf(p->err, sizeof(p->err), "unexpected end of input in Prolog/CHR term");
    return NULL;
  }
  if (tk->kind == GSLT_PLTOK_VAR) {
    p->pos++;
    return gslt_pl_make_var(p->arena, tk->text);
  }
  if (tk->kind == GSLT_PLTOK_INT) {
    p->pos++;
    return gslt_pl_make_int(p->arena, &tk->ival);
  }
  if (tk->kind == GSLT_PLTOK_LPAREN) {
    p->pos++;
    GsltPlTerm *inner = gslt_pl_parse_expr(p, 1200);
    if (!inner) return NULL;
    if (p->toks[p->pos].kind != GSLT_PLTOK_RPAREN) {
      snprintf(p->err, sizeof(p->err), "expected ')' after parenthesized Prolog term");
      return NULL;
    }
    p->pos++;
    return inner;
  }
  if (tk->kind == GSLT_PLTOK_LBRACE) {
    p->pos++;
    if (p->toks[p->pos].kind == GSLT_PLTOK_RBRACE) {
      p->pos++;
      return gslt_pl_make_atom(p->arena, gslt_str_from_cstr(p->arena, "{}"));
    }
    GsltPlTerm *inner = gslt_pl_parse_expr(p, 1200);
    if (!inner) return NULL;
    if (p->toks[p->pos].kind != GSLT_PLTOK_RBRACE) {
      snprintf(p->err, sizeof(p->err), "expected '}' after curly Prolog term");
      return NULL;
    }
    p->pos++;
    return gslt_pl_make_compound(p->arena, gslt_str_from_cstr(p->arena, "{}"), 1, &inner);
  }
  if (tk->kind == GSLT_PLTOK_LBRACK) {
    p->pos++;
    if (p->toks[p->pos].kind == GSLT_PLTOK_RBRACK) {
      p->pos++;
      return gslt_pl_make_atom(p->arena, gslt_str_from_cstr(p->arena, "[]"));
    }
    GsltPlTerm **items = NULL;
    uint32_t nitems = 0;
    if (!gslt_pl_parse_arg_list(p, &items, &nitems)) return NULL;
    GsltPlTerm *tail = NULL;
    if (p->toks[p->pos].kind == GSLT_PLTOK_BAR) {
      p->pos++;
      tail = gslt_pl_parse_expr(p, 999);
      if (!tail) return NULL;
    } else {
      tail = gslt_pl_make_atom(p->arena, gslt_str_from_cstr(p->arena, "[]"));
    }
    if (p->toks[p->pos].kind != GSLT_PLTOK_RBRACK) {
      snprintf(p->err, sizeof(p->err), "expected ']' at end of Prolog list");
      return NULL;
    }
    p->pos++;
    return gslt_c0_pkt_fold_list(p->arena, items, nitems, tail);
  }
  if (tk->kind == GSLT_PLTOK_ATOM) {
    GsltByteStr name = tk->text;
    p->pos++;
    /* Compound application f(a1, ..., an): only when '(' immediately follows with no layout! */
    if (p->toks[p->pos].kind == GSLT_PLTOK_LPAREN && !p->toks[p->pos].had_layout_before) {
      p->pos++;
      if (p->toks[p->pos].kind == GSLT_PLTOK_RPAREN) {
        snprintf(p->err, sizeof(p->err), "empty argument list f() is not valid ISO Prolog");
        return NULL;
      }
      GsltPlTerm **args = NULL;
      uint32_t nargs = 0;
      if (!gslt_pl_parse_arg_list(p, &args, &nargs)) return NULL;
      if (p->toks[p->pos].kind != GSLT_PLTOK_RPAREN) {
        snprintf(p->err, sizeof(p->err), "expected ')' after compound arguments");
        return NULL;
      }
      p->pos++;
      return gslt_pl_make_compound(p->arena, name, nargs, args);
    }
    /* Check if this atom is a prefix operator AND not followed by an infix/terminator token */
    const GsltPrologOp *pop = gslt_c0_find_prefix_op(name);
    const GsltPlToken *next_tk = &p->toks[p->pos];
    bool next_can_start_expr =
        next_tk->kind == GSLT_PLTOK_ATOM ||
        next_tk->kind == GSLT_PLTOK_VAR ||
        next_tk->kind == GSLT_PLTOK_INT ||
        next_tk->kind == GSLT_PLTOK_LPAREN ||
        next_tk->kind == GSLT_PLTOK_LBRACK ||
        next_tk->kind == GSLT_PLTOK_LBRACE;
    if (pop && pop->priority <= max_prio && next_can_start_expr) {
      /* Prefix '-' immediately adjacent to an integer literal folds to negative int! */
      if (gslt_str_eq_cstr(name, "-") && next_tk->kind == GSLT_PLTOK_INT && !next_tk->had_layout_before) {
        p->pos++;
        C0BigInt neg = next_tk->ival;
        neg.sign = (int8_t)(-neg.sign);
        return gslt_pl_make_int(p->arena, &neg);
      }
      uint16_t rhs_max = (pop->spec == GSLT_OP_FX) ? (uint16_t)(pop->priority - 1) : pop->priority;
      GsltPlTerm *rhs = gslt_pl_parse_expr(p, rhs_max);
      if (!rhs) return NULL;
      return gslt_pl_make_compound(p->arena, name, 1, &rhs);
    }
    return gslt_pl_make_atom(p->arena, name);
  }
  snprintf(p->err, sizeof(p->err), "unexpected token '%.*s' in Prolog/CHR expression",
           (int)tk->text.len, tk->text.bytes);
  return NULL;
}

static GsltPlTerm *gslt_pl_parse_expr(GsltPlParser *p, uint16_t max_prio) {
  uint16_t lhs_prio = max_prio;
  GsltPlTerm *lhs = gslt_pl_parse_prefix_or_atom(p, max_prio);
  if (!lhs) return NULL;
  /* Determine effective priority of lhs to enforce xfx / yfx left-operand priority */
  uint16_t cur_lhs_prio = 0;
  (void)lhs_prio;
  while (true) {
    const GsltPlToken *tk = &p->toks[p->pos];
    GsltByteStr op_name = { "", 0 };
    if (tk->kind == GSLT_PLTOK_COMMA) {
      op_name = gslt_str_from_cstr(p->arena, ",");
    } else if (tk->kind == GSLT_PLTOK_BAR) {
      op_name = gslt_str_from_cstr(p->arena, "|");
    } else if (tk->kind == GSLT_PLTOK_ATOM && !tk->quoted) {
      op_name = tk->text;
    } else if (tk->kind == GSLT_PLTOK_ATOM && tk->quoted) {
      /* Wait: in CHRPrologSyntax.lean, pl:operator:N matches literal operator tokens,
       * while quoted atoms like 'is' are PlAtom, NOT operators! */
      break;
    } else {
      break;
    }
    const GsltPrologOp *iop = gslt_c0_find_infix_op(op_name, max_prio);
    if (!iop) break;
    /* Check left-associativity constraint: for XFX and XFY, cur_lhs_prio must be < iop->priority;
     * for YFX, cur_lhs_prio must be <= iop->priority. */
    if ((iop->spec == GSLT_OP_XFX || iop->spec == GSLT_OP_XFY) && cur_lhs_prio >= iop->priority) {
      break;
    }
    if (iop->spec == GSLT_OP_YFX && cur_lhs_prio > iop->priority) {
      break;
    }
    p->pos++;
    uint16_t rhs_max = (iop->spec == GSLT_OP_XFY) ? iop->priority : (uint16_t)(iop->priority - 1);
    GsltPlTerm *rhs = gslt_pl_parse_expr(p, rhs_max);
    if (!rhs) return NULL;
    GsltPlTerm *pair[2] = { lhs, rhs };
    lhs = gslt_pl_make_compound(p->arena, gslt_str_from_cstr(p->arena, iop->name), 2, pair);
    cur_lhs_prio = iop->priority;
  }
  return lhs;
}

static inline bool gslt_c0_source_to_sentences(GsltArena *a, const char *src, size_t len,
                                               GsltPlTerm ***out_sentences, uint32_t *out_count,
                                               char *err, size_t err_cap) {
  GsltPlToken *toks = NULL;
  uint32_t ntoks = 0;
  if (!gslt_pl_tokenize(a, src, len, &toks, &ntoks, err, err_cap)) {
    return false;
  }
  GsltPlParser p;
  p.arena = a;
  p.toks = toks;
  p.ntoks = ntoks;
  p.pos = 0;
  p.err[0] = '\0';

  uint32_t cap = 16, count = 0;
  GsltPlTerm **sentences = (GsltPlTerm **)gslt_arena_alloc(a, cap * sizeof(GsltPlTerm *));
  if (!sentences) return false;

  while (p.toks[p.pos].kind != GSLT_PLTOK_EOF) {
    GsltPlTerm *sent = gslt_pl_parse_expr(&p, 1200);
    if (!sent) {
      snprintf(err, err_cap, "%s", p.err[0] ? p.err : "failed to parse Prolog/CHR sentence");
      return false;
    }
    if (p.toks[p.pos].kind != GSLT_PLTOK_DOT) {
      snprintf(err, err_cap, "expected '.' at end of Prolog/CHR sentence");
      return false;
    }
    p.pos++;
    if (count >= cap) {
      uint32_t ncap = cap * 2;
      GsltPlTerm **narr = (GsltPlTerm **)gslt_arena_alloc(a, ncap * sizeof(GsltPlTerm *));
      if (!narr) return false;
      memcpy(narr, sentences, count * sizeof(GsltPlTerm *));
      sentences = narr;
      cap = ncap;
    }
    sentences[count++] = sent;
  }
  *out_sentences = sentences;
  *out_count = count;
  return true;
}

/* =========================================================================
 * 7. C0 Independent IR, Lowering, Static Admission, Codecs & Printer
 * ========================================================================= */
typedef enum {
  GSLT_C0_VAL_INT      = 1,
  GSLT_C0_VAL_ATOM     = 2,
  GSLT_C0_VAL_TUPLE    = 3,
  GSLT_C0_VAL_VAR      = 4, /* C1 runtime logical variable */
  GSLT_C0_VAL_COMPOUND = 5  /* C1 general compound term f(a1, ..., ak) */
} GsltC0ValKind;

typedef struct GsltC0Value {
  GsltC0ValKind       kind;
  C0BigInt            ival;
  GsltByteStr         atom;
  uint32_t            var_id;
  uint32_t            nfields;
  struct GsltC0Value **fields;
} GsltC0Value;

typedef enum {
  GSLT_C0_TERM_VAL      = 1,
  GSLT_C0_TERM_VAR      = 2,
  GSLT_C0_TERM_TUPLE    = 3,
  GSLT_C0_TERM_COMPOUND = 4 /* C1 general compound term pattern/constructor */
} GsltC0TermKind;

typedef struct GsltC0Term {
  GsltC0TermKind      kind;
  GsltC0Value        *val;
  uint32_t            var_idx;
  GsltByteStr         functor;
  uint32_t            nfields;
  struct GsltC0Term **fields;
} GsltC0Term;

typedef struct {
  GsltByteStr  name;
  uint32_t     arity;
  GsltC0Term **args;
} GsltC0Head;

typedef enum {
  GSLT_C0_IOP_ADD  = 1,
  GSLT_C0_IOP_SUB  = 2,
  GSLT_C0_IOP_MUL  = 3,
  GSLT_C0_IOP_QUOT = 4, /* // */
  GSLT_C0_IOP_REM  = 5, /* rem */
  GSLT_C0_IOP_MOD  = 6  /* mod */
} GsltC0IntOp;

typedef enum {
  GSLT_C0_IEXPR_LIT = 1,
  GSLT_C0_IEXPR_VAR = 2,
  GSLT_C0_IEXPR_OP  = 3
} GsltC0IntExprKind;

typedef struct GsltC0IntExpr {
  GsltC0IntExprKind     kind;
  C0BigInt              lit;
  uint32_t              var_idx;
  GsltC0IntOp           op;
  struct GsltC0IntExpr *left;
  struct GsltC0IntExpr *right;
} GsltC0IntExpr;

typedef enum {
  GSLT_C0_CMP_EQ = 1, /* =:= */
  GSLT_C0_CMP_NE = 2, /* =\= */
  GSLT_C0_CMP_LT = 3, /* <   */
  GSLT_C0_CMP_LE = 4, /* =<  */
  GSLT_C0_CMP_GT = 5, /* >   */
  GSLT_C0_CMP_GE = 6  /* >=  */
} GsltC0CmpOp;

typedef enum {
  GSLT_C0_GUARD_IDENTICAL = 1, /* ==  */
  GSLT_C0_GUARD_DISTINCT  = 2, /* \== */
  GSLT_C0_GUARD_COMPARE   = 3  /* arithmetic comparison */
} GsltC0GuardKind;

typedef struct {
  GsltC0GuardKind kind;
  GsltC0Term     *t_left;
  GsltC0Term     *t_right;
  GsltC0CmpOp     cmp;
  GsltC0IntExpr  *e_left;
  GsltC0IntExpr  *e_right;
} GsltC0Guard;

typedef enum {
  GSLT_C0_GOAL_TELL     = 1,
  GSLT_C0_GOAL_ASSIGN   = 2,
  GSLT_C0_GOAL_FAIL     = 3,
  GSLT_C0_GOAL_UNIFY    = 4, /* C1 L = R */
  GSLT_C0_GOAL_UNIFY_OC = 5, /* C1 unify_with_occurs_check(L, R) */
  GSLT_C0_GOAL_GUARD    = 6  /* C1 guard test goal (e.g. X == x in query/body) */
} GsltC0GoalKind;

typedef struct {
  GsltC0GoalKind kind;
  GsltC0Head     tell_head;
  uint32_t       assign_var;
  GsltC0IntExpr *assign_expr;
  GsltC0Term    *unify_left;
  GsltC0Term    *unify_right;
  GsltC0Guard    guard_test;
} GsltC0Goal;

typedef struct {
  GsltByteStr  name;
  uint32_t     nkept;
  GsltC0Head  *kept;
  uint32_t     nremoved;
  GsltC0Head  *removed;
  uint32_t     nguards;
  GsltC0Guard *guards;
  uint32_t     nbody;
  GsltC0Goal  *body;
} GsltC0Rule;

typedef struct {
  GsltByteStr name;
  uint32_t    arity;
} GsltC0Declaration;

typedef enum {
  GSLT_C0_DIAG_NONE                  = 0,
  GSLT_C0_DIAG_DUPLICATE_DECLARATION = 1,
  GSLT_C0_DIAG_EMPTY_HEAD            = 2,
  GSLT_C0_DIAG_UNDECLARED_HEAD       = 3,
  GSLT_C0_DIAG_UNBOUND_GUARD         = 4,
  GSLT_C0_DIAG_UNBOUND_GOAL          = 5,
  GSLT_C0_DIAG_UNDECLARED_GOAL       = 6,
  GSLT_C0_DIAG_UNDECLARED_QUERY      = 7
} GsltC0DiagKind;

typedef struct {
  GsltC0DiagKind    kind;
  uint32_t          rule_index;
  GsltC0Declaration decl;
  GsltC0Head        head;
  GsltC0Guard       guard;
  GsltC0Goal        goal;
} GsltC0Diagnostic;

typedef struct {
  bool               is_c1;
  uint32_t           ndecls;
  GsltC0Declaration *decls;
  uint32_t           nrules;
  GsltC0Rule        *rules;
  uint32_t           ninputs;
  GsltC0Head        *inputs;
  uint32_t           nquery_goals;
  GsltC0Goal        *query_goals;
} GsltC0Program;

/* Structural equality of C0 IR (for multi-packet catalogue agreement & roundtrips) */
static inline bool gslt_c0_value_eq(const GsltC0Value *a, const GsltC0Value *b) {
  if (a == b) return true;
  if (!a || !b || a->kind != b->kind) return false;
  switch (a->kind) {
    case GSLT_C0_VAL_INT: return c0_bigint_eq(&a->ival, &b->ival);
    case GSLT_C0_VAL_ATOM: return gslt_str_eq(a->atom, b->atom);
    case GSLT_C0_VAL_VAR: return a->var_id == b->var_id;
    case GSLT_C0_VAL_TUPLE:
      if (a->nfields != b->nfields) return false;
      for (uint32_t i = 0; i < a->nfields; i++) {
        if (!gslt_c0_value_eq(a->fields[i], b->fields[i])) return false;
      }
      return true;
    case GSLT_C0_VAL_COMPOUND:
      if (!gslt_str_eq(a->atom, b->atom) || a->nfields != b->nfields) return false;
      for (uint32_t i = 0; i < a->nfields; i++) {
        if (!gslt_c0_value_eq(a->fields[i], b->fields[i])) return false;
      }
      return true;
  }
  return false;
}

static inline bool gslt_c0_term_eq(const GsltC0Term *a, const GsltC0Term *b) {
  if (a == b) return true;
  if (!a || !b || a->kind != b->kind) return false;
  switch (a->kind) {
    case GSLT_C0_TERM_VAL: return gslt_c0_value_eq(a->val, b->val);
    case GSLT_C0_TERM_VAR: return a->var_idx == b->var_idx;
    case GSLT_C0_TERM_TUPLE:
      if (a->nfields != b->nfields) return false;
      for (uint32_t i = 0; i < a->nfields; i++) {
        if (!gslt_c0_term_eq(a->fields[i], b->fields[i])) return false;
      }
      return true;
    case GSLT_C0_TERM_COMPOUND:
      if (!gslt_str_eq(a->functor, b->functor) || a->nfields != b->nfields) return false;
      for (uint32_t i = 0; i < a->nfields; i++) {
        if (!gslt_c0_term_eq(a->fields[i], b->fields[i])) return false;
      }
      return true;
  }
  return false;
}

static inline bool gslt_c0_head_eq(const GsltC0Head *a, const GsltC0Head *b) {
  if (!gslt_str_eq(a->name, b->name) || a->arity != b->arity) return false;
  for (uint32_t i = 0; i < a->arity; i++) {
    if (!gslt_c0_term_eq(a->args[i], b->args[i])) return false;
  }
  return true;
}

static inline bool gslt_c0_iexpr_eq(const GsltC0IntExpr *a, const GsltC0IntExpr *b) {
  if (a == b) return true;
  if (!a || !b || a->kind != b->kind) return false;
  switch (a->kind) {
    case GSLT_C0_IEXPR_LIT: return c0_bigint_eq(&a->lit, &b->lit);
    case GSLT_C0_IEXPR_VAR: return a->var_idx == b->var_idx;
    case GSLT_C0_IEXPR_OP:
      return a->op == b->op && gslt_c0_iexpr_eq(a->left, b->left) && gslt_c0_iexpr_eq(a->right, b->right);
  }
  return false;
}

static inline bool gslt_c0_guard_eq(const GsltC0Guard *a, const GsltC0Guard *b) {
  if (a->kind != b->kind) return false;
  if (a->kind == GSLT_C0_GUARD_COMPARE) {
    return a->cmp == b->cmp && gslt_c0_iexpr_eq(a->e_left, b->e_left) && gslt_c0_iexpr_eq(a->e_right, b->e_right);
  }
  return gslt_c0_term_eq(a->t_left, b->t_left) && gslt_c0_term_eq(a->t_right, b->t_right);
}

static inline bool gslt_c0_goal_eq(const GsltC0Goal *a, const GsltC0Goal *b) {
  if (a->kind != b->kind) return false;
  switch (a->kind) {
    case GSLT_C0_GOAL_TELL: return gslt_c0_head_eq(&a->tell_head, &b->tell_head);
    case GSLT_C0_GOAL_ASSIGN: return a->assign_var == b->assign_var && gslt_c0_iexpr_eq(a->assign_expr, b->assign_expr);
    case GSLT_C0_GOAL_FAIL: return true;
    case GSLT_C0_GOAL_UNIFY:
    case GSLT_C0_GOAL_UNIFY_OC:
      return gslt_c0_term_eq(a->unify_left, b->unify_left) && gslt_c0_term_eq(a->unify_right, b->unify_right);
    case GSLT_C0_GOAL_GUARD:
      return gslt_c0_guard_eq(&a->guard_test, &b->guard_test);
  }
  return false;
}

static inline bool gslt_c0_rule_eq(const GsltC0Rule *a, const GsltC0Rule *b) {
  if (!gslt_str_eq(a->name, b->name) || a->nkept != b->nkept || a->nremoved != b->nremoved ||
      a->nguards != b->nguards || a->nbody != b->nbody) return false;
  for (uint32_t i = 0; i < a->nkept; i++) if (!gslt_c0_head_eq(&a->kept[i], &b->kept[i])) return false;
  for (uint32_t i = 0; i < a->nremoved; i++) if (!gslt_c0_head_eq(&a->removed[i], &b->removed[i])) return false;
  for (uint32_t i = 0; i < a->nguards; i++) if (!gslt_c0_guard_eq(&a->guards[i], &b->guards[i])) return false;
  for (uint32_t i = 0; i < a->nbody; i++) if (!gslt_c0_goal_eq(&a->body[i], &b->body[i])) return false;
  return true;
}

static inline bool gslt_c0_program_eq(const GsltC0Program *a, const GsltC0Program *b) {
  if (!a || !b) return a == b;
  if (a->ndecls != b->ndecls || a->nrules != b->nrules || a->ninputs != b->ninputs ||
      a->nquery_goals != b->nquery_goals) return false;
  for (uint32_t i = 0; i < a->ndecls; i++) {
    if (!gslt_str_eq(a->decls[i].name, b->decls[i].name) || a->decls[i].arity != b->decls[i].arity) return false;
  }
  for (uint32_t i = 0; i < a->nrules; i++) {
    if (!gslt_c0_rule_eq(&a->rules[i], &b->rules[i])) return false;
  }
  for (uint32_t i = 0; i < a->ninputs; i++) {
    if (!gslt_c0_head_eq(&a->inputs[i], &b->inputs[i])) return false;
  }
  for (uint32_t i = 0; i < a->nquery_goals; i++) {
    if (!gslt_c0_goal_eq(&a->query_goals[i], &b->query_goals[i])) return false;
  }
  return true;
}

/* ---- Whole-Scope Variable Allocation (CHRPrologLowering.lean / lowering.metta) ---- */
typedef struct {
  GsltByteStr name;
  uint32_t    index;
} GsltC0VarSlot;

typedef struct {
  uint32_t       nslots;
  GsltC0VarSlot *slots;
} GsltC0VarAlloc;

static inline GsltPlTerm *gslt_c0_number_fresh(GsltArena *a, const GsltPlTerm *t, uint32_t *next_id) {
  if (!t) return NULL;
  if (t->kind == GSLT_PL_FRESH) {
    char buf[32];
    int n = snprintf(buf, sizeof(buf), "_#%u", (*next_id)++);
    GsltPlTerm *out = (GsltPlTerm *)gslt_arena_alloc(a, sizeof(GsltPlTerm));
    out->kind = GSLT_PL_VAR;
    out->name = gslt_str_intern(a, buf, (size_t)n);
    return out;
  }
  if (t->kind == GSLT_PL_COMPOUND) {
    GsltPlTerm *out = (GsltPlTerm *)gslt_arena_alloc(a, sizeof(GsltPlTerm));
    out->kind = GSLT_PL_COMPOUND;
    out->name = t->name;
    out->nargs = t->nargs;
    if (t->nargs > 0) {
      out->args = (GsltPlTerm **)gslt_arena_alloc(a, t->nargs * sizeof(GsltPlTerm *));
      for (uint32_t i = 0; i < t->nargs; i++) {
        out->args[i] = gslt_c0_number_fresh(a, t->args[i], next_id);
      }
    }
    return out;
  }
  GsltPlTerm *copy = (GsltPlTerm *)gslt_arena_alloc(a, sizeof(GsltPlTerm));
  *copy = *t;
  return copy;
}

static inline void gslt_c0_collect_vars(GsltArena *a, const GsltPlTerm *t,
                                        GsltByteStr **names, uint32_t *count, uint32_t *cap) {
  if (!t) return;
  if (t->kind == GSLT_PL_VAR) {
    for (uint32_t i = 0; i < *count; i++) {
      if (gslt_str_eq((*names)[i], t->name)) return;
    }
    if (*count >= *cap) {
      uint32_t ncap = (*cap) * 2;
      GsltByteStr *narr = (GsltByteStr *)gslt_arena_alloc(a, ncap * sizeof(GsltByteStr));
      memcpy(narr, *names, (*count) * sizeof(GsltByteStr));
      *names = narr;
      *cap = ncap;
    }
    (*names)[(*count)++] = t->name;
  } else if (t->kind == GSLT_PL_COMPOUND) {
    for (uint32_t i = 0; i < t->nargs; i++) {
      gslt_c0_collect_vars(a, t->args[i], names, count, cap);
    }
  }
}

/* preferredIndex? in CHRPrologLowering.lean:
 * "V<n>" keeps index n iff spelling == "V" ++ toString n. */
static inline bool gslt_c0_preferred_index(GsltByteStr spelling, uint32_t *out_idx) {
  if (spelling.len < 2 || spelling.bytes[0] != 'V') return false;
  /* Leading zero is only canonical for "V0" */
  if (spelling.bytes[1] == '0' && spelling.len > 2) return false;
  uint64_t val = 0;
  for (uint32_t i = 1; i < spelling.len; i++) {
    char c = spelling.bytes[i];
    if (c < '0' || c > '9') return false;
    val = val * 10u + (uint64_t)(c - '0');
    if (val > (uint64_t)UINT32_MAX) return false;
  }
  *out_idx = (uint32_t)val;
  return true;
}

static inline GsltC0VarAlloc gslt_c0_allocate_vars(GsltArena *a, const GsltPlTerm *numbered_rule) {
  uint32_t cap = 16, count = 0;
  GsltByteStr *names = (GsltByteStr *)gslt_arena_alloc(a, cap * sizeof(GsltByteStr));
  gslt_c0_collect_vars(a, numbered_rule, &names, &count, &cap);
  GsltC0VarAlloc alloc;
  alloc.nslots = count;
  alloc.slots = (GsltC0VarSlot *)gslt_arena_alloc(a, (count > 0 ? count : 1) * sizeof(GsltC0VarSlot));
  uint32_t *pref = (uint32_t *)gslt_arena_alloc(a, (count > 0 ? count : 1) * sizeof(uint32_t));
  bool all_pref = true;
  for (uint32_t i = 0; i < count; i++) {
    if (!gslt_c0_preferred_index(names[i], &pref[i])) {
      all_pref = false;
      break;
    }
    for (uint32_t j = 0; j < i; j++) {
      if (pref[j] == pref[i]) {
        all_pref = false;
        break;
      }
    }
    if (!all_pref) break;
  }
  for (uint32_t i = 0; i < count; i++) {
    alloc.slots[i].name = names[i];
    alloc.slots[i].index = all_pref ? pref[i] : i;
  }
  return alloc;
}

static inline bool gslt_c0_lookup_var(const GsltC0VarAlloc *alloc, GsltByteStr name, uint32_t *out_idx) {
  for (uint32_t i = 0; i < alloc->nslots; i++) {
    if (gslt_str_eq(alloc->slots[i].name, name)) {
      *out_idx = alloc->slots[i].index;
      return true;
    }
  }
  return false;
}

/* ---- Lowering PlTerm -> C0/C1 IR (CHRPrologLowering.lean / lowering.metta) ---- */
static inline GsltC0Term *gslt_c0_lower_term_ex(GsltArena *a, const GsltC0VarAlloc *alloc,
                                                 const GsltPlTerm *t, bool allow_c1,
                                                 char *err, size_t err_cap) {
  if (!t) return NULL;
  if (t->kind == GSLT_PL_VAR) {
    uint32_t idx = 0;
    if (!alloc || !gslt_c0_lookup_var(alloc, t->name, &idx)) {
      snprintf(err, err_cap, "source variable is outside its rule scope");
      return NULL;
    }
    GsltC0Term *ct = (GsltC0Term *)gslt_arena_alloc(a, sizeof(GsltC0Term));
    ct->kind = GSLT_C0_TERM_VAR;
    ct->var_idx = idx;
    return ct;
  }
  if (t->kind == GSLT_PL_INT) {
    GsltC0Value *v = (GsltC0Value *)gslt_arena_alloc(a, sizeof(GsltC0Value));
    v->kind = GSLT_C0_VAL_INT;
    v->ival = t->ival;
    GsltC0Term *ct = (GsltC0Term *)gslt_arena_alloc(a, sizeof(GsltC0Term));
    ct->kind = GSLT_C0_TERM_VAL;
    ct->val = v;
    return ct;
  }
  if (t->kind == GSLT_PL_ATOM) {
    GsltC0Value *v = (GsltC0Value *)gslt_arena_alloc(a, sizeof(GsltC0Value));
    v->kind = GSLT_C0_VAL_ATOM;
    v->atom = t->name;
    GsltC0Term *ct = (GsltC0Term *)gslt_arena_alloc(a, sizeof(GsltC0Term));
    ct->kind = GSLT_C0_TERM_VAL;
    ct->val = v;
    return ct;
  }
  if (t->kind == GSLT_PL_COMPOUND) {
    bool is_tuple = gslt_str_eq_cstr(t->name, "tuple");
    if (!is_tuple && !allow_c1) {
      snprintf(err, err_cap, "C0 compound values use tuple(...)");
      return NULL;
    }
    GsltC0Term *ct = (GsltC0Term *)gslt_arena_alloc(a, sizeof(GsltC0Term));
    ct->kind = is_tuple ? GSLT_C0_TERM_TUPLE : GSLT_C0_TERM_COMPOUND;
    ct->functor = t->name;
    ct->nfields = t->nargs;
    if (t->nargs > 0) {
      ct->fields = (GsltC0Term **)gslt_arena_alloc(a, t->nargs * sizeof(GsltC0Term *));
      for (uint32_t i = 0; i < t->nargs; i++) {
        ct->fields[i] = gslt_c0_lower_term_ex(a, alloc, t->args[i], allow_c1, err, err_cap);
        if (!ct->fields[i]) return NULL;
      }
    }
    return ct;
  }
  snprintf(err, err_cap, "C0 values are integers, atoms and tuples");
  return NULL;
}

static inline GsltC0Term *gslt_c0_lower_term(GsltArena *a, const GsltC0VarAlloc *alloc,
                                             const GsltPlTerm *t, char *err, size_t err_cap) {
  return gslt_c0_lower_term_ex(a, alloc, t, false, err, err_cap);
}

/* Convert a ground GsltC0Term (which may contain nested GSLT_C0_TERM_TUPLE) to a GsltC0Value */
static inline GsltC0Value *gslt_c0_ground_term_to_val(GsltArena *a, const GsltC0Term *t) {
  if (!t) return NULL;
  if (t->kind == GSLT_C0_TERM_VAL) return t->val;
  if (t->kind == GSLT_C0_TERM_VAR) return NULL;
  if (t->kind == GSLT_C0_TERM_TUPLE || t->kind == GSLT_C0_TERM_COMPOUND) {
    GsltC0Value *v = (GsltC0Value *)gslt_arena_alloc(a, sizeof(GsltC0Value));
    v->kind = (t->kind == GSLT_C0_TERM_TUPLE) ? GSLT_C0_VAL_TUPLE : GSLT_C0_VAL_COMPOUND;
    v->atom = t->functor;
    v->nfields = t->nfields;
    if (t->nfields > 0) {
      v->fields = (GsltC0Value **)gslt_arena_alloc(a, t->nfields * sizeof(GsltC0Value *));
      for (uint32_t i = 0; i < t->nfields; i++) {
        v->fields[i] = gslt_c0_ground_term_to_val(a, t->fields[i]);
        if (!v->fields[i]) return NULL;
      }
    }
    return v;
  }
  return NULL;
}

static inline bool gslt_c0_lower_head_ex(GsltArena *a, const GsltC0VarAlloc *alloc,
                                         const GsltPlTerm *t, bool allow_c1,
                                         GsltC0Head *out, char *err, size_t err_cap) {
  memset(out, 0, sizeof(*out));
  if (!t) return false;
  if (t->kind == GSLT_PL_ATOM) {
    out->name = t->name;
    out->arity = 0;
    out->args = NULL;
    return true;
  }
  if (t->kind == GSLT_PL_COMPOUND) {
    out->name = t->name;
    out->arity = t->nargs;
    out->args = (GsltC0Term **)gslt_arena_alloc(a, t->nargs * sizeof(GsltC0Term *));
    for (uint32_t i = 0; i < t->nargs; i++) {
      out->args[i] = gslt_c0_lower_term_ex(a, alloc, t->args[i], allow_c1, err, err_cap);
      if (!out->args[i]) return false;
    }
    return true;
  }
  snprintf(err, err_cap, "expected a CHR constraint");
  return false;
}

static inline bool gslt_c0_lower_head(GsltArena *a, const GsltC0VarAlloc *alloc,
                                      const GsltPlTerm *t, GsltC0Head *out,
                                      char *err, size_t err_cap) {
  return gslt_c0_lower_head_ex(a, alloc, t, false, out, err, err_cap);
}

static inline GsltC0IntExpr *gslt_c0_lower_expr(GsltArena *a, const GsltC0VarAlloc *alloc,
                                                const GsltPlTerm *t, char *err, size_t err_cap) {
  if (!t) return NULL;
  if (t->kind == GSLT_PL_INT) {
    GsltC0IntExpr *e = (GsltC0IntExpr *)gslt_arena_alloc(a, sizeof(GsltC0IntExpr));
    e->kind = GSLT_C0_IEXPR_LIT;
    e->lit = t->ival;
    return e;
  }
  if (t->kind == GSLT_PL_VAR) {
    uint32_t idx = 0;
    if (!alloc || !gslt_c0_lookup_var(alloc, t->name, &idx)) {
      snprintf(err, err_cap, "arithmetic variable is outside its rule scope");
      return NULL;
    }
    GsltC0IntExpr *e = (GsltC0IntExpr *)gslt_arena_alloc(a, sizeof(GsltC0IntExpr));
    e->kind = GSLT_C0_IEXPR_VAR;
    e->var_idx = idx;
    return e;
  }
  if (t->kind == GSLT_PL_COMPOUND) {
    if (t->nargs == 1) {
      if (gslt_str_eq_cstr(t->name, "-")) {
        GsltC0IntExpr *inner = gslt_c0_lower_expr(a, alloc, t->args[0], err, err_cap);
        if (!inner) return NULL;
        GsltC0IntExpr *zero = (GsltC0IntExpr *)gslt_arena_alloc(a, sizeof(GsltC0IntExpr));
        zero->kind = GSLT_C0_IEXPR_LIT;
        c0_bigint_zero(&zero->lit);
        GsltC0IntExpr *e = (GsltC0IntExpr *)gslt_arena_alloc(a, sizeof(GsltC0IntExpr));
        e->kind = GSLT_C0_IEXPR_OP;
        e->op = GSLT_C0_IOP_SUB;
        e->left = zero;
        e->right = inner;
        return e;
      }
      if (gslt_str_eq_cstr(t->name, "+")) {
        return gslt_c0_lower_expr(a, alloc, t->args[0], err, err_cap);
      }
      snprintf(err, err_cap, "unsupported C0 unary integer operation");
      return NULL;
    }
    if (t->nargs == 2) {
      GsltC0IntOp op;
      if (gslt_str_eq_cstr(t->name, "+")) op = GSLT_C0_IOP_ADD;
      else if (gslt_str_eq_cstr(t->name, "-")) op = GSLT_C0_IOP_SUB;
      else if (gslt_str_eq_cstr(t->name, "*")) op = GSLT_C0_IOP_MUL;
      else if (gslt_str_eq_cstr(t->name, "//")) op = GSLT_C0_IOP_QUOT;
      else if (gslt_str_eq_cstr(t->name, "rem")) op = GSLT_C0_IOP_REM;
      else if (gslt_str_eq_cstr(t->name, "mod")) op = GSLT_C0_IOP_MOD;
      else {
        snprintf(err, err_cap, "unsupported C0 integer operation");
        return NULL;
      }
      GsltC0IntExpr *l = gslt_c0_lower_expr(a, alloc, t->args[0], err, err_cap);
      if (!l) return NULL;
      GsltC0IntExpr *r = gslt_c0_lower_expr(a, alloc, t->args[1], err, err_cap);
      if (!r) return NULL;
      GsltC0IntExpr *e = (GsltC0IntExpr *)gslt_arena_alloc(a, sizeof(GsltC0IntExpr));
      e->kind = GSLT_C0_IEXPR_OP;
      e->op = op;
      e->left = l;
      e->right = r;
      return e;
    }
    snprintf(err, err_cap, "invalid C0 arithmetic arity");
    return NULL;
  }
  snprintf(err, err_cap, "C0 arithmetic requires an integer expression");
  return NULL;
}

static inline bool gslt_c0_lower_guard_ex(GsltArena *a, const GsltC0VarAlloc *alloc,
                                          const GsltPlTerm *t, bool allow_c1,
                                          GsltC0Guard *out, char *err, size_t err_cap) {
  memset(out, 0, sizeof(*out));
  if (!t || t->kind != GSLT_PL_COMPOUND || t->nargs != 2) {
    snprintf(err, err_cap, "expected a C0 guard test");
    return false;
  }
  if (gslt_str_eq_cstr(t->name, "==") || gslt_str_eq_cstr(t->name, "\\==")) {
    out->kind = gslt_str_eq_cstr(t->name, "==") ? GSLT_C0_GUARD_IDENTICAL : GSLT_C0_GUARD_DISTINCT;
    out->t_left = gslt_c0_lower_term_ex(a, alloc, t->args[0], allow_c1, err, err_cap);
    if (!out->t_left) return false;
    out->t_right = gslt_c0_lower_term_ex(a, alloc, t->args[1], allow_c1, err, err_cap);
    if (!out->t_right) return false;
    return true;
  }
  GsltC0CmpOp cmp;
  if (gslt_str_eq_cstr(t->name, "=:=")) cmp = GSLT_C0_CMP_EQ;
  else if (gslt_str_eq_cstr(t->name, "=\\=")) cmp = GSLT_C0_CMP_NE;
  else if (gslt_str_eq_cstr(t->name, "<")) cmp = GSLT_C0_CMP_LT;
  else if (gslt_str_eq_cstr(t->name, "=<")) cmp = GSLT_C0_CMP_LE;
  else if (gslt_str_eq_cstr(t->name, ">")) cmp = GSLT_C0_CMP_GT;
  else if (gslt_str_eq_cstr(t->name, ">=")) cmp = GSLT_C0_CMP_GE;
  else {
    snprintf(err, err_cap, "unsupported C0 guard test");
    return false;
  }
  out->kind = GSLT_C0_GUARD_COMPARE;
  out->cmp = cmp;
  out->e_left = gslt_c0_lower_expr(a, alloc, t->args[0], err, err_cap);
  if (!out->e_left) return false;
  out->e_right = gslt_c0_lower_expr(a, alloc, t->args[1], err, err_cap);
  if (!out->e_right) return false;
  return true;
}

static inline bool gslt_c0_lower_guard(GsltArena *a, const GsltC0VarAlloc *alloc,
                                       const GsltPlTerm *t, GsltC0Guard *out,
                                       char *err, size_t err_cap) {
  return gslt_c0_lower_guard_ex(a, alloc, t, false, out, err, err_cap);
}

static inline bool gslt_c0_lower_goal_ex(GsltArena *a, const GsltC0VarAlloc *alloc,
                                         const GsltPlTerm *t, bool allow_c1,
                                         GsltC0Goal *out, char *err, size_t err_cap) {
  memset(out, 0, sizeof(*out));
  if (!t) return false;
  if (t->kind == GSLT_PL_ATOM && gslt_str_eq_cstr(t->name, "fail")) {
    out->kind = GSLT_C0_GOAL_FAIL;
    return true;
  }
  if (t->kind == GSLT_PL_COMPOUND && t->nargs == 2 && gslt_str_eq_cstr(t->name, "is")) {
    if (t->args[0]->kind != GSLT_PL_VAR) {
      snprintf(err, err_cap, "C0 assignments require a variable on the left of is");
      return false;
    }
    uint32_t idx = 0;
    if (!alloc || !gslt_c0_lookup_var(alloc, t->args[0]->name, &idx)) {
      snprintf(err, err_cap, "assignment variable is outside its rule scope");
      return false;
    }
    GsltC0IntExpr *e = gslt_c0_lower_expr(a, alloc, t->args[1], err, err_cap);
    if (!e) return false;
    out->kind = GSLT_C0_GOAL_ASSIGN;
    out->assign_var = idx;
    out->assign_expr = e;
    return true;
  }
  if (allow_c1 && t->kind == GSLT_PL_COMPOUND && t->nargs == 2 &&
      (gslt_str_eq_cstr(t->name, "=") || gslt_str_eq_cstr(t->name, "unify_with_occurs_check"))) {
    out->kind = gslt_str_eq_cstr(t->name, "=") ? GSLT_C0_GOAL_UNIFY : GSLT_C0_GOAL_UNIFY_OC;
    out->unify_left = gslt_c0_lower_term_ex(a, alloc, t->args[0], true, err, err_cap);
    if (!out->unify_left) return false;
    out->unify_right = gslt_c0_lower_term_ex(a, alloc, t->args[1], true, err, err_cap);
    if (!out->unify_right) return false;
    return true;
  }
  if (allow_c1 && t->kind == GSLT_PL_COMPOUND && t->nargs == 2 &&
      (gslt_str_eq_cstr(t->name, "==") || gslt_str_eq_cstr(t->name, "\\==") ||
       gslt_str_eq_cstr(t->name, "=:=") || gslt_str_eq_cstr(t->name, "=\\=") ||
       gslt_str_eq_cstr(t->name, "<") || gslt_str_eq_cstr(t->name, "=<") ||
       gslt_str_eq_cstr(t->name, ">") || gslt_str_eq_cstr(t->name, ">="))) {
    out->kind = GSLT_C0_GOAL_GUARD;
    return gslt_c0_lower_guard_ex(a, alloc, t, true, &out->guard_test, err, err_cap);
  }
  out->kind = GSLT_C0_GOAL_TELL;
  return gslt_c0_lower_head_ex(a, alloc, t, allow_c1, &out->tell_head, err, err_cap);
}

static inline bool gslt_c0_lower_goal(GsltArena *a, const GsltC0VarAlloc *alloc,
                                      const GsltPlTerm *t, GsltC0Goal *out,
                                      char *err, size_t err_cap) {
  return gslt_c0_lower_goal_ex(a, alloc, t, false, out, err, err_cap);
}

static inline void gslt_c0_flatten_conjunction(GsltArena *a, const GsltPlTerm *t,
                                               const GsltPlTerm ***arr, uint32_t *count, uint32_t *cap) {
  if (!t) return;
  if (t->kind == GSLT_PL_COMPOUND && t->nargs == 2 && gslt_str_eq_cstr(t->name, ",")) {
    gslt_c0_flatten_conjunction(a, t->args[0], arr, count, cap);
    gslt_c0_flatten_conjunction(a, t->args[1], arr, count, cap);
    return;
  }
  if (*count >= *cap) {
    uint32_t ncap = (*cap) * 2;
    const GsltPlTerm **narr = (const GsltPlTerm **)gslt_arena_alloc(a, ncap * sizeof(const GsltPlTerm *));
    memcpy(narr, *arr, (*count) * sizeof(const GsltPlTerm *));
    *arr = narr;
    *cap = ncap;
  }
  (*arr)[(*count)++] = t;
}

static inline bool gslt_c0_lower_heads_conj_ex(GsltArena *a, const GsltC0VarAlloc *alloc,
                                               const GsltPlTerm *t, bool allow_c1,
                                               GsltC0Head **out_heads, uint32_t *out_count,
                                               char *err, size_t err_cap) {
  uint32_t cap = 8, count = 0;
  const GsltPlTerm **conj = (const GsltPlTerm **)gslt_arena_alloc(a, cap * sizeof(const GsltPlTerm *));
  gslt_c0_flatten_conjunction(a, t, &conj, &count, &cap);
  GsltC0Head *heads = (GsltC0Head *)gslt_arena_alloc(a, (count > 0 ? count : 1) * sizeof(GsltC0Head));
  for (uint32_t i = 0; i < count; i++) {
    if (!gslt_c0_lower_head_ex(a, alloc, conj[i], allow_c1, &heads[i], err, err_cap)) return false;
  }
  *out_heads = heads;
  *out_count = count;
  return true;
}

static inline bool gslt_c0_lower_guards_conj_ex(GsltArena *a, const GsltC0VarAlloc *alloc,
                                                const GsltPlTerm *t, bool allow_c1,
                                                GsltC0Guard **out_guards, uint32_t *out_count,
                                                char *err, size_t err_cap) {
  uint32_t cap = 8, count = 0;
  const GsltPlTerm **conj = (const GsltPlTerm **)gslt_arena_alloc(a, cap * sizeof(const GsltPlTerm *));
  gslt_c0_flatten_conjunction(a, t, &conj, &count, &cap);
  GsltC0Guard *guards = (GsltC0Guard *)gslt_arena_alloc(a, (count > 0 ? count : 1) * sizeof(GsltC0Guard));
  uint32_t ng = 0;
  for (uint32_t i = 0; i < count; i++) {
    if (conj[i]->kind == GSLT_PL_ATOM && gslt_str_eq_cstr(conj[i]->name, "true")) continue;
    if (!gslt_c0_lower_guard_ex(a, alloc, conj[i], allow_c1, &guards[ng++], err, err_cap)) return false;
  }
  *out_guards = guards;
  *out_count = ng;
  return true;
}

static inline bool gslt_c0_lower_goals_conj_ex(GsltArena *a, const GsltC0VarAlloc *alloc,
                                               const GsltPlTerm *t, bool allow_c1,
                                               GsltC0Goal **out_goals, uint32_t *out_count,
                                               char *err, size_t err_cap) {
  uint32_t cap = 8, count = 0;
  const GsltPlTerm **conj = (const GsltPlTerm **)gslt_arena_alloc(a, cap * sizeof(const GsltPlTerm *));
  gslt_c0_flatten_conjunction(a, t, &conj, &count, &cap);
  GsltC0Goal *goals = (GsltC0Goal *)gslt_arena_alloc(a, (count > 0 ? count : 1) * sizeof(GsltC0Goal));
  uint32_t nb = 0;
  for (uint32_t i = 0; i < count; i++) {
    if (conj[i]->kind == GSLT_PL_ATOM && gslt_str_eq_cstr(conj[i]->name, "true")) continue;
    if (!gslt_c0_lower_goal_ex(a, alloc, conj[i], allow_c1, &goals[nb++], err, err_cap)) return false;
  }
  *out_goals = goals;
  *out_count = nb;
  return true;
}

static inline bool gslt_c0_lower_rule_ex(GsltArena *a, uint32_t ordinal, const GsltPlTerm *written,
                                         bool allow_c1, GsltC0Rule *out_rule, char *err, size_t err_cap) {
  memset(out_rule, 0, sizeof(*out_rule));
  uint32_t fresh_next = 0;
  GsltPlTerm *source = gslt_c0_number_fresh(a, written, &fresh_next);
  GsltC0VarAlloc alloc = gslt_c0_allocate_vars(a, source);

  const GsltPlTerm *body_term = source;
  if (source->kind == GSLT_PL_COMPOUND && source->nargs == 2 && gslt_str_eq_cstr(source->name, "@")) {
    if (source->args[0]->kind != GSLT_PL_ATOM) {
      snprintf(err, err_cap, "CHR rule names must be atoms");
      return false;
    }
    out_rule->name = source->args[0]->name;
    body_term = source->args[1];
  } else {
    char rbuf[32];
    int n = snprintf(rbuf, sizeof(rbuf), "rule:%u", ordinal);
    out_rule->name = gslt_str_intern(a, rbuf, (size_t)n);
  }

  if (body_term->kind != GSLT_PL_COMPOUND || body_term->nargs != 2) {
    snprintf(err, err_cap, "expected a CHR rule");
    return false;
  }
  const GsltPlTerm *left = body_term->args[0];
  const GsltPlTerm *right = body_term->args[1];
  if (gslt_str_eq_cstr(body_term->name, "==>")) {
    if (!gslt_c0_lower_heads_conj_ex(a, &alloc, left, allow_c1, &out_rule->kept, &out_rule->nkept, err, err_cap)) return false;
    out_rule->removed = NULL;
    out_rule->nremoved = 0;
  } else if (gslt_str_eq_cstr(body_term->name, "<=>")) {
    if (left->kind == GSLT_PL_COMPOUND && left->nargs == 2 && gslt_str_eq_cstr(left->name, "\\")) {
      if (!gslt_c0_lower_heads_conj_ex(a, &alloc, left->args[0], allow_c1, &out_rule->kept, &out_rule->nkept, err, err_cap)) return false;
      if (!gslt_c0_lower_heads_conj_ex(a, &alloc, left->args[1], allow_c1, &out_rule->removed, &out_rule->nremoved, err, err_cap)) return false;
    } else {
      out_rule->kept = NULL;
      out_rule->nkept = 0;
      if (!gslt_c0_lower_heads_conj_ex(a, &alloc, left, allow_c1, &out_rule->removed, &out_rule->nremoved, err, err_cap)) return false;
    }
  } else {
    snprintf(err, err_cap, "expected <=> or ==>");
    return false;
  }

  if (right->kind == GSLT_PL_COMPOUND && right->nargs == 2 && gslt_str_eq_cstr(right->name, "|")) {
    if (!gslt_c0_lower_guards_conj_ex(a, &alloc, right->args[0], allow_c1, &out_rule->guards, &out_rule->nguards, err, err_cap)) return false;
    if (!gslt_c0_lower_goals_conj_ex(a, &alloc, right->args[1], allow_c1, &out_rule->body, &out_rule->nbody, err, err_cap)) return false;
  } else {
    out_rule->guards = NULL;
    out_rule->nguards = 0;
    if (!gslt_c0_lower_goals_conj_ex(a, &alloc, right, allow_c1, &out_rule->body, &out_rule->nbody, err, err_cap)) return false;
  }
  return true;
}

static inline bool gslt_c0_lower_rule(GsltArena *a, uint32_t ordinal, const GsltPlTerm *written,
                                      GsltC0Rule *out_rule, char *err, size_t err_cap) {
  return gslt_c0_lower_rule_ex(a, ordinal, written, false, out_rule, err, err_cap);
}

/* ---- Static Admission (Admission.lean & CHRPrologLowering.lean) ---- */
static inline void gslt_c0_term_vars(const GsltC0Term *t, uint32_t *vars, uint32_t *nvars, uint32_t cap) {
  if (!t) return;
  if (t->kind == GSLT_C0_TERM_VAR) {
    if (*nvars < cap) vars[(*nvars)++] = t->var_idx;
  } else if (t->kind == GSLT_C0_TERM_TUPLE || t->kind == GSLT_C0_TERM_COMPOUND) {
    for (uint32_t i = 0; i < t->nfields; i++) {
      gslt_c0_term_vars(t->fields[i], vars, nvars, cap);
    }
  }
}

static inline void gslt_c0_head_vars(const GsltC0Head *h, uint32_t *vars, uint32_t *nvars, uint32_t cap) {
  for (uint32_t i = 0; i < h->arity; i++) {
    gslt_c0_term_vars(h->args[i], vars, nvars, cap);
  }
}

static inline void gslt_c0_expr_vars(const GsltC0IntExpr *e, uint32_t *vars, uint32_t *nvars, uint32_t cap) {
  if (!e) return;
  if (e->kind == GSLT_C0_IEXPR_VAR) {
    if (*nvars < cap) vars[(*nvars)++] = e->var_idx;
  } else if (e->kind == GSLT_C0_IEXPR_OP) {
    gslt_c0_expr_vars(e->left, vars, nvars, cap);
    gslt_c0_expr_vars(e->right, vars, nvars, cap);
  }
}

static inline void gslt_c0_guard_vars(const GsltC0Guard *g, uint32_t *vars, uint32_t *nvars, uint32_t cap) {
  if (g->kind == GSLT_C0_GUARD_COMPARE) {
    gslt_c0_expr_vars(g->e_left, vars, nvars, cap);
    gslt_c0_expr_vars(g->e_right, vars, nvars, cap);
  } else {
    gslt_c0_term_vars(g->t_left, vars, nvars, cap);
    gslt_c0_term_vars(g->t_right, vars, nvars, cap);
  }
}

static inline bool gslt_c0_vars_available(const uint32_t *bound, uint32_t nbound,
                                          const uint32_t *read, uint32_t nread) {
  for (uint32_t i = 0; i < nread; i++) {
    bool found = false;
    for (uint32_t j = 0; j < nbound; j++) {
      if (bound[j] == read[i]) { found = true; break; }
    }
    if (!found) return false;
  }
  return true;
}

static inline bool gslt_c0_is_declared(const GsltC0Declaration *decls, uint32_t ndecls,
                                       GsltByteStr name, uint32_t arity) {
  for (uint32_t i = 0; i < ndecls; i++) {
    if (decls[i].arity == arity && gslt_str_eq(decls[i].name, name)) return true;
  }
  return false;
}

/* Exact priority order of Admission.diagnose in Mettapedia/Languages/CHR/Admission.lean:
 *   1. duplicateDeclaration
 *   2. per-rule (0 .. nrules-1):
 *      a) emptyHead
 *      b) undeclaredHead (kept ++ removed in order)
 *      c) unboundGuard (guards in order)
 *      d) goals in order:
 *         - .tell head: first check declared (undeclaredGoal), then available (unboundGoal)
 *         - .assign target expr: check expr available (unboundGoal), then add target to bound
 *         - .unify / .unify_oc (C1): add variables in both sides to bound
 *         - .fail: ok */
static inline bool gslt_c0_diagnose_ex(const GsltC0Declaration *decls, uint32_t ndecls,
                                       const GsltC0Rule *rules, uint32_t nrules,
                                       bool allow_c1, GsltC0Diagnostic *out_diag) {
  if (out_diag) memset(out_diag, 0, sizeof(*out_diag));
  for (uint32_t i = 0; i < ndecls; i++) {
    for (uint32_t j = 0; j < i; j++) {
      if (decls[i].arity == decls[j].arity && gslt_str_eq(decls[i].name, decls[j].name)) {
        if (out_diag) {
          out_diag->kind = GSLT_C0_DIAG_DUPLICATE_DECLARATION;
          out_diag->decl = decls[i];
        }
        return false;
      }
    }
  }
  for (uint32_t r = 0; r < nrules; r++) {
    const GsltC0Rule *rule = &rules[r];
    if (rule->nkept + rule->nremoved == 0) {
      if (out_diag) {
        out_diag->kind = GSLT_C0_DIAG_EMPTY_HEAD;
        out_diag->rule_index = r;
      }
      return false;
    }
    uint32_t bound[256];
    uint32_t nbound = 0;
    for (uint32_t i = 0; i < rule->nkept; i++) {
      if (!gslt_c0_is_declared(decls, ndecls, rule->kept[i].name, rule->kept[i].arity)) {
        if (out_diag) {
          out_diag->kind = GSLT_C0_DIAG_UNDECLARED_HEAD;
          out_diag->rule_index = r;
          out_diag->head = rule->kept[i];
        }
        return false;
      }
      gslt_c0_head_vars(&rule->kept[i], bound, &nbound, 256);
    }
    for (uint32_t i = 0; i < rule->nremoved; i++) {
      if (!gslt_c0_is_declared(decls, ndecls, rule->removed[i].name, rule->removed[i].arity)) {
        if (out_diag) {
          out_diag->kind = GSLT_C0_DIAG_UNDECLARED_HEAD;
          out_diag->rule_index = r;
          out_diag->head = rule->removed[i];
        }
        return false;
      }
      gslt_c0_head_vars(&rule->removed[i], bound, &nbound, 256);
    }
    for (uint32_t i = 0; i < rule->nguards; i++) {
      uint32_t gvars[128];
      uint32_t ngvars = 0;
      gslt_c0_guard_vars(&rule->guards[i], gvars, &ngvars, 128);
      if (!gslt_c0_vars_available(bound, nbound, gvars, ngvars)) {
        if (out_diag) {
          out_diag->kind = GSLT_C0_DIAG_UNBOUND_GUARD;
          out_diag->rule_index = r;
          out_diag->guard = rule->guards[i];
        }
        return false;
      }
    }
    for (uint32_t i = 0; i < rule->nbody; i++) {
      const GsltC0Goal *goal = &rule->body[i];
      if (goal->kind == GSLT_C0_GOAL_TELL) {
        if (!gslt_c0_is_declared(decls, ndecls, goal->tell_head.name, goal->tell_head.arity)) {
          if (out_diag) {
            out_diag->kind = GSLT_C0_DIAG_UNDECLARED_GOAL;
            out_diag->rule_index = r;
            out_diag->head = goal->tell_head;
          }
          return false;
        }
        uint32_t hvars[128];
        uint32_t nhvars = 0;
        gslt_c0_head_vars(&goal->tell_head, hvars, &nhvars, 128);
        if (!allow_c1 && !gslt_c0_vars_available(bound, nbound, hvars, nhvars)) {
          if (out_diag) {
            out_diag->kind = GSLT_C0_DIAG_UNBOUND_GOAL;
            out_diag->rule_index = r;
            out_diag->goal = *goal;
          }
          return false;
        }
        if (allow_c1) {
          for (uint32_t v = 0; v < nhvars; v++) {
            if (nbound < 256) bound[nbound++] = hvars[v];
          }
        }
      } else if (goal->kind == GSLT_C0_GOAL_ASSIGN) {
        uint32_t evars[128];
        uint32_t nevars = 0;
        gslt_c0_expr_vars(goal->assign_expr, evars, &nevars, 128);
        if (!gslt_c0_vars_available(bound, nbound, evars, nevars)) {
          if (out_diag) {
            out_diag->kind = GSLT_C0_DIAG_UNBOUND_GOAL;
            out_diag->rule_index = r;
            out_diag->goal = *goal;
          }
          return false;
        }
        if (nbound < 256) bound[nbound++] = goal->assign_var;
      } else if (goal->kind == GSLT_C0_GOAL_UNIFY || goal->kind == GSLT_C0_GOAL_UNIFY_OC) {
        gslt_c0_term_vars(goal->unify_left, bound, &nbound, 256);
        gslt_c0_term_vars(goal->unify_right, bound, &nbound, 256);
      }
    }
  }
  return true;
}

static inline bool gslt_c0_diagnose(const GsltC0Declaration *decls, uint32_t ndecls,
                                    const GsltC0Rule *rules, uint32_t nrules,
                                    GsltC0Diagnostic *out_diag) {
  return gslt_c0_diagnose_ex(decls, ndecls, rules, nrules, false, out_diag);
}

static inline const char *gslt_c0_diag_name(GsltC0DiagKind kind) {
  switch (kind) {
    case GSLT_C0_DIAG_NONE:                  return "none";
    case GSLT_C0_DIAG_DUPLICATE_DECLARATION: return "duplicateDeclaration";
    case GSLT_C0_DIAG_EMPTY_HEAD:            return "emptyHead";
    case GSLT_C0_DIAG_UNDECLARED_HEAD:       return "undeclaredHead";
    case GSLT_C0_DIAG_UNBOUND_GUARD:         return "unboundGuard";
    case GSLT_C0_DIAG_UNBOUND_GOAL:          return "unboundGoal";
    case GSLT_C0_DIAG_UNDECLARED_GOAL:       return "undeclaredGoal";
    case GSLT_C0_DIAG_UNDECLARED_QUERY:      return "undeclaredQuery";
  }
  return "unknown";
}

/* Assemble a C0/C1 Program from lowered PlTerm sentences (CHRPrologLowering.lean / lowering.metta) */
static inline bool gslt_c0_lower_sentences_ex(GsltArena *a, GsltPlTerm **sentences, uint32_t nsentences,
                                              bool allow_c1, GsltC0Program *out_prog,
                                              GsltC0Diagnostic *out_diag, char *err, size_t err_cap) {
  memset(out_prog, 0, sizeof(*out_prog));
  out_prog->is_c1 = allow_c1;
  if (out_diag) memset(out_diag, 0, sizeof(*out_diag));

  uint32_t dcap = 16, rcap = 16, icap = 16, qgcap = 16;
  out_prog->decls = (GsltC0Declaration *)gslt_arena_alloc(a, dcap * sizeof(GsltC0Declaration));
  out_prog->rules = (GsltC0Rule *)gslt_arena_alloc(a, rcap * sizeof(GsltC0Rule));
  out_prog->inputs = (GsltC0Head *)gslt_arena_alloc(a, icap * sizeof(GsltC0Head));
  out_prog->query_goals = (GsltC0Goal *)gslt_arena_alloc(a, qgcap * sizeof(GsltC0Goal));

  for (uint32_t s = 0; s < nsentences; s++) {
    const GsltPlTerm *sent = sentences[s];
    /* 1. Directive :- ... */
    if (sent->kind == GSLT_PL_COMPOUND && sent->nargs == 1 && gslt_str_eq_cstr(sent->name, ":-")) {
      const GsltPlTerm *dir = sent->args[0];
      if (dir->kind == GSLT_PL_COMPOUND && dir->nargs == 1 && gslt_str_eq_cstr(dir->name, "chr_constraint")) {
        uint32_t ccap = 8, ccount = 0;
        const GsltPlTerm **conj = (const GsltPlTerm **)gslt_arena_alloc(a, ccap * sizeof(const GsltPlTerm *));
        gslt_c0_flatten_conjunction(a, dir->args[0], &conj, &ccount, &ccap);
        for (uint32_t i = 0; i < ccount; i++) {
          const GsltPlTerm *item = conj[i];
          if (item->kind != GSLT_PL_COMPOUND || item->nargs != 2 ||
              !gslt_str_eq_cstr(item->name, "/") ||
              item->args[0]->kind != GSLT_PL_ATOM ||
              item->args[1]->kind != GSLT_PL_INT) {
            snprintf(err, err_cap, "expected a constraint name/arity declaration");
            return false;
          }
          if (item->args[1]->ival.sign < 0) {
            snprintf(err, err_cap, "constraint arity must be nonnegative");
            return false;
          }
          uint64_t arity = 0;
          if (!c0_bigint_to_u64(&item->args[1]->ival, &arity) || arity > 1024) {
            snprintf(err, err_cap, "constraint arity out of range");
            return false;
          }
          if (out_prog->ndecls >= dcap) {
            uint32_t ncap = dcap * 2;
            GsltC0Declaration *ndecls = (GsltC0Declaration *)gslt_arena_alloc(a, ncap * sizeof(GsltC0Declaration));
            memcpy(ndecls, out_prog->decls, out_prog->ndecls * sizeof(GsltC0Declaration));
            out_prog->decls = ndecls;
            dcap = ncap;
          }
          out_prog->decls[out_prog->ndecls].name = item->args[0]->name;
          out_prog->decls[out_prog->ndecls].arity = (uint32_t)arity;
          out_prog->ndecls++;
        }
        continue;
      }
      if (allow_c1 && dir->kind == GSLT_PL_COMPOUND && dir->nargs == 2 && gslt_str_eq_cstr(dir->name, "module")) {
        /* C1 permits :- module(Name, [...]). */
        continue;
      }
      if (dir->kind == GSLT_PL_COMPOUND && dir->nargs == 1 && gslt_str_eq_cstr(dir->name, "use_module")) {
        const GsltPlTerm *lib = dir->args[0];
        if (lib->kind == GSLT_PL_COMPOUND && lib->nargs == 1 &&
            gslt_str_eq_cstr(lib->name, "library") &&
            lib->args[0]->kind == GSLT_PL_ATOM &&
            gslt_str_eq_cstr(lib->args[0]->name, "chr")) {
          continue;
        }
        snprintf(err, err_cap, "C0 does not execute host module imports");
        return false;
      }
      if (dir->kind == GSLT_PL_COMPOUND && dir->nargs == 2 && gslt_str_eq_cstr(dir->name, "chr_option")) {
        if (dir->args[0]->kind == GSLT_PL_ATOM && gslt_str_eq_cstr(dir->args[0]->name, "optimize") &&
            dir->args[1]->kind == GSLT_PL_ATOM && gslt_str_eq_cstr(dir->args[1]->name, "off")) {
          continue;
        }
        snprintf(err, err_cap, "C0 uses its declared refined execution profile");
        return false;
      }
      if (dir->kind == GSLT_PL_COMPOUND && dir->nargs == 2 && gslt_str_eq_cstr(dir->name, "set_prolog_flag")) {
        if (dir->args[0]->kind == GSLT_PL_ATOM && gslt_str_eq_cstr(dir->args[0]->name, "double_quotes")) {
          if (dir->args[1]->kind == GSLT_PL_ATOM && gslt_str_eq_cstr(dir->args[1]->name, "atom")) {
            continue;
          }
          snprintf(err, err_cap, "C0 reads double-quoted text as atoms; other double_quotes modes need value kinds C0 does not have");
          return false;
        }
        snprintf(err, err_cap, "unsupported C0 source flag");
        return false;
      }
      snprintf(err, err_cap, "unsupported C0 source directive");
      return false;
    }
    /* 2. Query ?- ... */
    if (sent->kind == GSLT_PL_COMPOUND && sent->nargs == 1 && gslt_str_eq_cstr(sent->name, "?-")) {
      if (allow_c1) {
        uint32_t fresh_next = 0;
        GsltPlTerm *qsrc = gslt_c0_number_fresh(a, sent->args[0], &fresh_next);
        GsltC0VarAlloc qalloc = gslt_c0_allocate_vars(a, qsrc);
        uint32_t ccap = 8, ccount = 0;
        const GsltPlTerm **conj = (const GsltPlTerm **)gslt_arena_alloc(a, ccap * sizeof(const GsltPlTerm *));
        gslt_c0_flatten_conjunction(a, qsrc, &conj, &ccount, &ccap);
        for (uint32_t i = 0; i < ccount; i++) {
          if (conj[i]->kind == GSLT_PL_ATOM && gslt_str_eq_cstr(conj[i]->name, "true")) continue;
          GsltC0Goal qg;
          if (!gslt_c0_lower_goal_ex(a, &qalloc, conj[i], true, &qg, err, err_cap)) {
            return false;
          }
          if (out_prog->nquery_goals >= qgcap) {
            uint32_t ncap = qgcap * 2;
            GsltC0Goal *nqg = (GsltC0Goal *)gslt_arena_alloc(a, ncap * sizeof(GsltC0Goal));
            memcpy(nqg, out_prog->query_goals, out_prog->nquery_goals * sizeof(GsltC0Goal));
            out_prog->query_goals = nqg;
            qgcap = ncap;
          }
          out_prog->query_goals[out_prog->nquery_goals++] = qg;
        }
        continue;
      }
      uint32_t ccap = 8, ccount = 0;
      const GsltPlTerm **conj = (const GsltPlTerm **)gslt_arena_alloc(a, ccap * sizeof(const GsltPlTerm *));
      gslt_c0_flatten_conjunction(a, sent->args[0], &conj, &ccount, &ccap);
      GsltC0VarAlloc empty_alloc = { 0, NULL };
      for (uint32_t i = 0; i < ccount; i++) {
        if (conj[i]->kind == GSLT_PL_ATOM && gslt_str_eq_cstr(conj[i]->name, "true")) continue;
        GsltC0Head qh;
        char qerr[256] = {0};
        if (!gslt_c0_lower_head(a, &empty_alloc, conj[i], &qh, qerr, sizeof(qerr))) {
          snprintf(err, err_cap, "initial C0 queries must be ground");
          return false;
        }
        /* Ensure every argument is a ground value (folding nested Term.tuple -> Value.tuple) */
        for (uint32_t j = 0; j < qh.arity; j++) {
          GsltC0Value *gv = gslt_c0_ground_term_to_val(a, qh.args[j]);
          if (!gv) {
            snprintf(err, err_cap, "initial C0 queries must be ground");
            return false;
          }
          qh.args[j]->kind = GSLT_C0_TERM_VAL;
          qh.args[j]->val = gv;
        }
        if (out_prog->ninputs >= icap) {
          uint32_t ncap = icap * 2;
          GsltC0Head *ninputs = (GsltC0Head *)gslt_arena_alloc(a, ncap * sizeof(GsltC0Head));
          memcpy(ninputs, out_prog->inputs, out_prog->ninputs * sizeof(GsltC0Head));
          out_prog->inputs = ninputs;
          icap = ncap;
        }
        out_prog->inputs[out_prog->ninputs++] = qh;
      }
      continue;
    }
    /* 3. CHR Rule */
    if (out_prog->nrules >= rcap) {
      uint32_t ncap = rcap * 2;
      GsltC0Rule *nrules = (GsltC0Rule *)gslt_arena_alloc(a, ncap * sizeof(GsltC0Rule));
      memcpy(nrules, out_prog->rules, out_prog->nrules * sizeof(GsltC0Rule));
      out_prog->rules = nrules;
      rcap = ncap;
    }
    if (!gslt_c0_lower_rule_ex(a, s, sent, allow_c1, &out_prog->rules[out_prog->nrules], err, err_cap)) {
      return false;
    }
    out_prog->nrules++;
  }

  /* Verify all initial query constraints are declared (c0:assemble in lowering.metta) */
  for (uint32_t i = 0; i < out_prog->ninputs; i++) {
    if (!gslt_c0_is_declared(out_prog->decls, out_prog->ndecls,
                             out_prog->inputs[i].name, out_prog->inputs[i].arity)) {
      if (out_diag) {
        out_diag->kind = GSLT_C0_DIAG_UNDECLARED_QUERY;
        out_diag->head = out_prog->inputs[i];
      }
      snprintf(err, err_cap, "initial C0 constraint has no matching name/arity declaration");
      return false;
    }
  }
  for (uint32_t i = 0; i < out_prog->nquery_goals; i++) {
    if (out_prog->query_goals[i].kind == GSLT_C0_GOAL_TELL) {
      if (!gslt_c0_is_declared(out_prog->decls, out_prog->ndecls,
                               out_prog->query_goals[i].tell_head.name,
                               out_prog->query_goals[i].tell_head.arity)) {
        if (out_diag) {
          out_diag->kind = GSLT_C0_DIAG_UNDECLARED_QUERY;
          out_diag->head = out_prog->query_goals[i].tell_head;
        }
        snprintf(err, err_cap, "initial C1 constraint has no matching name/arity declaration");
        return false;
      }
    }
  }

  /* Run Admission.diagnose */
  GsltC0Diagnostic diag;
  if (!gslt_c0_diagnose_ex(out_prog->decls, out_prog->ndecls, out_prog->rules, out_prog->nrules, allow_c1, &diag)) {
    if (out_diag) *out_diag = diag;
    snprintf(err, err_cap, "C0 admission refused: %s (rule %u)",
             gslt_c0_diag_name(diag.kind), diag.rule_index);
    return false;
  }
  return true;
}

static inline bool gslt_c0_lower_sentences(GsltArena *a, GsltPlTerm **sentences, uint32_t nsentences,
                                           GsltC0Program *out_prog, GsltC0Diagnostic *out_diag,
                                           char *err, size_t err_cap) {
  return gslt_c0_lower_sentences_ex(a, sentences, nsentences, false, out_prog, out_diag, err, err_cap);
}

static inline bool gslt_c0_parse_source(GsltArena *a, const char *src, size_t len,
                                        GsltC0Program *out_prog, GsltC0Diagnostic *out_diag,
                                        char *err, size_t err_cap) {
  GsltPlTerm **sentences = NULL;
  uint32_t nsentences = 0;
  if (!gslt_c0_source_to_sentences(a, src, len, &sentences, &nsentences, err, err_cap)) {
    return false;
  }
  return gslt_c0_lower_sentences_ex(a, sentences, nsentences, false, out_prog, out_diag, err, err_cap);
}

static inline bool gslt_c1_parse_source(GsltArena *a, const char *src, size_t len,
                                        GsltC0Program *out_prog, GsltC0Diagnostic *out_diag,
                                        char *err, size_t err_cap) {
  GsltPlTerm **sentences = NULL;
  uint32_t nsentences = 0;
  if (!gslt_c0_source_to_sentences(a, src, len, &sentences, &nsentences, err, err_cap)) {
    return false;
  }
  return gslt_c0_lower_sentences_ex(a, sentences, nsentences, true, out_prog, out_diag, err, err_cap);
}

static inline bool gslt_c1_set_query_string(GsltArena *a, GsltC0Program *prog,
                                            const char *qstr, GsltC0Diagnostic *out_diag,
                                            char *err, size_t err_cap) {
  if (!prog || !qstr) return false;
  const char *p = qstr;
  while (*p && isspace((unsigned char)*p)) p++;
  size_t plen = strlen(p);
  while (plen > 0 && isspace((unsigned char)p[plen - 1])) plen--;
  bool has_prefix = (plen >= 2 && strncmp(p, "?-", 2) == 0);
  bool has_dot = (plen > 0 && p[plen - 1] == '.');
  size_t cap = plen + 16;
  char *qbuf = (char *)gslt_arena_alloc(a, cap);
  int n = snprintf(qbuf, cap, "%s%.*s%s", has_prefix ? "" : "?- ", (int)plen, p, has_dot ? "" : ".");
  size_t qlen = (n > 0) ? (size_t)n : 0;

  GsltPlTerm **sentences = NULL;
  uint32_t nsentences = 0;
  if (!gslt_c0_source_to_sentences(a, qbuf, qlen, &sentences, &nsentences, err, err_cap) || nsentences != 1) {
    return false;
  }
  const GsltPlTerm *sent = sentences[0];
  if (sent->kind != GSLT_PL_COMPOUND || sent->nargs != 1 || !gslt_str_eq_cstr(sent->name, "?-")) {
    snprintf(err, err_cap, "expected a C1 query sentence");
    return false;
  }
  prog->is_c1 = true;
  prog->ninputs = 0;
  prog->nquery_goals = 0;
  uint32_t qgcap = 16;
  prog->query_goals = (GsltC0Goal *)gslt_arena_alloc(a, qgcap * sizeof(GsltC0Goal));
  uint32_t fresh_next = 0;
  GsltPlTerm *qsrc = gslt_c0_number_fresh(a, sent->args[0], &fresh_next);
  GsltC0VarAlloc qalloc = gslt_c0_allocate_vars(a, qsrc);
  uint32_t ccap = 8, ccount = 0;
  const GsltPlTerm **conj = (const GsltPlTerm **)gslt_arena_alloc(a, ccap * sizeof(const GsltPlTerm *));
  gslt_c0_flatten_conjunction(a, qsrc, &conj, &ccount, &ccap);
  for (uint32_t i = 0; i < ccount; i++) {
    if (conj[i]->kind == GSLT_PL_ATOM && gslt_str_eq_cstr(conj[i]->name, "true")) continue;
    GsltC0Goal qg;
    if (!gslt_c0_lower_goal_ex(a, &qalloc, conj[i], true, &qg, err, err_cap)) return false;
    if (qg.kind == GSLT_C0_GOAL_TELL &&
        !gslt_c0_is_declared(prog->decls, prog->ndecls, qg.tell_head.name, qg.tell_head.arity)) {
      if (out_diag) {
        out_diag->kind = GSLT_C0_DIAG_UNDECLARED_QUERY;
        out_diag->head = qg.tell_head;
      }
      snprintf(err, err_cap, "initial C1 constraint has no matching name/arity declaration");
      return false;
    }
    if (prog->nquery_goals >= qgcap) {
      uint32_t ncap = qgcap * 2;
      GsltC0Goal *nqg = (GsltC0Goal *)gslt_arena_alloc(a, ncap * sizeof(GsltC0Goal));
      memcpy(nqg, prog->query_goals, prog->nquery_goals * sizeof(GsltC0Goal));
      prog->query_goals = nqg;
      qgcap = ncap;
    }
    prog->query_goals[prog->nquery_goals++] = qg;
  }
  return true;
}

static inline bool gslt_c0_lower_packet(GsltArena *a, const GsltSexpr *pkt,
                                        GsltC0Program *out_prog, GsltC0Diagnostic *out_diag,
                                        GsltPacketProvenance *out_prov,
                                        char *err, size_t err_cap) {
  const GsltSexpr *tree = gslt_packet_unwrap_result(pkt);
  if (!tree && gslt_packet_node_label_eq(pkt, "chr:program")) tree = pkt;
  if (!tree) {
    snprintf(err, err_cap, "expected an explicitly selected whole-input parser result");
    return false;
  }
  if (out_prov) {
    if (!gslt_packet_inspect(a, tree, 0, out_prov)) {
      snprintf(err, err_cap, "malformed SyntaxGSLT packet spine or invalid codepoint leaf");
      return false;
    }
  }
  GsltPlTerm **sentences = NULL;
  uint32_t nsentences = 0;
  if (!gslt_c0_packet_to_sentences(a, pkt, &sentences, &nsentences, err, err_cap)) {
    return false;
  }
  return gslt_c0_lower_sentences(a, sentences, nsentences, out_prog, out_diag, err, err_cap);
}

/* Read a (SourceValuesV1 (result ...) ...) catalogue for C0.
 * Enforces that the catalogue is non-empty and that ALL packets lower cleanly
 * to the exact same GsltC0Program IR, while retaining provenance for each packet. */
static inline bool gslt_c0_read_catalogue(GsltArena *a, const char *cat_text, size_t cat_len,
                                          GsltC0Program *out_prog, GsltC0Diagnostic *out_diag,
                                          GsltPacketProvenance **out_provs, uint32_t *out_nprovs,
                                          char *err, size_t err_cap) {
  GsltSexpr *root = gslt_sexpr_parse_all(a, cat_text, cat_len, err, err_cap);
  if (!root) return false;
  /* Also allow a single (result (node chr:program ...) nil) packet directly */
  if (gslt_packet_unwrap_result(root) != NULL || gslt_packet_node_label_eq(root, "chr:program")) {
    GsltPacketProvenance *prov = (GsltPacketProvenance *)gslt_arena_alloc(a, sizeof(GsltPacketProvenance));
    if (!gslt_c0_lower_packet(a, root, out_prog, out_diag, prov, err, err_cap)) return false;
    if (out_provs) *out_provs = prov;
    if (out_nprovs) *out_nprovs = 1;
    return true;
  }
  if (root->kind != GSLT_SEXPR_LIST || root->nitems == 0 ||
      root->items[0]->kind != GSLT_SEXPR_SYM ||
      !gslt_str_eq_cstr(root->items[0]->text, "SourceValuesV1")) {
    snprintf(err, err_cap, "expected the selected whole-input source catalogue");
    return false;
  }
  if (root->nitems == 1) {
    snprintf(err, err_cap, "no selected source interpretation");
    return false;
  }
  uint32_t npkts = root->nitems - 1;
  GsltPacketProvenance *provs = (GsltPacketProvenance *)gslt_arena_alloc(a, npkts * sizeof(GsltPacketProvenance));
  GsltC0Program first_prog;
  memset(&first_prog, 0, sizeof(first_prog));
  for (uint32_t i = 0; i < npkts; i++) {
    GsltC0Program cur_prog;
    if (!gslt_c0_lower_packet(a, root->items[i + 1], &cur_prog, out_diag, &provs[i], err, err_cap)) {
      return false;
    }
    provs[i].packet_index = i;
    if (i == 0) {
      first_prog = cur_prog;
    } else if (!gslt_c0_program_eq(&first_prog, &cur_prog)) {
      snprintf(err, err_cap, "CHR source alternatives have different IR interpretations");
      return false;
    }
  }
  *out_prog = first_prog;
  if (out_provs) *out_provs = provs;
  if (out_nprovs) *out_nprovs = npkts;
  return true;
}

/* ---- Canonical C0 Printers (CHRPrologPrinter.lean & CeTTa / Lean IR Codecs) ---- */
typedef struct {
  char  *buf;
  size_t len;
  size_t cap;
} GsltStrBuf;

static inline bool gslt_sb_init(GsltArena *a, GsltStrBuf *sb, size_t init_cap) {
  sb->cap = (init_cap < 256) ? 256 : init_cap;
  sb->len = 0;
  sb->buf = (char *)gslt_arena_alloc(a, sb->cap);
  if (!sb->buf) return false;
  sb->buf[0] = '\0';
  return true;
}

static inline bool gslt_sb_ensure(GsltArena *a, GsltStrBuf *sb, size_t extra) {
  if (sb->len + extra + 1 <= sb->cap) return true;
  size_t ncap = sb->cap * 2;
  while (sb->len + extra + 1 > ncap) ncap *= 2;
  char *nbuf = (char *)gslt_arena_alloc(a, ncap);
  if (!nbuf) return false;
  memcpy(nbuf, sb->buf, sb->len + 1);
  sb->buf = nbuf;
  sb->cap = ncap;
  return true;
}

static inline bool gslt_sb_append_bytes(GsltArena *a, GsltStrBuf *sb, const char *s, size_t n) {
  if (!gslt_sb_ensure(a, sb, n)) return false;
  if (n > 0) memcpy(sb->buf + sb->len, s, n);
  sb->len += n;
  sb->buf[sb->len] = '\0';
  return true;
}

static inline bool gslt_sb_append_cstr(GsltArena *a, GsltStrBuf *sb, const char *s) {
  return gslt_sb_append_bytes(a, sb, s, strlen(s));
}

static inline bool gslt_sb_append_u32(GsltArena *a, GsltStrBuf *sb, uint32_t v) {
  char tmp[32];
  int n = snprintf(tmp, sizeof(tmp), "%u", v);
  return gslt_sb_append_bytes(a, sb, tmp, (size_t)n);
}

static inline bool gslt_sb_append_bigint(GsltArena *a, GsltStrBuf *sb, const C0BigInt *v) {
  char tmp[512];
  if (!c0_bigint_format_dec(v, tmp, sizeof(tmp))) return false;
  return gslt_sb_append_cstr(a, sb, tmp);
}

/* CHRPrologPrinter.atom: single-quoted with '', \\, \n, \r, \t, \a, \b, \v, \f */
static inline void gslt_c0_print_prolog_atom(GsltArena *a, GsltStrBuf *sb, GsltByteStr text) {
  gslt_sb_append_cstr(a, sb, "'");
  for (uint32_t i = 0; i < text.len; i++) {
    unsigned char c = (unsigned char)text.bytes[i];
    switch (c) {
      case '\'': gslt_sb_append_cstr(a, sb, "''"); break;
      case '\\': gslt_sb_append_cstr(a, sb, "\\\\"); break;
      case '\n': gslt_sb_append_cstr(a, sb, "\\n"); break;
      case '\r': gslt_sb_append_cstr(a, sb, "\\r"); break;
      case '\t': gslt_sb_append_cstr(a, sb, "\\t"); break;
      case 0x07: gslt_sb_append_cstr(a, sb, "\\a"); break;
      case 0x08: gslt_sb_append_cstr(a, sb, "\\b"); break;
      case 0x0b: gslt_sb_append_cstr(a, sb, "\\v"); break;
      case 0x0c: gslt_sb_append_cstr(a, sb, "\\f"); break;
      case 0x00: gslt_sb_append_cstr(a, sb, "\\0\\"); break;
      default:   gslt_sb_append_bytes(a, sb, (const char *)&c, 1); break;
    }
  }
  gslt_sb_append_cstr(a, sb, "'");
}

static inline void gslt_c0_print_prolog_val(GsltArena *a, GsltStrBuf *sb, const GsltC0Value *v) {
  if (v->kind == GSLT_C0_VAL_INT) {
    gslt_sb_append_bigint(a, sb, &v->ival);
  } else if (v->kind == GSLT_C0_VAL_ATOM) {
    gslt_c0_print_prolog_atom(a, sb, v->atom);
  } else if (v->kind == GSLT_C0_VAL_VAR) {
    gslt_sb_append_cstr(a, sb, "R");
    gslt_sb_append_u32(a, sb, v->var_id);
  } else if (v->kind == GSLT_C0_VAL_COMPOUND) {
    gslt_c0_print_prolog_atom(a, sb, v->atom);
    gslt_sb_append_cstr(a, sb, "(");
    for (uint32_t i = 0; i < v->nfields; i++) {
      if (i > 0) gslt_sb_append_cstr(a, sb, ", ");
      gslt_c0_print_prolog_val(a, sb, v->fields[i]);
    }
    gslt_sb_append_cstr(a, sb, ")");
  } else {
    gslt_sb_append_cstr(a, sb, "tuple(");
    for (uint32_t i = 0; i < v->nfields; i++) {
      if (i > 0) gslt_sb_append_cstr(a, sb, ", ");
      gslt_c0_print_prolog_val(a, sb, v->fields[i]);
    }
    gslt_sb_append_cstr(a, sb, ")");
  }
}

static inline void gslt_c0_print_prolog_term(GsltArena *a, GsltStrBuf *sb, const GsltC0Term *t) {
  if (t->kind == GSLT_C0_TERM_VAL) {
    gslt_c0_print_prolog_val(a, sb, t->val);
  } else if (t->kind == GSLT_C0_TERM_VAR) {
    gslt_sb_append_cstr(a, sb, "V");
    gslt_sb_append_u32(a, sb, t->var_idx);
  } else if (t->kind == GSLT_C0_TERM_COMPOUND) {
    gslt_c0_print_prolog_atom(a, sb, t->functor);
    gslt_sb_append_cstr(a, sb, "(");
    for (uint32_t i = 0; i < t->nfields; i++) {
      if (i > 0) gslt_sb_append_cstr(a, sb, ", ");
      gslt_c0_print_prolog_term(a, sb, t->fields[i]);
    }
    gslt_sb_append_cstr(a, sb, ")");
  } else {
    gslt_sb_append_cstr(a, sb, "tuple(");
    for (uint32_t i = 0; i < t->nfields; i++) {
      if (i > 0) gslt_sb_append_cstr(a, sb, ", ");
      gslt_c0_print_prolog_term(a, sb, t->fields[i]);
    }
    gslt_sb_append_cstr(a, sb, ")");
  }
}

static inline void gslt_c0_print_prolog_head(GsltArena *a, GsltStrBuf *sb, const GsltC0Head *h) {
  gslt_c0_print_prolog_atom(a, sb, h->name);
  if (h->arity > 0) {
    gslt_sb_append_cstr(a, sb, "(");
    for (uint32_t i = 0; i < h->arity; i++) {
      if (i > 0) gslt_sb_append_cstr(a, sb, ", ");
      gslt_c0_print_prolog_term(a, sb, h->args[i]);
    }
    gslt_sb_append_cstr(a, sb, ")");
  }
}

static inline void gslt_c0_print_prolog_expr(GsltArena *a, GsltStrBuf *sb, const GsltC0IntExpr *e) {
  if (e->kind == GSLT_C0_IEXPR_LIT) {
    gslt_sb_append_bigint(a, sb, &e->lit);
  } else if (e->kind == GSLT_C0_IEXPR_VAR) {
    gslt_sb_append_cstr(a, sb, "V");
    gslt_sb_append_u32(a, sb, e->var_idx);
  } else {
    const char *op_str = "+";
    switch (e->op) {
      case GSLT_C0_IOP_ADD:  op_str = "+";   break;
      case GSLT_C0_IOP_SUB:  op_str = "-";   break;
      case GSLT_C0_IOP_MUL:  op_str = "*";   break;
      case GSLT_C0_IOP_QUOT: op_str = "//";  break;
      case GSLT_C0_IOP_REM:  op_str = "rem"; break;
      case GSLT_C0_IOP_MOD:  op_str = "mod"; break;
    }
    gslt_sb_append_cstr(a, sb, "(");
    gslt_c0_print_prolog_expr(a, sb, e->left);
    gslt_sb_append_cstr(a, sb, " ");
    gslt_sb_append_cstr(a, sb, op_str);
    gslt_sb_append_cstr(a, sb, " ");
    gslt_c0_print_prolog_expr(a, sb, e->right);
    gslt_sb_append_cstr(a, sb, ")");
  }
}

static inline void gslt_c0_print_prolog_guard(GsltArena *a, GsltStrBuf *sb, const GsltC0Guard *g) {
  if (g->kind == GSLT_C0_GUARD_IDENTICAL || g->kind == GSLT_C0_GUARD_DISTINCT) {
    gslt_c0_print_prolog_term(a, sb, g->t_left);
    gslt_sb_append_cstr(a, sb, (g->kind == GSLT_C0_GUARD_IDENTICAL) ? " == " : " \\== ");
    gslt_c0_print_prolog_term(a, sb, g->t_right);
  } else {
    const char *cmp_str = "=:=";
    switch (g->cmp) {
      case GSLT_C0_CMP_EQ: cmp_str = "=:="; break;
      case GSLT_C0_CMP_NE: cmp_str = "=\\="; break;
      case GSLT_C0_CMP_LT: cmp_str = "<";   break;
      case GSLT_C0_CMP_LE: cmp_str = "=<";  break;
      case GSLT_C0_CMP_GT: cmp_str = ">";   break;
      case GSLT_C0_CMP_GE: cmp_str = ">=";  break;
    }
    gslt_c0_print_prolog_expr(a, sb, g->e_left);
    gslt_sb_append_cstr(a, sb, " ");
    gslt_sb_append_cstr(a, sb, cmp_str);
    gslt_sb_append_cstr(a, sb, " ");
    gslt_c0_print_prolog_expr(a, sb, g->e_right);
  }
}

static inline void gslt_c0_print_prolog_goal(GsltArena *a, GsltStrBuf *sb, const GsltC0Goal *g) {
  if (g->kind == GSLT_C0_GOAL_TELL) {
    gslt_c0_print_prolog_head(a, sb, &g->tell_head);
  } else if (g->kind == GSLT_C0_GOAL_ASSIGN) {
    gslt_sb_append_cstr(a, sb, "V");
    gslt_sb_append_u32(a, sb, g->assign_var);
    gslt_sb_append_cstr(a, sb, " is ");
    gslt_c0_print_prolog_expr(a, sb, g->assign_expr);
  } else if (g->kind == GSLT_C0_GOAL_UNIFY) {
    gslt_c0_print_prolog_term(a, sb, g->unify_left);
    gslt_sb_append_cstr(a, sb, " = ");
    gslt_c0_print_prolog_term(a, sb, g->unify_right);
  } else if (g->kind == GSLT_C0_GOAL_UNIFY_OC) {
    gslt_sb_append_cstr(a, sb, "unify_with_occurs_check(");
    gslt_c0_print_prolog_term(a, sb, g->unify_left);
    gslt_sb_append_cstr(a, sb, ", ");
    gslt_c0_print_prolog_term(a, sb, g->unify_right);
    gslt_sb_append_cstr(a, sb, ")");
  } else if (g->kind == GSLT_C0_GOAL_GUARD) {
    gslt_c0_print_prolog_guard(a, sb, &g->guard_test);
  } else {
    gslt_sb_append_cstr(a, sb, "fail");
  }
}

/* Exact match to CHRPrologPrinter.program in CHRPrologPrinter.lean */
static inline GsltByteStr gslt_c0_emit_prolog_source(GsltArena *a, const GsltC0Program *prog) {
  GsltStrBuf sb;
  gslt_sb_init(a, &sb, 1024);
  gslt_sb_append_cstr(a, &sb, ":- use_module(library(chr)).\n");
  if (prog->ndecls > 0) {
    gslt_sb_append_cstr(a, &sb, ":- chr_constraint ");
    for (uint32_t i = 0; i < prog->ndecls; i++) {
      if (i > 0) gslt_sb_append_cstr(a, &sb, ", ");
      gslt_c0_print_prolog_atom(a, &sb, prog->decls[i].name);
      gslt_sb_append_cstr(a, &sb, "/");
      gslt_sb_append_u32(a, &sb, prog->decls[i].arity);
    }
    gslt_sb_append_cstr(a, &sb, ".\n:- chr_option(optimize,off).\n");
  }
  for (uint32_t r = 0; r < prog->nrules; r++) {
    const GsltC0Rule *rule = &prog->rules[r];
    gslt_c0_print_prolog_atom(a, &sb, rule->name);
    gslt_sb_append_cstr(a, &sb, " @ ");
    if (rule->nremoved == 0) {
      if (rule->nkept == 0) gslt_sb_append_cstr(a, &sb, "true");
      for (uint32_t i = 0; i < rule->nkept; i++) {
        if (i > 0) gslt_sb_append_cstr(a, &sb, ", ");
        gslt_c0_print_prolog_head(a, &sb, &rule->kept[i]);
      }
      gslt_sb_append_cstr(a, &sb, " ==> ");
    } else if (rule->nkept == 0) {
      for (uint32_t i = 0; i < rule->nremoved; i++) {
        if (i > 0) gslt_sb_append_cstr(a, &sb, ", ");
        gslt_c0_print_prolog_head(a, &sb, &rule->removed[i]);
      }
      gslt_sb_append_cstr(a, &sb, " <=> ");
    } else {
      for (uint32_t i = 0; i < rule->nkept; i++) {
        if (i > 0) gslt_sb_append_cstr(a, &sb, ", ");
        gslt_c0_print_prolog_head(a, &sb, &rule->kept[i]);
      }
      gslt_sb_append_cstr(a, &sb, " \\ ");
      for (uint32_t i = 0; i < rule->nremoved; i++) {
        if (i > 0) gslt_sb_append_cstr(a, &sb, ", ");
        gslt_c0_print_prolog_head(a, &sb, &rule->removed[i]);
      }
      gslt_sb_append_cstr(a, &sb, " <=> ");
    }
    if (rule->nguards > 0) {
      for (uint32_t i = 0; i < rule->nguards; i++) {
        if (i > 0) gslt_sb_append_cstr(a, &sb, ", ");
        gslt_c0_print_prolog_guard(a, &sb, &rule->guards[i]);
      }
      gslt_sb_append_cstr(a, &sb, " | ");
    }
    if (rule->nbody == 0) {
      gslt_sb_append_cstr(a, &sb, "true");
    } else {
      for (uint32_t i = 0; i < rule->nbody; i++) {
        if (i > 0) gslt_sb_append_cstr(a, &sb, ", ");
        gslt_c0_print_prolog_goal(a, &sb, &rule->body[i]);
      }
    }
    gslt_sb_append_cstr(a, &sb, ".\n");
  }
  if (prog->ninputs > 0) {
    gslt_sb_append_cstr(a, &sb, "?- ");
    for (uint32_t i = 0; i < prog->ninputs; i++) {
      if (i > 0) gslt_sb_append_cstr(a, &sb, ", ");
      gslt_c0_print_prolog_head(a, &sb, &prog->inputs[i]);
    }
    gslt_sb_append_cstr(a, &sb, ".\n");
  }
  if (prog->nquery_goals > 0) {
    gslt_sb_append_cstr(a, &sb, "?- ");
    for (uint32_t i = 0; i < prog->nquery_goals; i++) {
      if (i > 0) gslt_sb_append_cstr(a, &sb, ", ");
      gslt_c0_print_prolog_goal(a, &sb, &prog->query_goals[i]);
    }
    gslt_sb_append_cstr(a, &sb, ".\n");
  }
  GsltByteStr out = { sb.buf, (uint32_t)sb.len };
  return out;
}

/* ---- C0 IR Codec (CeTTa lowering.metta (C0Program ...) & Lean CHRProgramCodec.lean) ---- */
static inline void gslt_sb_append_quoted_str(GsltArena *a, GsltStrBuf *sb, GsltByteStr s) {
  gslt_sb_append_cstr(a, sb, "\"");
  for (uint32_t i = 0; i < s.len; i++) {
    unsigned char c = (unsigned char)s.bytes[i];
    switch (c) {
      case '"':  gslt_sb_append_cstr(a, sb, "\\\""); break;
      case '\\': gslt_sb_append_cstr(a, sb, "\\\\"); break;
      case '\n': gslt_sb_append_cstr(a, sb, "\\n");  break;
      case '\r': gslt_sb_append_cstr(a, sb, "\\r");  break;
      case '\t': gslt_sb_append_cstr(a, sb, "\\t");  break;
      case 0x07: gslt_sb_append_cstr(a, sb, "\\a");  break;
      case 0x08: gslt_sb_append_cstr(a, sb, "\\b");  break;
      case 0x0b: gslt_sb_append_cstr(a, sb, "\\v");  break;
      case 0x0c: gslt_sb_append_cstr(a, sb, "\\f");  break;
      case 0x00: gslt_sb_append_cstr(a, sb, "\\0");  break;
      default:   gslt_sb_append_bytes(a, sb, (const char *)&c, 1); break;
    }
  }
  gslt_sb_append_cstr(a, sb, "\"");
}

static inline void gslt_c0_emit_ir_val(GsltArena *a, GsltStrBuf *sb, const GsltC0Value *v) {
  if (v->kind == GSLT_C0_VAL_INT) {
    gslt_sb_append_bigint(a, sb, &v->ival);
  } else if (v->kind == GSLT_C0_VAL_ATOM) {
    gslt_sb_append_quoted_str(a, sb, v->atom);
  } else if (v->kind == GSLT_C0_VAL_VAR) {
    gslt_sb_append_cstr(a, sb, "(ChrRVar ");
    gslt_sb_append_u32(a, sb, v->var_id);
    gslt_sb_append_cstr(a, sb, ")");
  } else if (v->kind == GSLT_C0_VAL_COMPOUND) {
    gslt_sb_append_cstr(a, sb, "(ChrCompound ");
    gslt_sb_append_quoted_str(a, sb, v->atom);
    gslt_sb_append_cstr(a, sb, " ");
    for (uint32_t i = 0; i < v->nfields; i++) {
      gslt_sb_append_cstr(a, sb, "(ChrCons ");
      gslt_c0_emit_ir_val(a, sb, v->fields[i]);
      gslt_sb_append_cstr(a, sb, " ");
    }
    gslt_sb_append_cstr(a, sb, "ChrNil");
    for (uint32_t i = 0; i < v->nfields; i++) gslt_sb_append_cstr(a, sb, ")");
    gslt_sb_append_cstr(a, sb, ")");
  } else {
    gslt_sb_append_cstr(a, sb, "(ChrTuple ");
    for (uint32_t i = 0; i < v->nfields; i++) {
      gslt_sb_append_cstr(a, sb, "(ChrCons ");
      gslt_c0_emit_ir_val(a, sb, v->fields[i]);
      gslt_sb_append_cstr(a, sb, " ");
    }
    gslt_sb_append_cstr(a, sb, "ChrNil");
    for (uint32_t i = 0; i < v->nfields; i++) gslt_sb_append_cstr(a, sb, ")");
    gslt_sb_append_cstr(a, sb, ")");
  }
}

static inline void gslt_c0_emit_ir_term(GsltArena *a, GsltStrBuf *sb, const GsltC0Term *t) {
  if (t->kind == GSLT_C0_TERM_VAL) {
    if (t->val->kind == GSLT_C0_VAL_TUPLE) {
      gslt_sb_append_cstr(a, sb, "(ChrTupleTerm ");
      for (uint32_t i = 0; i < t->val->nfields; i++) {
        GsltC0Term sub;
        memset(&sub, 0, sizeof(sub));
        sub.kind = GSLT_C0_TERM_VAL;
        sub.val = t->val->fields[i];
        gslt_sb_append_cstr(a, sb, "(ChrCons ");
        gslt_c0_emit_ir_term(a, sb, &sub);
        gslt_sb_append_cstr(a, sb, " ");
      }
      gslt_sb_append_cstr(a, sb, "ChrNil");
      for (uint32_t i = 0; i < t->val->nfields; i++) gslt_sb_append_cstr(a, sb, ")");
      gslt_sb_append_cstr(a, sb, ")");
    } else {
      gslt_sb_append_cstr(a, sb, "(ChrValue ");
      gslt_c0_emit_ir_val(a, sb, t->val);
      gslt_sb_append_cstr(a, sb, ")");
    }
  } else if (t->kind == GSLT_C0_TERM_VAR) {
    gslt_sb_append_cstr(a, sb, "(ChrVar ");
    gslt_sb_append_u32(a, sb, t->var_idx);
    gslt_sb_append_cstr(a, sb, ")");
  } else if (t->kind == GSLT_C0_TERM_COMPOUND) {
    gslt_sb_append_cstr(a, sb, "(ChrCompoundTerm ");
    gslt_sb_append_quoted_str(a, sb, t->functor);
    gslt_sb_append_cstr(a, sb, " ");
    for (uint32_t i = 0; i < t->nfields; i++) {
      gslt_sb_append_cstr(a, sb, "(ChrCons ");
      gslt_c0_emit_ir_term(a, sb, t->fields[i]);
      gslt_sb_append_cstr(a, sb, " ");
    }
    gslt_sb_append_cstr(a, sb, "ChrNil");
    for (uint32_t i = 0; i < t->nfields; i++) gslt_sb_append_cstr(a, sb, ")");
    gslt_sb_append_cstr(a, sb, ")");
  } else {
    gslt_sb_append_cstr(a, sb, "(ChrTupleTerm ");
    for (uint32_t i = 0; i < t->nfields; i++) {
      gslt_sb_append_cstr(a, sb, "(ChrCons ");
      gslt_c0_emit_ir_term(a, sb, t->fields[i]);
      gslt_sb_append_cstr(a, sb, " ");
    }
    gslt_sb_append_cstr(a, sb, "ChrNil");
    for (uint32_t i = 0; i < t->nfields; i++) gslt_sb_append_cstr(a, sb, ")");
    gslt_sb_append_cstr(a, sb, ")");
  }
}

static inline void gslt_c0_emit_ir_head(GsltArena *a, GsltStrBuf *sb, const GsltC0Head *h) {
  gslt_sb_append_cstr(a, sb, "(ChrHead ");
  gslt_sb_append_quoted_str(a, sb, h->name);
  gslt_sb_append_cstr(a, sb, " ");
  gslt_sb_append_u32(a, sb, h->arity);
  gslt_sb_append_cstr(a, sb, " ");
  for (uint32_t i = 0; i < h->arity; i++) {
    gslt_sb_append_cstr(a, sb, "(ChrCons ");
    gslt_c0_emit_ir_term(a, sb, h->args[i]);
    gslt_sb_append_cstr(a, sb, " ");
  }
  gslt_sb_append_cstr(a, sb, "ChrNil");
  for (uint32_t i = 0; i < h->arity; i++) gslt_sb_append_cstr(a, sb, ")");
  gslt_sb_append_cstr(a, sb, ")");
}

static inline void gslt_c0_emit_ir_expr(GsltArena *a, GsltStrBuf *sb, const GsltC0IntExpr *e) {
  if (e->kind == GSLT_C0_IEXPR_LIT) {
    gslt_sb_append_cstr(a, sb, "(ChrLiteral ");
    gslt_sb_append_bigint(a, sb, &e->lit);
    gslt_sb_append_cstr(a, sb, ")");
  } else if (e->kind == GSLT_C0_IEXPR_VAR) {
    gslt_sb_append_cstr(a, sb, "(ChrIndex ");
    gslt_sb_append_u32(a, sb, e->var_idx);
    gslt_sb_append_cstr(a, sb, ")");
  } else {
    const char *op_str = "ChrAdd";
    switch (e->op) {
      case GSLT_C0_IOP_ADD:  op_str = "ChrAdd";       break;
      case GSLT_C0_IOP_SUB:  op_str = "ChrSubtract";  break;
      case GSLT_C0_IOP_MUL:  op_str = "ChrMultiply";  break;
      case GSLT_C0_IOP_QUOT: op_str = "ChrQuotient";  break;
      case GSLT_C0_IOP_REM:  op_str = "ChrRemainder"; break;
      case GSLT_C0_IOP_MOD:  op_str = "ChrModulo";    break;
    }
    gslt_sb_append_cstr(a, sb, "(ChrOperation ");
    gslt_sb_append_cstr(a, sb, op_str);
    gslt_sb_append_cstr(a, sb, " ");
    gslt_c0_emit_ir_expr(a, sb, e->left);
    gslt_sb_append_cstr(a, sb, " ");
    gslt_c0_emit_ir_expr(a, sb, e->right);
    gslt_sb_append_cstr(a, sb, ")");
  }
}

static inline void gslt_c0_emit_ir_guard(GsltArena *a, GsltStrBuf *sb, const GsltC0Guard *g) {
  if (g->kind == GSLT_C0_GUARD_IDENTICAL || g->kind == GSLT_C0_GUARD_DISTINCT) {
    gslt_sb_append_cstr(a, sb, (g->kind == GSLT_C0_GUARD_IDENTICAL) ? "(ChrIdentical " : "(ChrDistinct ");
    gslt_c0_emit_ir_term(a, sb, g->t_left);
    gslt_sb_append_cstr(a, sb, " ");
    gslt_c0_emit_ir_term(a, sb, g->t_right);
    gslt_sb_append_cstr(a, sb, ")");
  } else {
    const char *cmp_str = "ChrEqual";
    switch (g->cmp) {
      case GSLT_C0_CMP_EQ: cmp_str = "ChrEqual";        break;
      case GSLT_C0_CMP_NE: cmp_str = "ChrDifferent";    break;
      case GSLT_C0_CMP_LT: cmp_str = "ChrLess";         break;
      case GSLT_C0_CMP_LE: cmp_str = "ChrLessEqual";    break;
      case GSLT_C0_CMP_GT: cmp_str = "ChrGreater";      break;
      case GSLT_C0_CMP_GE: cmp_str = "ChrGreaterEqual"; break;
    }
    gslt_sb_append_cstr(a, sb, "(ChrCompare ");
    gslt_sb_append_cstr(a, sb, cmp_str);
    gslt_sb_append_cstr(a, sb, " ");
    gslt_c0_emit_ir_expr(a, sb, g->e_left);
    gslt_sb_append_cstr(a, sb, " ");
    gslt_c0_emit_ir_expr(a, sb, g->e_right);
    gslt_sb_append_cstr(a, sb, ")");
  }
}

static inline void gslt_c0_emit_ir_goal(GsltArena *a, GsltStrBuf *sb, const GsltC0Goal *g) {
  if (g->kind == GSLT_C0_GOAL_TELL) {
    gslt_sb_append_cstr(a, sb, "(ChrTell ");
    gslt_c0_emit_ir_head(a, sb, &g->tell_head);
    gslt_sb_append_cstr(a, sb, ")");
  } else if (g->kind == GSLT_C0_GOAL_ASSIGN) {
    gslt_sb_append_cstr(a, sb, "(ChrAssign ");
    gslt_sb_append_u32(a, sb, g->assign_var);
    gslt_sb_append_cstr(a, sb, " ");
    gslt_c0_emit_ir_expr(a, sb, g->assign_expr);
    gslt_sb_append_cstr(a, sb, ")");
  } else if (g->kind == GSLT_C0_GOAL_UNIFY) {
    gslt_sb_append_cstr(a, sb, "(ChrUnify ");
    gslt_c0_emit_ir_term(a, sb, g->unify_left);
    gslt_sb_append_cstr(a, sb, " ");
    gslt_c0_emit_ir_term(a, sb, g->unify_right);
    gslt_sb_append_cstr(a, sb, ")");
  } else if (g->kind == GSLT_C0_GOAL_UNIFY_OC) {
    gslt_sb_append_cstr(a, sb, "(ChrUnifyOC ");
    gslt_c0_emit_ir_term(a, sb, g->unify_left);
    gslt_sb_append_cstr(a, sb, " ");
    gslt_c0_emit_ir_term(a, sb, g->unify_right);
    gslt_sb_append_cstr(a, sb, ")");
  } else if (g->kind == GSLT_C0_GOAL_GUARD) {
    gslt_sb_append_cstr(a, sb, "(ChrGuardGoal ");
    gslt_c0_emit_ir_guard(a, sb, &g->guard_test);
    gslt_sb_append_cstr(a, sb, ")");
  } else {
    gslt_sb_append_cstr(a, sb, "ChrFailGoal");
  }
}

static inline GsltByteStr gslt_c0_emit_ir(GsltArena *a, const GsltC0Program *prog) {
  GsltStrBuf sb;
  gslt_sb_init(a, &sb, 1024);
  gslt_sb_append_cstr(a, &sb, "(C0Program (");
  for (uint32_t i = 0; i < prog->ndecls; i++) {
    if (i > 0) gslt_sb_append_cstr(a, &sb, " ");
    gslt_sb_append_cstr(a, &sb, "(C0Declaration ");
    gslt_sb_append_quoted_str(a, &sb, prog->decls[i].name);
    gslt_sb_append_cstr(a, &sb, " ");
    gslt_sb_append_u32(a, &sb, prog->decls[i].arity);
    gslt_sb_append_cstr(a, &sb, ")");
  }
  gslt_sb_append_cstr(a, &sb, ") (");
  for (uint32_t r = 0; r < prog->nrules; r++) {
    if (r > 0) gslt_sb_append_cstr(a, &sb, " ");
    const GsltC0Rule *rule = &prog->rules[r];
    gslt_sb_append_cstr(a, &sb, "(C0Rule ");
    gslt_sb_append_quoted_str(a, &sb, rule->name);
    gslt_sb_append_cstr(a, &sb, " (");
    for (uint32_t i = 0; i < rule->nkept; i++) {
      if (i > 0) gslt_sb_append_cstr(a, &sb, " ");
      gslt_c0_emit_ir_head(a, &sb, &rule->kept[i]);
    }
    gslt_sb_append_cstr(a, &sb, ") (");
    for (uint32_t i = 0; i < rule->nremoved; i++) {
      if (i > 0) gslt_sb_append_cstr(a, &sb, " ");
      gslt_c0_emit_ir_head(a, &sb, &rule->removed[i]);
    }
    gslt_sb_append_cstr(a, &sb, ") (");
    for (uint32_t i = 0; i < rule->nguards; i++) {
      if (i > 0) gslt_sb_append_cstr(a, &sb, " ");
      gslt_c0_emit_ir_guard(a, &sb, &rule->guards[i]);
    }
    gslt_sb_append_cstr(a, &sb, ") (");
    for (uint32_t i = 0; i < rule->nbody; i++) {
      if (i > 0) gslt_sb_append_cstr(a, &sb, " ");
      gslt_c0_emit_ir_goal(a, &sb, &rule->body[i]);
    }
    gslt_sb_append_cstr(a, &sb, "))");
  }
  gslt_sb_append_cstr(a, &sb, ") (");
  for (uint32_t i = 0; i < prog->ninputs; i++) {
    if (i > 0) gslt_sb_append_cstr(a, &sb, " ");
    gslt_c0_emit_ir_head(a, &sb, &prog->inputs[i]);
  }
  gslt_sb_append_cstr(a, &sb, "))");
  GsltByteStr out = { sb.buf, (uint32_t)sb.len };
  return out;
}

/* Parse C0 IR: supports both CeTTa (C0Program ...) and Lean CHRProgramCodec (node "program" ...) */
static GsltC0Term *gslt_c0_parse_ir_term(GsltArena *a, const GsltSexpr *s, char *err, size_t err_cap);

static inline bool gslt_c0_parse_chr_list_terms(GsltArena *a, const GsltSexpr *s,
                                                GsltC0Term ***out_terms, uint32_t *out_count,
                                                char *err, size_t err_cap) {
  uint32_t cap = 8, count = 0;
  GsltC0Term **arr = (GsltC0Term **)gslt_arena_alloc(a, cap * sizeof(GsltC0Term *));
  const GsltSexpr *cur = s;
  /* Support both ChrCons/ChrNil spine (lowering.metta) and flat list [...] (CHRProgramCodec.lean) */
  if (s && s->kind == GSLT_SEXPR_LIST &&
      !(s->nitems == 3 && s->items[0]->kind == GSLT_SEXPR_SYM && gslt_str_eq_cstr(s->items[0]->text, "ChrCons"))) {
    arr = (GsltC0Term **)gslt_arena_alloc(a, (s->nitems + 1) * sizeof(GsltC0Term *));
    for (uint32_t i = 0; i < s->nitems; i++) {
      GsltC0Term *t = gslt_c0_parse_ir_term(a, s->items[i], err, err_cap);
      if (!t) return false;
      arr[i] = t;
    }
    *out_terms = arr;
    *out_count = s->nitems;
    return true;
  }
  while (cur) {
    if (cur->kind == GSLT_SEXPR_SYM && gslt_str_eq_cstr(cur->text, "ChrNil")) {
      *out_terms = arr;
      *out_count = count;
      return true;
    }
    if (cur->kind == GSLT_SEXPR_LIST && cur->nitems == 3 &&
        cur->items[0]->kind == GSLT_SEXPR_SYM && gslt_str_eq_cstr(cur->items[0]->text, "ChrCons")) {
      GsltC0Term *t = gslt_c0_parse_ir_term(a, cur->items[1], err, err_cap);
      if (!t) return false;
      if (count >= cap) {
        uint32_t ncap = cap * 2;
        GsltC0Term **narr = (GsltC0Term **)gslt_arena_alloc(a, ncap * sizeof(GsltC0Term *));
        memcpy(narr, arr, count * sizeof(GsltC0Term *));
        arr = narr;
        cap = ncap;
      }
      arr[count++] = t;
      cur = cur->items[2];
    } else {
      snprintf(err, err_cap, "expected ChrCons or ChrNil in C0 IR term list");
      return false;
    }
  }
  return false;
}

static inline GsltC0Value *gslt_c0_parse_ir_val(GsltArena *a, const GsltSexpr *s,
                                                char *err, size_t err_cap) {
  if (!s) return NULL;
  if (s->kind == GSLT_SEXPR_INT) {
    GsltC0Value *v = (GsltC0Value *)gslt_arena_alloc(a, sizeof(GsltC0Value));
    v->kind = GSLT_C0_VAL_INT;
    v->ival = s->int_val;
    return v;
  }
  if (s->kind == GSLT_SEXPR_STR || s->kind == GSLT_SEXPR_SYM) {
    GsltC0Value *v = (GsltC0Value *)gslt_arena_alloc(a, sizeof(GsltC0Value));
    v->kind = GSLT_C0_VAL_ATOM;
    v->atom = s->text;
    return v;
  }
  if (s->kind == GSLT_SEXPR_LIST && s->nitems == 2 && s->items[0]->kind == GSLT_SEXPR_SYM) {
    GsltByteStr tag = s->items[0]->text;
    if (gslt_str_eq_cstr(tag, "ChrInt") && s->items[1]->kind == GSLT_SEXPR_INT) {
      GsltC0Value *v = (GsltC0Value *)gslt_arena_alloc(a, sizeof(GsltC0Value));
      v->kind = GSLT_C0_VAL_INT;
      v->ival = s->items[1]->int_val;
      return v;
    }
    if (gslt_str_eq_cstr(tag, "ChrSymbol")) {
      GsltC0Value *v = (GsltC0Value *)gslt_arena_alloc(a, sizeof(GsltC0Value));
      v->kind = GSLT_C0_VAL_ATOM;
      v->atom = s->items[1]->text;
      return v;
    }
  }
  if (s->kind == GSLT_SEXPR_LIST && s->nitems == 2 &&
      s->items[0]->kind == GSLT_SEXPR_SYM && gslt_str_eq_cstr(s->items[0]->text, "ChrTuple")) {
    uint32_t cap = 8, count = 0;
    GsltC0Value **fields = (GsltC0Value **)gslt_arena_alloc(a, cap * sizeof(GsltC0Value *));
    const GsltSexpr *cur = s->items[1];
    if (cur->kind == GSLT_SEXPR_LIST &&
        !(cur->nitems == 3 && cur->items[0]->kind == GSLT_SEXPR_SYM && gslt_str_eq_cstr(cur->items[0]->text, "ChrCons"))) {
      fields = (GsltC0Value **)gslt_arena_alloc(a, (cur->nitems + 1) * sizeof(GsltC0Value *));
      for (uint32_t i = 0; i < cur->nitems; i++) {
        GsltC0Value *fv = gslt_c0_parse_ir_val(a, cur->items[i], err, err_cap);
        if (!fv) return NULL;
        fields[i] = fv;
      }
      count = cur->nitems;
    } else {
      while (cur) {
        if (cur->kind == GSLT_SEXPR_SYM && gslt_str_eq_cstr(cur->text, "ChrNil")) break;
        if (cur->kind == GSLT_SEXPR_LIST && cur->nitems == 3 &&
            cur->items[0]->kind == GSLT_SEXPR_SYM && gslt_str_eq_cstr(cur->items[0]->text, "ChrCons")) {
          GsltC0Value *fv = gslt_c0_parse_ir_val(a, cur->items[1], err, err_cap);
          if (!fv) return NULL;
          if (count >= cap) {
            uint32_t ncap = cap * 2;
            GsltC0Value **nf = (GsltC0Value **)gslt_arena_alloc(a, ncap * sizeof(GsltC0Value *));
            memcpy(nf, fields, count * sizeof(GsltC0Value *));
            fields = nf;
            cap = ncap;
          }
          fields[count++] = fv;
          cur = cur->items[2];
        } else {
          snprintf(err, err_cap, "invalid ChrTuple list in C0 IR");
          return NULL;
        }
      }
    }
    GsltC0Value *v = (GsltC0Value *)gslt_arena_alloc(a, sizeof(GsltC0Value));
    v->kind = GSLT_C0_VAL_TUPLE;
    v->nfields = count;
    v->fields = fields;
    return v;
  }
  snprintf(err, err_cap, "invalid C0 IR value");
  return NULL;
}

static GsltC0Term *gslt_c0_parse_ir_term(GsltArena *a, const GsltSexpr *s, char *err, size_t err_cap) {
  if (!s || s->kind != GSLT_SEXPR_LIST || s->nitems < 2 || s->items[0]->kind != GSLT_SEXPR_SYM) {
    snprintf(err, err_cap, "expected C0 IR term");
    return NULL;
  }
  GsltByteStr tag = s->items[0]->text;
  if ((gslt_str_eq_cstr(tag, "ChrValue") || gslt_str_eq_cstr(tag, "ChrLiteral")) && s->nitems == 2) {
    GsltC0Value *v = gslt_c0_parse_ir_val(a, s->items[1], err, err_cap);
    if (!v) return NULL;
    GsltC0Term *t = (GsltC0Term *)gslt_arena_alloc(a, sizeof(GsltC0Term));
    t->kind = GSLT_C0_TERM_VAL;
    t->val = v;
    return t;
  }
  if ((gslt_str_eq_cstr(tag, "ChrVar") || gslt_str_eq_cstr(tag, "ChrVariable")) &&
      s->nitems == 2 && s->items[1]->kind == GSLT_SEXPR_INT) {
    uint64_t idx = 0;
    if (!c0_bigint_to_u64(&s->items[1]->int_val, &idx)) return NULL;
    GsltC0Term *t = (GsltC0Term *)gslt_arena_alloc(a, sizeof(GsltC0Term));
    t->kind = GSLT_C0_TERM_VAR;
    t->var_idx = (uint32_t)idx;
    return t;
  }
  if ((gslt_str_eq_cstr(tag, "ChrTupleTerm") || gslt_str_eq_cstr(tag, "ChrTermTuple")) && s->nitems == 2) {
    GsltC0Term **fields = NULL;
    uint32_t nfields = 0;
    if (!gslt_c0_parse_chr_list_terms(a, s->items[1], &fields, &nfields, err, err_cap)) return NULL;
    GsltC0Term *t = (GsltC0Term *)gslt_arena_alloc(a, sizeof(GsltC0Term));
    t->kind = GSLT_C0_TERM_TUPLE;
    t->nfields = nfields;
    t->fields = fields;
    return t;
  }
  snprintf(err, err_cap, "unknown C0 IR term tag");
  return NULL;
}

static inline bool gslt_c0_parse_ir_head(GsltArena *a, const GsltSexpr *s, GsltC0Head *out,
                                         char *err, size_t err_cap) {
  memset(out, 0, sizeof(*out));
  if (!s || s->kind != GSLT_SEXPR_LIST || s->items[0]->kind != GSLT_SEXPR_SYM ||
      !gslt_str_eq_cstr(s->items[0]->text, "ChrHead")) {
    snprintf(err, err_cap, "expected (ChrHead ...)");
    return false;
  }
  if (s->nitems == 3) {
    /* Lean CHRProgramCodec: (ChrHead name [terms...]) */
    GsltC0Term **args = NULL;
    uint32_t nargs = 0;
    if (!gslt_c0_parse_chr_list_terms(a, s->items[2], &args, &nargs, err, err_cap)) return false;
    out->name = s->items[1]->text;
    out->arity = nargs;
    out->args = args;
    return true;
  }
  if (s->nitems != 4 || s->items[2]->kind != GSLT_SEXPR_INT) {
    snprintf(err, err_cap, "expected (ChrHead name arity terms)");
    return false;
  }
  uint64_t arity = 0;
  if (!c0_bigint_to_u64(&s->items[2]->int_val, &arity)) return false;
  GsltC0Term **args = NULL;
  uint32_t nargs = 0;
  if (!gslt_c0_parse_chr_list_terms(a, s->items[3], &args, &nargs, err, err_cap)) return false;
  if (nargs != (uint32_t)arity) {
    snprintf(err, err_cap, "ChrHead arity mismatch");
    return false;
  }
  out->name = s->items[1]->text;
  out->arity = nargs;
  out->args = args;
  return true;
}

static inline GsltC0IntExpr *gslt_c0_parse_ir_expr(GsltArena *a, const GsltSexpr *s,
                                                   char *err, size_t err_cap) {
  if (!s || s->kind != GSLT_SEXPR_LIST || s->nitems < 2 || s->items[0]->kind != GSLT_SEXPR_SYM) {
    snprintf(err, err_cap, "expected C0 IR expression");
    return NULL;
  }
  GsltByteStr tag = s->items[0]->text;
  if ((gslt_str_eq_cstr(tag, "ChrLiteral") || gslt_str_eq_cstr(tag, "ChrNumber")) &&
      s->nitems == 2 && s->items[1]->kind == GSLT_SEXPR_INT) {
    GsltC0IntExpr *e = (GsltC0IntExpr *)gslt_arena_alloc(a, sizeof(GsltC0IntExpr));
    e->kind = GSLT_C0_IEXPR_LIT;
    e->lit = s->items[1]->int_val;
    return e;
  }
  if ((gslt_str_eq_cstr(tag, "ChrIndex") || gslt_str_eq_cstr(tag, "ChrIntVariable")) &&
      s->nitems == 2 && s->items[1]->kind == GSLT_SEXPR_INT) {
    uint64_t idx = 0;
    if (!c0_bigint_to_u64(&s->items[1]->int_val, &idx)) return NULL;
    GsltC0IntExpr *e = (GsltC0IntExpr *)gslt_arena_alloc(a, sizeof(GsltC0IntExpr));
    e->kind = GSLT_C0_IEXPR_VAR;
    e->var_idx = (uint32_t)idx;
    return e;
  }
  if (s->nitems == 3 &&
      (gslt_str_eq_cstr(tag, "ChrAdd") || gslt_str_eq_cstr(tag, "ChrSubtract") ||
       gslt_str_eq_cstr(tag, "ChrMultiply") || gslt_str_eq_cstr(tag, "ChrQuotient") ||
       gslt_str_eq_cstr(tag, "ChrRemainder") || gslt_str_eq_cstr(tag, "ChrModulo"))) {
    GsltC0IntOp op = GSLT_C0_IOP_ADD;
    if (gslt_str_eq_cstr(tag, "ChrAdd")) op = GSLT_C0_IOP_ADD;
    else if (gslt_str_eq_cstr(tag, "ChrSubtract")) op = GSLT_C0_IOP_SUB;
    else if (gslt_str_eq_cstr(tag, "ChrMultiply")) op = GSLT_C0_IOP_MUL;
    else if (gslt_str_eq_cstr(tag, "ChrQuotient")) op = GSLT_C0_IOP_QUOT;
    else if (gslt_str_eq_cstr(tag, "ChrRemainder")) op = GSLT_C0_IOP_REM;
    else if (gslt_str_eq_cstr(tag, "ChrModulo")) op = GSLT_C0_IOP_MOD;
    GsltC0IntExpr *l = gslt_c0_parse_ir_expr(a, s->items[1], err, err_cap);
    if (!l) return NULL;
    GsltC0IntExpr *r = gslt_c0_parse_ir_expr(a, s->items[2], err, err_cap);
    if (!r) return NULL;
    GsltC0IntExpr *e = (GsltC0IntExpr *)gslt_arena_alloc(a, sizeof(GsltC0IntExpr));
    e->kind = GSLT_C0_IEXPR_OP;
    e->op = op;
    e->left = l;
    e->right = r;
    return e;
  }
  if (gslt_str_eq_cstr(tag, "ChrOperation") && s->nitems == 4 && s->items[1]->kind == GSLT_SEXPR_SYM) {
    GsltByteStr oname = s->items[1]->text;
    GsltC0IntOp op;
    if (gslt_str_eq_cstr(oname, "ChrAdd")) op = GSLT_C0_IOP_ADD;
    else if (gslt_str_eq_cstr(oname, "ChrSubtract")) op = GSLT_C0_IOP_SUB;
    else if (gslt_str_eq_cstr(oname, "ChrMultiply")) op = GSLT_C0_IOP_MUL;
    else if (gslt_str_eq_cstr(oname, "ChrQuotient")) op = GSLT_C0_IOP_QUOT;
    else if (gslt_str_eq_cstr(oname, "ChrRemainder")) op = GSLT_C0_IOP_REM;
    else if (gslt_str_eq_cstr(oname, "ChrModulo")) op = GSLT_C0_IOP_MOD;
    else {
      snprintf(err, err_cap, "unknown ChrOperation operator");
      return NULL;
    }
    GsltC0IntExpr *l = gslt_c0_parse_ir_expr(a, s->items[2], err, err_cap);
    if (!l) return NULL;
    GsltC0IntExpr *r = gslt_c0_parse_ir_expr(a, s->items[3], err, err_cap);
    if (!r) return NULL;
    GsltC0IntExpr *e = (GsltC0IntExpr *)gslt_arena_alloc(a, sizeof(GsltC0IntExpr));
    e->kind = GSLT_C0_IEXPR_OP;
    e->op = op;
    e->left = l;
    e->right = r;
    return e;
  }
  snprintf(err, err_cap, "unknown C0 IR expression tag");
  return NULL;
}

static inline bool gslt_c0_parse_ir_guard(GsltArena *a, const GsltSexpr *s, GsltC0Guard *out,
                                          char *err, size_t err_cap) {
  memset(out, 0, sizeof(*out));
  if (!s || s->kind != GSLT_SEXPR_LIST || s->nitems < 3 || s->items[0]->kind != GSLT_SEXPR_SYM) {
    snprintf(err, err_cap, "expected C0 IR guard");
    return false;
  }
  GsltByteStr tag = s->items[0]->text;
  if ((gslt_str_eq_cstr(tag, "ChrIdentical") || gslt_str_eq_cstr(tag, "ChrDistinct")) && s->nitems == 3) {
    out->kind = gslt_str_eq_cstr(tag, "ChrIdentical") ? GSLT_C0_GUARD_IDENTICAL : GSLT_C0_GUARD_DISTINCT;
    out->t_left = gslt_c0_parse_ir_term(a, s->items[1], err, err_cap);
    if (!out->t_left) return false;
    out->t_right = gslt_c0_parse_ir_term(a, s->items[2], err, err_cap);
    return out->t_right != NULL;
  }
  if (gslt_str_eq_cstr(tag, "ChrCompare") && s->nitems == 4) {
    GsltByteStr cname = (s->items[1]->kind == GSLT_SEXPR_LIST && s->items[1]->nitems == 1)
                        ? s->items[1]->items[0]->text : s->items[1]->text;
    GsltC0CmpOp cmp;
    if (gslt_str_eq_cstr(cname, "ChrEqual")) cmp = GSLT_C0_CMP_EQ;
    else if (gslt_str_eq_cstr(cname, "ChrDifferent")) cmp = GSLT_C0_CMP_NE;
    else if (gslt_str_eq_cstr(cname, "ChrLess")) cmp = GSLT_C0_CMP_LT;
    else if (gslt_str_eq_cstr(cname, "ChrLessEqual")) cmp = GSLT_C0_CMP_LE;
    else if (gslt_str_eq_cstr(cname, "ChrGreater")) cmp = GSLT_C0_CMP_GT;
    else if (gslt_str_eq_cstr(cname, "ChrGreaterEqual")) cmp = GSLT_C0_CMP_GE;
    else return false;
    out->kind = GSLT_C0_GUARD_COMPARE;
    out->cmp = cmp;
    out->e_left = gslt_c0_parse_ir_expr(a, s->items[2], err, err_cap);
    if (!out->e_left) return false;
    out->e_right = gslt_c0_parse_ir_expr(a, s->items[3], err, err_cap);
    return out->e_right != NULL;
  }
  return false;
}

static inline bool gslt_c0_parse_ir_goal(GsltArena *a, const GsltSexpr *s, GsltC0Goal *out,
                                         char *err, size_t err_cap) {
  memset(out, 0, sizeof(*out));
  if (!s) return false;
  if (s->kind == GSLT_SEXPR_SYM &&
      (gslt_str_eq_cstr(s->text, "ChrFailGoal") || gslt_str_eq_cstr(s->text, "ChrFail"))) {
    out->kind = GSLT_C0_GOAL_FAIL;
    return true;
  }
  if (s->kind == GSLT_SEXPR_LIST && s->nitems == 1 && s->items[0]->kind == GSLT_SEXPR_SYM &&
      (gslt_str_eq_cstr(s->items[0]->text, "ChrFailGoal") || gslt_str_eq_cstr(s->items[0]->text, "ChrFail"))) {
    out->kind = GSLT_C0_GOAL_FAIL;
    return true;
  }
  if (s->kind == GSLT_SEXPR_LIST && s->nitems >= 2 && s->items[0]->kind != GSLT_SEXPR_LIST) {
    GsltByteStr tag = s->items[0]->text;
    if (gslt_str_eq_cstr(tag, "ChrTell") && s->nitems == 2) {
      out->kind = GSLT_C0_GOAL_TELL;
      return gslt_c0_parse_ir_head(a, s->items[1], &out->tell_head, err, err_cap);
    }
    if (gslt_str_eq_cstr(tag, "ChrAssign") && s->nitems == 3 && s->items[1]->kind == GSLT_SEXPR_INT) {
      uint64_t idx = 0;
      if (!c0_bigint_to_u64(&s->items[1]->int_val, &idx)) return false;
      out->kind = GSLT_C0_GOAL_ASSIGN;
      out->assign_var = (uint32_t)idx;
      out->assign_expr = gslt_c0_parse_ir_expr(a, s->items[2], err, err_cap);
      return out->assign_expr != NULL;
    }
  }
  return false;
}

static inline bool gslt_c0_parse_ir(GsltArena *a, const char *src, size_t len,
                                    GsltC0Program *out_prog, GsltC0Diagnostic *out_diag,
                                    char *err, size_t err_cap) {
  memset(out_prog, 0, sizeof(*out_prog));
  if (out_diag) memset(out_diag, 0, sizeof(*out_diag));
  GsltSexpr *root = gslt_sexpr_parse_all(a, src, len, err, err_cap);
  if (!root || root->kind != GSLT_SEXPR_LIST || (root->nitems != 3 && root->nitems != 4) ||
      root->items[0]->kind != GSLT_SEXPR_SYM ||
      (!gslt_str_eq_cstr(root->items[0]->text, "C0Program") &&
       !gslt_str_eq_cstr(root->items[0]->text, "ChrProgram")) ||
      root->items[1]->kind != GSLT_SEXPR_LIST ||
      root->items[2]->kind != GSLT_SEXPR_LIST ||
      (root->nitems == 4 && root->items[3]->kind != GSLT_SEXPR_LIST)) {
    snprintf(err, err_cap, "expected (C0Program declarations rules inputs) or (ChrProgram declarations rules [inputs])");
    return false;
  }
  const GsltSexpr *decls_s = root->items[1];
  const GsltSexpr *rules_s = root->items[2];
  const GsltSexpr *inputs_s = (root->nitems == 4) ? root->items[3] : NULL;

  out_prog->ndecls = decls_s->nitems;
  out_prog->decls = (GsltC0Declaration *)gslt_arena_alloc(a, (out_prog->ndecls + 1) * sizeof(GsltC0Declaration));
  for (uint32_t i = 0; i < decls_s->nitems; i++) {
    const GsltSexpr *d = decls_s->items[i];
    if (d->kind != GSLT_SEXPR_LIST || d->nitems != 3 ||
        d->items[0]->kind != GSLT_SEXPR_SYM ||
        (!gslt_str_eq_cstr(d->items[0]->text, "C0Declaration") &&
         !gslt_str_eq_cstr(d->items[0]->text, "ChrDeclare")) ||
        d->items[2]->kind != GSLT_SEXPR_INT) {
      snprintf(err, err_cap, "invalid C0Declaration in IR");
      return false;
    }
    uint64_t ar = 0;
    if (!c0_bigint_to_u64(&d->items[2]->int_val, &ar)) return false;
    out_prog->decls[i].name = d->items[1]->text;
    out_prog->decls[i].arity = (uint32_t)ar;
  }

  out_prog->nrules = rules_s->nitems;
  out_prog->rules = (GsltC0Rule *)gslt_arena_alloc(a, (out_prog->nrules + 1) * sizeof(GsltC0Rule));
  for (uint32_t r = 0; r < rules_s->nitems; r++) {
    const GsltSexpr *rs = rules_s->items[r];
    if (rs->kind != GSLT_SEXPR_LIST || rs->nitems != 6 ||
        rs->items[0]->kind != GSLT_SEXPR_SYM ||
        (!gslt_str_eq_cstr(rs->items[0]->text, "C0Rule") &&
         !gslt_str_eq_cstr(rs->items[0]->text, "ChrRule")) ||
        rs->items[2]->kind != GSLT_SEXPR_LIST || rs->items[3]->kind != GSLT_SEXPR_LIST ||
        rs->items[4]->kind != GSLT_SEXPR_LIST || rs->items[5]->kind != GSLT_SEXPR_LIST) {
      snprintf(err, err_cap, "invalid C0Rule in IR");
      return false;
    }
    GsltC0Rule *rule = &out_prog->rules[r];
    rule->name = rs->items[1]->text;
    rule->nkept = rs->items[2]->nitems;
    rule->kept = (GsltC0Head *)gslt_arena_alloc(a, (rule->nkept + 1) * sizeof(GsltC0Head));
    for (uint32_t i = 0; i < rule->nkept; i++) {
      if (!gslt_c0_parse_ir_head(a, rs->items[2]->items[i], &rule->kept[i], err, err_cap)) return false;
    }
    rule->nremoved = rs->items[3]->nitems;
    rule->removed = (GsltC0Head *)gslt_arena_alloc(a, (rule->nremoved + 1) * sizeof(GsltC0Head));
    for (uint32_t i = 0; i < rule->nremoved; i++) {
      if (!gslt_c0_parse_ir_head(a, rs->items[3]->items[i], &rule->removed[i], err, err_cap)) return false;
    }
    rule->nguards = rs->items[4]->nitems;
    rule->guards = (GsltC0Guard *)gslt_arena_alloc(a, (rule->nguards + 1) * sizeof(GsltC0Guard));
    for (uint32_t i = 0; i < rule->nguards; i++) {
      if (!gslt_c0_parse_ir_guard(a, rs->items[4]->items[i], &rule->guards[i], err, err_cap)) return false;
    }
    rule->nbody = rs->items[5]->nitems;
    rule->body = (GsltC0Goal *)gslt_arena_alloc(a, (rule->nbody + 1) * sizeof(GsltC0Goal));
    for (uint32_t i = 0; i < rule->nbody; i++) {
      if (!gslt_c0_parse_ir_goal(a, rs->items[5]->items[i], &rule->body[i], err, err_cap)) return false;
    }
  }

  out_prog->ninputs = inputs_s ? inputs_s->nitems : 0;
  out_prog->inputs = (GsltC0Head *)gslt_arena_alloc(a, (out_prog->ninputs + 1) * sizeof(GsltC0Head));
  for (uint32_t i = 0; i < out_prog->ninputs; i++) {
    if (!gslt_c0_parse_ir_head(a, inputs_s->items[i], &out_prog->inputs[i], err, err_cap)) return false;
    for (uint32_t j = 0; j < out_prog->inputs[i].arity; j++) {
      GsltC0Value *gv = gslt_c0_ground_term_to_val(a, out_prog->inputs[i].args[j]);
      if (!gv) {
        snprintf(err, err_cap, "initial C0 queries must be ground");
        return false;
      }
      out_prog->inputs[i].args[j]->kind = GSLT_C0_TERM_VAL;
      out_prog->inputs[i].args[j]->val = gv;
    }
    if (!gslt_c0_is_declared(out_prog->decls, out_prog->ndecls,
                             out_prog->inputs[i].name, out_prog->inputs[i].arity)) {
      if (out_diag) {
        out_diag->kind = GSLT_C0_DIAG_UNDECLARED_QUERY;
        out_diag->head = out_prog->inputs[i];
      }
      snprintf(err, err_cap, "initial C0 constraint has no matching name/arity declaration");
      return false;
    }
  }

  GsltC0Diagnostic diag;
  if (!gslt_c0_diagnose(out_prog->decls, out_prog->ndecls, out_prog->rules, out_prog->nrules, &diag)) {
    if (out_diag) *out_diag = diag;
    snprintf(err, err_cap, "C0 admission refused: %s (rule %u)",
             gslt_c0_diag_name(diag.kind), diag.rule_index);
    return false;
  }
  return true;
}

/* ---- C0 SyntaxGSLT Packet Synthesizer (PlTerm -> (result (node chr:program ...) nil)) ----
 * Synthesizes a genuine SyntaxGSLT packet tree over CHRPrologSyntax.lean node labels
 * (chr:program, chr:sentences-more, pl:sentence, pl:apply:N, pl:compound, pl:atom, pl:variable, pl:number)
 * so any C0 program or sentence list can be serialized as a selected packet or SourceValuesV1 catalogue
 * and re-read by gslt_c0_lower_packet / gslt_c0_read_catalogue! */
static inline void gslt_c0_emit_pkt_word_chars(GsltArena *a, GsltStrBuf *sb,
                                               const char *first_lbl, const char *rest_lbl,
                                               GsltByteStr text) {
  if (text.len == 0) {
    gslt_sb_append_cstr(a, sb, "(node pl:name-tail-empty nil)");
    return;
  }
  uint32_t cp0 = (uint8_t)text.bytes[0];
  gslt_sb_append_cstr(a, sb, "(pair (node ");
  gslt_sb_append_cstr(a, sb, first_lbl);
  gslt_sb_append_cstr(a, sb, " (cp ");
  gslt_sb_append_u32(a, sb, cp0);
  gslt_sb_append_cstr(a, sb, ")) (pair ");
  for (uint32_t i = 1; i < text.len; i++) {
    gslt_sb_append_cstr(a, sb, "(node pl:name-tail-more (pair (node ");
    gslt_sb_append_cstr(a, sb, rest_lbl);
    gslt_sb_append_cstr(a, sb, " (cp ");
    gslt_sb_append_u32(a, sb, (uint8_t)text.bytes[i]);
    gslt_sb_append_cstr(a, sb, ")) (pair ");
  }
  gslt_sb_append_cstr(a, sb, "(node pl:name-tail-empty nil)");
  for (uint32_t i = 1; i < text.len; i++) {
    gslt_sb_append_cstr(a, sb, " nil)))");
  }
  gslt_sb_append_cstr(a, sb, " nil))");
}

static inline void gslt_c0_emit_pkt_atom_node(GsltArena *a, GsltStrBuf *sb, GsltByteStr name) {
  /* Check if simple lowercase ASCII word */
  bool is_word = (name.len > 0 && name.bytes[0] >= 'a' && name.bytes[0] <= 'z');
  for (uint32_t i = 1; is_word && i < name.len; i++) {
    char c = name.bytes[i];
    if (!isalnum((unsigned char)c) && c != '_') is_word = false;
  }
  if (is_word) {
    gslt_sb_append_cstr(a, sb, "(node pl:atom-word (pair (node pl:word ");
    gslt_c0_emit_pkt_word_chars(a, sb, "pl:lower", "pl:name-rest", name);
    gslt_sb_append_cstr(a, sb, ") nil))");
  } else {
    /* Emit as pl:atom-quoted */
    gslt_sb_append_cstr(a, sb, "(node pl:atom-quoted (pair ");
    uint32_t closes = 0;
    size_t pos = 0;
    while (pos < name.len) {
      uint32_t cp = 0;
      size_t adv = gslt_utf8_decode(name.bytes + pos, name.len - pos, &cp);
      if (adv == 0) { cp = (uint8_t)name.bytes[pos]; adv = 1; }
      pos += adv;
      if (cp == '\'') {
        gslt_sb_append_cstr(a, sb, "(node pl:single-quote (pair ");
        closes += 2;
      } else {
        gslt_sb_append_cstr(a, sb, "(node pl:single-more (pair (node pl:single-scalar (cp ");
        gslt_sb_append_u32(a, sb, cp);
        gslt_sb_append_cstr(a, sb, ")) (pair ");
        closes += 3;
      }
    }
    gslt_sb_append_cstr(a, sb, "(node pl:single-empty nil)");
    while (closes > 0) {
      if (closes >= 3) {
        gslt_sb_append_cstr(a, sb, " nil)))");
        closes -= 3;
      } else {
        gslt_sb_append_cstr(a, sb, " nil))");
        closes -= 2;
      }
    }
    gslt_sb_append_cstr(a, sb, " nil))");
  }
}

static inline int gslt_c0_find_op_index(GsltByteStr name, uint32_t arity) {
  for (int i = 0; i < GSLT_C0_NUM_OPERATORS; i++) {
    GsltOpSpec sp = GSLT_C0_OPERATORS[i].spec;
    bool is_unary = (sp == GSLT_OP_FX || sp == GSLT_OP_FY || sp == GSLT_OP_XF || sp == GSLT_OP_YF);
    if (((arity == 1 && is_unary) || (arity == 2 && !is_unary)) &&
        gslt_str_eq_cstr(name, GSLT_C0_OPERATORS[i].name)) {
      return i;
    }
  }
  return -1;
}

static inline void gslt_c0_emit_pkt_pl_term(GsltArena *a, GsltStrBuf *sb, const GsltPlTerm *t) {
  if (t->kind == GSLT_PL_VAR || t->kind == GSLT_PL_FRESH) {
    GsltByteStr vname = (t->kind == GSLT_PL_FRESH) ? gslt_str_from_cstr(a, "_") : t->name;
    gslt_sb_append_cstr(a, sb, "(node pl:variable (pair (node pl:variable-name ");
    gslt_c0_emit_pkt_word_chars(a, sb, "pl:variable-start", "pl:name-rest", vname);
    gslt_sb_append_cstr(a, sb, ") nil))");
    return;
  }
  if (t->kind == GSLT_PL_INT) {
    char dbuf[512];
    C0BigInt mag = t->ival;
    bool neg = (mag.sign < 0);
    if (neg) mag.sign = 1;
    c0_bigint_format_dec(&mag, dbuf, sizeof(dbuf));
    size_t dlen = strlen(dbuf);
    if (neg) {
      /* Prefix '-' operator 8 with pl:layout-empty folds to negative integer */
      gslt_sb_append_cstr(a, sb, "(node pl:apply:8 (pair (node pl:operator:8 nil) (pair (node pl:layout-empty nil) (pair ");
    }
    gslt_sb_append_cstr(a, sb, "(node pl:number (pair (node pl:number-decimal (pair ");
    for (size_t i = 0; i < dlen; i++) {
      if (i + 1 < dlen) {
        gslt_sb_append_cstr(a, sb, "(node pl:digits-more (pair (node pl:digit (cp ");
        gslt_sb_append_u32(a, sb, (uint8_t)dbuf[i]);
        gslt_sb_append_cstr(a, sb, ")) (pair ");
      } else {
        gslt_sb_append_cstr(a, sb, "(node pl:digits-one (pair (node pl:digit (cp ");
        gslt_sb_append_u32(a, sb, (uint8_t)dbuf[i]);
        gslt_sb_append_cstr(a, sb, ")) nil))");
      }
    }
    for (size_t i = 1; i < dlen; i++) gslt_sb_append_cstr(a, sb, " nil)))");
    gslt_sb_append_cstr(a, sb, " nil)) nil))");
    if (neg) gslt_sb_append_cstr(a, sb, " nil))))");
    return;
  }
  if (t->kind == GSLT_PL_ATOM) {
    gslt_sb_append_cstr(a, sb, "(node pl:atom (pair ");
    gslt_c0_emit_pkt_atom_node(a, sb, t->name);
    gslt_sb_append_cstr(a, sb, " nil))");
    return;
  }
  if (t->kind == GSLT_PL_COMPOUND) {
    int op_idx = gslt_c0_find_op_index(t->name, t->nargs);
    if (op_idx >= 0) {
      const GsltPrologOp *op = &GSLT_C0_OPERATORS[op_idx];
      if (t->nargs == 1 && (op->spec == GSLT_OP_FX || op->spec == GSLT_OP_FY)) {
        gslt_sb_append_cstr(a, sb, "(node pl:apply:");
        gslt_sb_append_u32(a, sb, (uint32_t)op_idx);
        gslt_sb_append_cstr(a, sb, " (pair (node pl:operator:");
        gslt_sb_append_u32(a, sb, (uint32_t)op_idx);
        gslt_sb_append_cstr(a, sb, " nil) (pair (node pl:layout-space (pair (node pl:space (cp 32)) (pair (node pl:layout-empty nil) nil))) (pair ");
        gslt_c0_emit_pkt_pl_term(a, sb, t->args[0]);
        gslt_sb_append_cstr(a, sb, " nil))))");
        return;
      }
      if (t->nargs == 2) {
        gslt_sb_append_cstr(a, sb, "(node pl:apply:");
        gslt_sb_append_u32(a, sb, (uint32_t)op_idx);
        gslt_sb_append_cstr(a, sb, " (pair ");
        gslt_c0_emit_pkt_pl_term(a, sb, t->args[0]);
        gslt_sb_append_cstr(a, sb, " (pair (node pl:layout-empty nil) (pair (node pl:operator:");
        gslt_sb_append_u32(a, sb, (uint32_t)op_idx);
        gslt_sb_append_cstr(a, sb, " nil) (pair (node pl:layout-empty nil) (pair ");
        gslt_c0_emit_pkt_pl_term(a, sb, t->args[1]);
        gslt_sb_append_cstr(a, sb, " nil))))))");
        return;
      }
    }
    gslt_sb_append_cstr(a, sb, "(node pl:compound (pair ");
    gslt_c0_emit_pkt_atom_node(a, sb, t->name);
    gslt_sb_append_cstr(a, sb, " (pair (node pl:layout-empty nil) (pair ");
    for (uint32_t i = 0; i < t->nargs; i++) {
      if (i + 1 < t->nargs) {
        gslt_sb_append_cstr(a, sb, "(node pl:arguments-more (pair ");
        gslt_c0_emit_pkt_pl_term(a, sb, t->args[i]);
        gslt_sb_append_cstr(a, sb, " (pair (node pl:layout-empty nil) (pair (node pl:layout-empty nil) (pair ");
      } else {
        gslt_sb_append_cstr(a, sb, "(node pl:arguments-one (pair ");
        gslt_c0_emit_pkt_pl_term(a, sb, t->args[i]);
        gslt_sb_append_cstr(a, sb, " nil))");
      }
    }
    for (uint32_t i = 1; i < t->nargs; i++) gslt_sb_append_cstr(a, sb, " nil)))))");
    gslt_sb_append_cstr(a, sb, " (pair (node pl:layout-empty nil) nil)))))");
  }
}

static inline GsltByteStr gslt_c0_source_to_packet_str(GsltArena *a, const char *src, size_t len,
                                                       char *err, size_t err_cap) {
  GsltByteStr empty = { "", 0 };
  GsltPlTerm **sentences = NULL;
  uint32_t nsentences = 0;
  if (!gslt_c0_source_to_sentences(a, src, len, &sentences, &nsentences, err, err_cap)) {
    return empty;
  }
  GsltStrBuf sb;
  gslt_sb_init(a, &sb, 1024);
  gslt_sb_append_cstr(a, &sb, "(result (node chr:program (pair ");
  for (uint32_t i = 0; i < nsentences; i++) {
    gslt_sb_append_cstr(a, &sb, "(node chr:sentences-more (pair (node pl:sentence (pair (node pl:layout-empty nil) (pair ");
    gslt_c0_emit_pkt_pl_term(a, &sb, sentences[i]);
    gslt_sb_append_cstr(a, &sb, " (pair (node pl:layout-empty nil) (pair (node pl:layout-empty nil) nil))))) (pair ");
  }
  gslt_sb_append_cstr(a, &sb, "(node chr:sentences-empty (pair (node pl:layout-empty nil) nil))");
  for (uint32_t i = 0; i < nsentences; i++) {
    gslt_sb_append_cstr(a, &sb, " nil)))");
  }
  gslt_sb_append_cstr(a, &sb, " nil)) nil)");
  GsltByteStr out = { sb.buf, (uint32_t)sb.len };
  return out;
}


/* =========================================================================
 * 8. D0 SyntaxGSLT Packet Lowerer, Catalogue Reader & Lean IRCodec Bridge
 * =========================================================================
 * Matches hyperon/cetta-prime-nik-20260811/langdef/lang/datalog/reader.metta
 * and Mettapedia/GSLT/LanguageDef/ModuleFormat/SouffleDatalogSourceReader.lean:
 *   - Layout filtering: dl-src:trivia-empty, dl-src:trivia-space,
 *     dl-src:trivia-line-comment, dl-src:trivia-block-comment,
 *     dl-src:directive-space
 *   - 64-bit domain validation: D0NumberValue in [-2^63, 2^63),
 *     D0UnsignedValue in [0, 2^64); rejects FloatingLiteral
 *   - Escapes: dl-src:escape-quote (34), dl-src:escape-apostrophe (39),
 *     dl-src:escape-slash (92), dl-src:escape-bell (7),
 *     dl-src:escape-backspace (8), dl-src:escape-formfeed (12),
 *     dl-src:escape-newline (10), dl-src:escape-return (13),
 *     dl-src:escape-tab (9), dl-src:escape-vertical-tab (11)
 *   - Emits canonical (D0Program ...) S-expression consumed by d0_parse_ir_program.
 */

static inline void gslt_sb_append_char(GsltArena *a, GsltStrBuf *sb, char c) {
  gslt_sb_append_bytes(a, sb, &c, 1);
}

static inline void gslt_sb_append_ir_quoted(GsltArena *a, GsltStrBuf *sb, GsltByteStr s) {
  gslt_sb_append_quoted_str(a, sb, s);
}

static inline bool gslt_d0_pkt_fields(GsltArena *a, const GsltSexpr *fields,
                                      const GsltSexpr ***out_items, uint32_t *out_count) {
  const GsltSexpr **raw = NULL;
  uint32_t nraw = 0;
  if (!gslt_packet_fields(a, fields, &raw, &nraw)) return false;
  const GsltSexpr **kept = (const GsltSexpr **)gslt_arena_alloc(a, (nraw + 1) * sizeof(GsltSexpr *));
  if (!kept) return false;
  uint32_t k = 0;
  for (uint32_t i = 0; i < nraw; i++) {
    GsltByteStr lbl;
    const GsltSexpr *f = NULL;
    if (gslt_packet_is_node(raw[i], &lbl, &f) && gslt_d0_is_layout(lbl)) {
      continue;
    }
    kept[k++] = raw[i];
  }
  *out_items = kept;
  *out_count = k;
  return true;
}

static inline bool gslt_d0_pkt_text(GsltArena *a, const GsltSexpr *node, GsltByteStr *out) {
  return gslt_c0_pkt_text_of(a, node, out);
}

static inline bool gslt_d0_pkt_qualified_name(GsltArena *a, const GsltSexpr *node,
                                              GsltStrBuf *sb, char *err, size_t err_cap) {
  GsltByteStr lbl;
  const GsltSexpr *fields = NULL;
  if (!gslt_packet_is_node(node, &lbl, &fields)) {
    snprintf(err, err_cap, "D0Error: UnknownName");
    return false;
  }
  const GsltSexpr **ch = NULL;
  uint32_t nch = 0;
  if (!gslt_d0_pkt_fields(a, fields, &ch, &nch)) return false;
  if (gslt_str_eq_cstr(lbl, "dl-src:qualified-name-one") && nch == 1) {
    GsltByteStr id;
    if (!gslt_d0_pkt_text(a, ch[0], &id)) return false;
    gslt_sb_append_ir_quoted(a, sb, id);
    return true;
  }
  if (gslt_str_eq_cstr(lbl, "dl-src:qualified-name-more") && nch == 2) {
    GsltByteStr id;
    if (!gslt_d0_pkt_text(a, ch[0], &id)) return false;
    gslt_sb_append_ir_quoted(a, sb, id);
    gslt_sb_append_char(a, sb, ' ');
    return gslt_d0_pkt_qualified_name(a, ch[1], sb, err, err_cap);
  }
  snprintf(err, err_cap, "D0Error: UnknownName %.*s", (int)lbl.len, lbl.bytes);
  return false;
}

static inline bool gslt_d0_pkt_constant(GsltArena *a, const GsltSexpr *node,
                                        GsltStrBuf *sb, char *err, size_t err_cap) {
  GsltByteStr lbl;
  const GsltSexpr *fields = NULL;
  if (!gslt_packet_is_node(node, &lbl, &fields)) {
    snprintf(err, err_cap, "D0Error: UnknownConstant");
    return false;
  }
  const GsltSexpr **ch = NULL;
  uint32_t nch = 0;
  if (!gslt_d0_pkt_fields(a, fields, &ch, &nch) || nch != 1) {
    snprintf(err, err_cap, "D0Error: UnknownConstant");
    return false;
  }
  if (gslt_str_eq_cstr(lbl, "dl-src:constant-float")) {
    snprintf(err, err_cap, "D0Error: FloatingLiteral");
    return false;
  }
  if (gslt_str_eq_cstr(lbl, "dl-src:constant-integer")) {
    GsltByteStr nlbl;
    const GsltSexpr *nfields = NULL;
    if (!gslt_packet_is_node(ch[0], &nlbl, &nfields)) return false;
    const GsltSexpr **nch = NULL;
    uint32_t nnch = 0;
    if (!gslt_d0_pkt_fields(a, nfields, &nch, &nnch) || nnch != 1) return false;
    GsltByteStr digits;
    if (!gslt_d0_pkt_text(a, nch[0], &digits)) return false;
    uint32_t radix = 10;
    bool neg = false;
    if (gslt_str_eq_cstr(nlbl, "dl-src:integer-decimal")) { radix = 10; neg = false; }
    else if (gslt_str_eq_cstr(nlbl, "dl-src:integer-binary")) { radix = 2; neg = false; }
    else if (gslt_str_eq_cstr(nlbl, "dl-src:integer-hex")) { radix = 16; neg = false; }
    else if (gslt_str_eq_cstr(nlbl, "dl-src:integer-negative")) { radix = 10; neg = true; }
    else if (gslt_str_eq_cstr(nlbl, "dl-src:integer-negative-binary")) { radix = 2; neg = true; }
    else if (gslt_str_eq_cstr(nlbl, "dl-src:integer-negative-hex")) { radix = 16; neg = true; }
    else {
      snprintf(err, err_cap, "D0Error: UnknownNumber");
      return false;
    }
    C0BigInt mag;
    if (!c0_bigint_parse_radix(digits.bytes, digits.len, radix, &mag)) {
      snprintf(err, err_cap, "D0Error: NumberOutsideDomain");
      return false;
    }
    if (neg && mag.sign != 0) mag.sign = -1;
    int64_t sval = 0;
    if (!c0_bigint_to_i64(&mag, &sval)) {
      snprintf(err, err_cap, "D0Error: NumberOutsideDomain");
      return false;
    }
    char ibuf[64];
    snprintf(ibuf, sizeof(ibuf), "(D0NumberValue %" PRId64 ")", sval);
    gslt_sb_append_cstr(a, sb, ibuf);
    return true;
  }
  if (gslt_str_eq_cstr(lbl, "dl-src:constant-unsigned")) {
    GsltByteStr nlbl;
    const GsltSexpr *nfields = NULL;
    if (!gslt_packet_is_node(ch[0], &nlbl, &nfields)) return false;
    const GsltSexpr **nch = NULL;
    uint32_t nnch = 0;
    if (!gslt_d0_pkt_fields(a, nfields, &nch, &nnch) || nnch != 1) return false;
    GsltByteStr digits;
    if (!gslt_d0_pkt_text(a, nch[0], &digits)) return false;
    uint32_t radix = 10;
    if (gslt_str_eq_cstr(nlbl, "dl-src:unsigned-decimal")) radix = 10;
    else if (gslt_str_eq_cstr(nlbl, "dl-src:unsigned-binary")) radix = 2;
    else if (gslt_str_eq_cstr(nlbl, "dl-src:unsigned-hex")) radix = 16;
    else {
      snprintf(err, err_cap, "D0Error: UnknownNumber");
      return false;
    }
    C0BigInt mag;
    uint64_t uval = 0;
    if (!c0_bigint_parse_radix(digits.bytes, digits.len, radix, &mag) ||
        !c0_bigint_to_u64(&mag, &uval)) {
      snprintf(err, err_cap, "D0Error: UnsignedOutsideDomain");
      return false;
    }
    char ubuf[64];
    snprintf(ubuf, sizeof(ubuf), "(D0UnsignedValue %" PRIu64 ")", uval);
    gslt_sb_append_cstr(a, sb, ubuf);
    return true;
  }
  if (gslt_str_eq_cstr(lbl, "dl-src:constant-symbol")) {
    GsltByteStr slbl;
    const GsltSexpr *sfields = NULL;
    if (!gslt_packet_is_node(ch[0], &slbl, &sfields) || !gslt_str_eq_cstr(slbl, "dl-src:symbol")) {
      snprintf(err, err_cap, "D0Error: UnknownSymbol");
      return false;
    }
    const GsltSexpr **sch = NULL;
    uint32_t nsch = 0;
    if (!gslt_d0_pkt_fields(a, sfields, &sch, &nsch) || nsch != 1) return false;
    GsltStrBuf sym_buf;
    gslt_sb_init(a, &sym_buf, 64);
    const GsltSexpr *cur = sch[0];
    while (true) {
      GsltByteStr blbl;
      const GsltSexpr *bfields = NULL;
      if (!gslt_packet_is_node(cur, &blbl, &bfields)) {
        snprintf(err, err_cap, "D0Error: UnknownSymbolBody");
        return false;
      }
      const GsltSexpr **bch = NULL;
      uint32_t nbch = 0;
      if (!gslt_d0_pkt_fields(a, bfields, &bch, &nbch)) return false;
      if (gslt_str_eq_cstr(blbl, "dl-src:symbol-empty") && nbch == 0) {
        break;
      }
      if (gslt_str_eq_cstr(blbl, "dl-src:symbol-body") && nbch == 2) {
        GsltByteStr seg;
        if (!gslt_d0_pkt_text(a, bch[0], &seg)) return false;
        gslt_sb_append_bytes(a, &sym_buf, seg.bytes, seg.len);
        cur = bch[1];
        continue;
      }
      if (gslt_str_eq_cstr(blbl, "dl-src:symbol-escape") && nbch == 2) {
        GsltByteStr elbl;
        const GsltSexpr *efields = NULL;
        if (!gslt_packet_is_node(bch[0], &elbl, &efields)) return false;
        char ec = 0;
        if (gslt_str_eq_cstr(elbl, "dl-src:escape-quote")) ec = '"';
        else if (gslt_str_eq_cstr(elbl, "dl-src:escape-apostrophe")) ec = '\'';
        else if (gslt_str_eq_cstr(elbl, "dl-src:escape-slash")) ec = '\\';
        else if (gslt_str_eq_cstr(elbl, "dl-src:escape-bell")) ec = '\a';
        else if (gslt_str_eq_cstr(elbl, "dl-src:escape-backspace")) ec = '\b';
        else if (gslt_str_eq_cstr(elbl, "dl-src:escape-formfeed")) ec = '\f';
        else if (gslt_str_eq_cstr(elbl, "dl-src:escape-newline")) ec = '\n';
        else if (gslt_str_eq_cstr(elbl, "dl-src:escape-return")) ec = '\r';
        else if (gslt_str_eq_cstr(elbl, "dl-src:escape-tab")) ec = '\t';
        else if (gslt_str_eq_cstr(elbl, "dl-src:escape-vertical-tab")) ec = '\v';
        else {
          snprintf(err, err_cap, "D0Error: UnknownEscape");
          return false;
        }
        gslt_sb_append_char(a, &sym_buf, ec);
        cur = bch[1];
        continue;
      }
      snprintf(err, err_cap, "D0Error: UnknownSymbolBody");
      return false;
    }
    GsltByteStr sstr = { sym_buf.buf, (uint32_t)sym_buf.len };
    gslt_sb_append_cstr(a, sb, "(D0SymbolValue ");
    gslt_sb_append_ir_quoted(a, sb, sstr);
    gslt_sb_append_char(a, sb, ')');
    return true;
  }
  snprintf(err, err_cap, "D0Error: UnknownConstant");
  return false;
}

static inline bool gslt_d0_pkt_term(GsltArena *a, const GsltSexpr *node,
                                    GsltStrBuf *sb, char *err, size_t err_cap) {
  GsltByteStr lbl;
  const GsltSexpr *fields = NULL;
  if (!gslt_packet_is_node(node, &lbl, &fields)) return false;
  const GsltSexpr **ch = NULL;
  uint32_t nch = 0;
  if (!gslt_d0_pkt_fields(a, fields, &ch, &nch)) return false;
  if (gslt_str_eq_cstr(lbl, "dl-src:term-variable") && nch == 1) {
    GsltByteStr vname;
    if (!gslt_d0_pkt_text(a, ch[0], &vname)) return false;
    gslt_sb_append_cstr(a, sb, "(D0Var ");
    gslt_sb_append_ir_quoted(a, sb, vname);
    gslt_sb_append_char(a, sb, ')');
    return true;
  }
  if (gslt_str_eq_cstr(lbl, "dl-src:term-anonymous") && nch == 0) {
    gslt_sb_append_cstr(a, sb, "D0Anonymous");
    return true;
  }
  if (gslt_str_eq_cstr(lbl, "dl-src:term-constant") && nch == 1) {
    gslt_sb_append_cstr(a, sb, "(D0Literal ");
    if (!gslt_d0_pkt_constant(a, ch[0], sb, err, err_cap)) return false;
    gslt_sb_append_char(a, sb, ')');
    return true;
  }
  snprintf(err, err_cap, "D0Error: UnknownTerm");
  return false;
}

static inline bool gslt_d0_pkt_terms(GsltArena *a, const GsltSexpr *node,
                                     GsltStrBuf *sb, bool first, char *err, size_t err_cap) {
  GsltByteStr lbl;
  const GsltSexpr *fields = NULL;
  if (!gslt_packet_is_node(node, &lbl, &fields)) return false;
  const GsltSexpr **ch = NULL;
  uint32_t nch = 0;
  if (!gslt_d0_pkt_fields(a, fields, &ch, &nch)) return false;
  if (gslt_str_eq_cstr(lbl, "dl-src:terms-empty") && nch == 0) return true;
  if (gslt_str_eq_cstr(lbl, "dl-src:terms-one") && nch == 1) {
    if (!first) gslt_sb_append_char(a, sb, ' ');
    return gslt_d0_pkt_term(a, ch[0], sb, err, err_cap);
  }
  if (gslt_str_eq_cstr(lbl, "dl-src:terms-more") && nch == 2) {
    if (!first) gslt_sb_append_char(a, sb, ' ');
    if (!gslt_d0_pkt_term(a, ch[0], sb, err, err_cap)) return false;
    return gslt_d0_pkt_terms(a, ch[1], sb, false, err, err_cap);
  }
  snprintf(err, err_cap, "D0Error: UnknownTermsList");
  return false;
}

static inline bool gslt_d0_pkt_constants(GsltArena *a, const GsltSexpr *node,
                                         GsltStrBuf *sb, bool first, char *err, size_t err_cap) {
  GsltByteStr lbl;
  const GsltSexpr *fields = NULL;
  if (!gslt_packet_is_node(node, &lbl, &fields)) return false;
  const GsltSexpr **ch = NULL;
  uint32_t nch = 0;
  if (!gslt_d0_pkt_fields(a, fields, &ch, &nch)) return false;
  if (gslt_str_eq_cstr(lbl, "dl-src:constants-empty") && nch == 0) return true;
  if (gslt_str_eq_cstr(lbl, "dl-src:constants-one") && nch == 1) {
    if (!first) gslt_sb_append_char(a, sb, ' ');
    return gslt_d0_pkt_constant(a, ch[0], sb, err, err_cap);
  }
  if (gslt_str_eq_cstr(lbl, "dl-src:constants-more") && nch == 2) {
    if (!first) gslt_sb_append_char(a, sb, ' ');
    if (!gslt_d0_pkt_constant(a, ch[0], sb, err, err_cap)) return false;
    return gslt_d0_pkt_constants(a, ch[1], sb, false, err, err_cap);
  }
  snprintf(err, err_cap, "D0Error: UnknownConstantsList");
  return false;
}

static inline bool gslt_d0_pkt_atom(GsltArena *a, const GsltSexpr *node,
                                    GsltStrBuf *sb, char *err, size_t err_cap) {
  GsltByteStr lbl;
  const GsltSexpr *fields = NULL;
  if (!gslt_packet_is_node(node, &lbl, &fields) || !gslt_str_eq_cstr(lbl, "dl-src:atom")) {
    snprintf(err, err_cap, "D0Error: UnknownAtom");
    return false;
  }
  const GsltSexpr **ch = NULL;
  uint32_t nch = 0;
  if (!gslt_d0_pkt_fields(a, fields, &ch, &nch) || nch != 2) return false;
  gslt_sb_append_cstr(a, sb, "(D0Atom (");
  if (!gslt_d0_pkt_qualified_name(a, ch[0], sb, err, err_cap)) return false;
  gslt_sb_append_cstr(a, sb, ") (");
  if (!gslt_d0_pkt_terms(a, ch[1], sb, true, err, err_cap)) return false;
  gslt_sb_append_cstr(a, sb, "))");
  return true;
}

static inline bool gslt_d0_pkt_premise(GsltArena *a, const GsltSexpr *node,
                                       GsltStrBuf *sb, char *err, size_t err_cap) {
  GsltByteStr lbl;
  const GsltSexpr *fields = NULL;
  if (!gslt_packet_is_node(node, &lbl, &fields)) return false;
  const GsltSexpr **ch = NULL;
  uint32_t nch = 0;
  if (!gslt_d0_pkt_fields(a, fields, &ch, &nch) || nch != 1) return false;
  if (gslt_str_eq_cstr(lbl, "dl-src:positive-atom")) {
    gslt_sb_append_cstr(a, sb, "(D0Positive ");
    if (!gslt_d0_pkt_atom(a, ch[0], sb, err, err_cap)) return false;
    gslt_sb_append_char(a, sb, ')');
    return true;
  }
  if (gslt_str_eq_cstr(lbl, "dl-src:positive-comparison")) {
    GsltByteStr clbl;
    const GsltSexpr *cfields = NULL;
    if (!gslt_packet_is_node(ch[0], &clbl, &cfields) || !gslt_str_eq_cstr(clbl, "dl-src:comparison")) {
      snprintf(err, err_cap, "D0Error: MalformedComparison");
      return false;
    }
    const GsltSexpr **cch = NULL;
    uint32_t ncch = 0;
    if (!gslt_d0_pkt_fields(a, cfields, &cch, &ncch) || ncch != 3) {
      snprintf(err, err_cap, "D0Error: MalformedComparison");
      return false;
    }
    GsltByteStr olbl;
    const GsltSexpr *ofields = NULL;
    if (!gslt_packet_is_node(cch[1], &olbl, &ofields)) return false;
    const char *op_ir = NULL;
    if (gslt_str_eq_cstr(olbl, "dl-src:comparison-equal")) op_ir = "D0Equal";
    else if (gslt_str_eq_cstr(olbl, "dl-src:comparison-different")) op_ir = "D0Different";
    else if (gslt_str_eq_cstr(olbl, "dl-src:comparison-less")) op_ir = "D0Less";
    else if (gslt_str_eq_cstr(olbl, "dl-src:comparison-less-equal")) op_ir = "D0LessEqual";
    else if (gslt_str_eq_cstr(olbl, "dl-src:comparison-greater")) op_ir = "D0Greater";
    else if (gslt_str_eq_cstr(olbl, "dl-src:comparison-greater-equal")) op_ir = "D0GreaterEqual";
    else {
      snprintf(err, err_cap, "D0Error: UnknownOperator");
      return false;
    }
    gslt_sb_append_cstr(a, sb, "(D0Compare ");
    gslt_sb_append_cstr(a, sb, op_ir);
    gslt_sb_append_char(a, sb, ' ');
    if (!gslt_d0_pkt_term(a, cch[0], sb, err, err_cap)) return false;
    gslt_sb_append_char(a, sb, ' ');
    if (!gslt_d0_pkt_term(a, cch[2], sb, err, err_cap)) return false;
    gslt_sb_append_char(a, sb, ')');
    return true;
  }
  snprintf(err, err_cap, "D0Error: UnknownPremise");
  return false;
}

static inline bool gslt_d0_pkt_body(GsltArena *a, const GsltSexpr *node,
                                    GsltStrBuf *sb, bool first, char *err, size_t err_cap) {
  GsltByteStr lbl;
  const GsltSexpr *fields = NULL;
  if (!gslt_packet_is_node(node, &lbl, &fields)) return false;
  const GsltSexpr **ch = NULL;
  uint32_t nch = 0;
  if (!gslt_d0_pkt_fields(a, fields, &ch, &nch)) return false;
  if (gslt_str_eq_cstr(lbl, "dl-src:body-one") && nch == 1) {
    if (!first) gslt_sb_append_char(a, sb, ' ');
    return gslt_d0_pkt_premise(a, ch[0], sb, err, err_cap);
  }
  if (gslt_str_eq_cstr(lbl, "dl-src:body-more") && nch == 2) {
    if (!first) gslt_sb_append_char(a, sb, ' ');
    if (!gslt_d0_pkt_premise(a, ch[0], sb, err, err_cap)) return false;
    return gslt_d0_pkt_body(a, ch[1], sb, false, err, err_cap);
  }
  snprintf(err, err_cap, "D0Error: UnknownBody");
  return false;
}

static inline bool gslt_d0_pkt_attributes(GsltArena *a, const GsltSexpr *node,
                                          GsltStrBuf *sb, bool first, char *err, size_t err_cap) {
  GsltByteStr lbl;
  const GsltSexpr *fields = NULL;
  if (!gslt_packet_is_node(node, &lbl, &fields)) return false;
  const GsltSexpr **ch = NULL;
  uint32_t nch = 0;
  if (!gslt_d0_pkt_fields(a, fields, &ch, &nch)) return false;
  if (gslt_str_eq_cstr(lbl, "dl-src:attributes-empty") && nch == 0) return true;
  if ((gslt_str_eq_cstr(lbl, "dl-src:attributes-one") && nch == 1) ||
      (gslt_str_eq_cstr(lbl, "dl-src:attributes-more") && nch == 2)) {
    GsltByteStr albl;
    const GsltSexpr *afields = NULL;
    if (!gslt_packet_is_node(ch[0], &albl, &afields) || !gslt_str_eq_cstr(albl, "dl-src:attr")) {
      snprintf(err, err_cap, "D0Error: UnknownAttribute");
      return false;
    }
    const GsltSexpr **ach = NULL;
    uint32_t nach = 0;
    if (!gslt_d0_pkt_fields(a, afields, &ach, &nach) || nach != 2) return false;
    GsltByteStr aname, tlbl;
    const GsltSexpr *tfields = NULL;
    if (!gslt_d0_pkt_text(a, ach[0], &aname) || !gslt_packet_is_node(ach[1], &tlbl, &tfields)) return false;
    const char *tir = NULL;
    if (gslt_str_eq_cstr(tlbl, "dl-src:type-symbol")) tir = "D0Symbol";
    else if (gslt_str_eq_cstr(tlbl, "dl-src:type-number")) tir = "D0Number";
    else if (gslt_str_eq_cstr(tlbl, "dl-src:type-unsigned")) tir = "D0Unsigned";
    else if (gslt_str_eq_cstr(tlbl, "dl-src:type-float")) tir = "D0Float";
    else {
      snprintf(err, err_cap, "D0Error: UnknownType");
      return false;
    }
    if (!first) gslt_sb_append_char(a, sb, ' ');
    gslt_sb_append_cstr(a, sb, "(D0Attribute ");
    gslt_sb_append_ir_quoted(a, sb, aname);
    gslt_sb_append_char(a, sb, ' ');
    gslt_sb_append_cstr(a, sb, tir);
    gslt_sb_append_char(a, sb, ')');
    if (nch == 2) {
      return gslt_d0_pkt_attributes(a, ch[1], sb, false, err, err_cap);
    }
    return true;
  }
  snprintf(err, err_cap, "D0Error: UnknownAttributes");
  return false;
}

static inline bool gslt_d0_pkt_declared_relations(GsltArena *a, const GsltSexpr *rel_node,
                                                  GsltByteStr attrs_str, GsltStrBuf *sb,
                                                  bool *io_first_stmt, char *err, size_t err_cap) {
  GsltByteStr lbl;
  const GsltSexpr *fields = NULL;
  if (!gslt_packet_is_node(rel_node, &lbl, &fields)) return false;
  const GsltSexpr **ch = NULL;
  uint32_t nch = 0;
  if (!gslt_d0_pkt_fields(a, fields, &ch, &nch)) return false;
  if ((gslt_str_eq_cstr(lbl, "dl-src:relations-one") && nch == 1) ||
      (gslt_str_eq_cstr(lbl, "dl-src:relations-more") && nch == 2)) {
    GsltByteStr rname;
    if (!gslt_d0_pkt_text(a, ch[0], &rname)) return false;
    if (!*io_first_stmt) gslt_sb_append_char(a, sb, ' ');
    *io_first_stmt = false;
    gslt_sb_append_cstr(a, sb, "(D0Declaration (");
    gslt_sb_append_ir_quoted(a, sb, rname);
    gslt_sb_append_cstr(a, sb, ") (");
    gslt_sb_append_bytes(a, sb, attrs_str.bytes, attrs_str.len);
    gslt_sb_append_cstr(a, sb, "))");
    if (nch == 2) {
      return gslt_d0_pkt_declared_relations(a, ch[1], attrs_str, sb, io_first_stmt, err, err_cap);
    }
    return true;
  }
  snprintf(err, err_cap, "D0Error: UnknownRelations");
  return false;
}

static inline bool gslt_d0_pkt_items(GsltArena *a, const GsltSexpr *node,
                                     GsltStrBuf *sb, bool *io_first_stmt,
                                     char *err, size_t err_cap) {
  GsltByteStr lbl;
  const GsltSexpr *fields = NULL;
  if (!gslt_packet_is_node(node, &lbl, &fields)) return false;
  const GsltSexpr **ch = NULL;
  uint32_t nch = 0;
  if (!gslt_d0_pkt_fields(a, fields, &ch, &nch)) return false;
  if (gslt_str_eq_cstr(lbl, "dl-src:items-empty") && nch == 0) return true;
  if (gslt_str_eq_cstr(lbl, "dl-src:items-more") && nch == 2) {
    const GsltSexpr *item = ch[0];
    GsltByteStr ilbl;
    const GsltSexpr *ifields = NULL;
    if (!gslt_packet_is_node(item, &ilbl, &ifields)) return false;
    const GsltSexpr **ich = NULL;
    uint32_t nich = 0;
    if (!gslt_d0_pkt_fields(a, ifields, &ich, &nich) || nich != 1) return false;

    if (gslt_str_eq_cstr(ilbl, "dl-src:item-declaration")) {
      GsltByteStr dlbl;
      const GsltSexpr *dfields = NULL;
      if (!gslt_packet_is_node(ich[0], &dlbl, &dfields) || !gslt_str_eq_cstr(dlbl, "dl-src:declaration")) {
        snprintf(err, err_cap, "D0Error: MalformedDeclaration");
        return false;
      }
      const GsltSexpr **dch = NULL;
      uint32_t ndch = 0;
      if (!gslt_d0_pkt_fields(a, dfields, &dch, &ndch) || ndch != 2) return false;
      GsltStrBuf asb;
      gslt_sb_init(a, &asb, 64);
      if (!gslt_d0_pkt_attributes(a, dch[1], &asb, true, err, err_cap)) return false;
      GsltByteStr astr = { asb.buf, (uint32_t)asb.len };
      if (!gslt_d0_pkt_declared_relations(a, dch[0], astr, sb, io_first_stmt, err, err_cap)) return false;
    } else if (gslt_str_eq_cstr(ilbl, "dl-src:item-fact")) {
      GsltByteStr flbl;
      const GsltSexpr *ffields = NULL;
      if (!gslt_packet_is_node(ich[0], &flbl, &ffields) || !gslt_str_eq_cstr(flbl, "dl-src:fact")) return false;
      const GsltSexpr **fch = NULL;
      uint32_t nfch = 0;
      if (!gslt_d0_pkt_fields(a, ffields, &fch, &nfch) || nfch != 1) return false;
      GsltByteStr glbl;
      const GsltSexpr *gfields = NULL;
      if (!gslt_packet_is_node(fch[0], &glbl, &gfields) || !gslt_str_eq_cstr(glbl, "dl-src:ground-atom")) return false;
      const GsltSexpr **gch = NULL;
      uint32_t ngch = 0;
      if (!gslt_d0_pkt_fields(a, gfields, &gch, &ngch) || ngch != 2) return false;
      if (!*io_first_stmt) gslt_sb_append_char(a, sb, ' ');
      *io_first_stmt = false;
      gslt_sb_append_cstr(a, sb, "(D0Fact (");
      if (!gslt_d0_pkt_qualified_name(a, gch[0], sb, err, err_cap)) return false;
      gslt_sb_append_cstr(a, sb, ") (");
      if (!gslt_d0_pkt_constants(a, gch[1], sb, true, err, err_cap)) return false;
      gslt_sb_append_cstr(a, sb, "))");
    } else if (gslt_str_eq_cstr(ilbl, "dl-src:item-rule")) {
      GsltByteStr rlbl;
      const GsltSexpr *rfields = NULL;
      if (!gslt_packet_is_node(ich[0], &rlbl, &rfields) || !gslt_str_eq_cstr(rlbl, "dl-src:rule")) return false;
      const GsltSexpr **rch = NULL;
      uint32_t nrch = 0;
      if (!gslt_d0_pkt_fields(a, rfields, &rch, &nrch) || nrch != 2) return false;
      if (!*io_first_stmt) gslt_sb_append_char(a, sb, ' ');
      *io_first_stmt = false;
      gslt_sb_append_cstr(a, sb, "(D0Rule ");
      if (!gslt_d0_pkt_atom(a, rch[0], sb, err, err_cap)) return false;
      gslt_sb_append_cstr(a, sb, " (");
      if (!gslt_d0_pkt_body(a, rch[1], sb, true, err, err_cap)) return false;
      gslt_sb_append_cstr(a, sb, "))");
    } else if (gslt_str_eq_cstr(ilbl, "dl-src:item-input") || gslt_str_eq_cstr(ilbl, "dl-src:item-output")) {
      bool is_in = gslt_str_eq_cstr(ilbl, "dl-src:item-input");
      GsltByteStr dlbl;
      const GsltSexpr *dfields = NULL;
      if (!gslt_packet_is_node(ich[0], &dlbl, &dfields)) return false;
      const GsltSexpr **dch = NULL;
      uint32_t ndch = 0;
      if (!gslt_d0_pkt_fields(a, dfields, &dch, &ndch) || ndch < 1) return false;
      if (!*io_first_stmt) gslt_sb_append_char(a, sb, ' ');
      *io_first_stmt = false;
      gslt_sb_append_cstr(a, sb, is_in ? "(D0Input (" : "(D0Output (");
      if (!gslt_d0_pkt_qualified_name(a, dch[0], sb, err, err_cap)) return false;
      gslt_sb_append_cstr(a, sb, "))");
    } else {
      snprintf(err, err_cap, "D0Error: UnknownItem");
      return false;
    }
    return gslt_d0_pkt_items(a, ch[1], sb, io_first_stmt, err, err_cap);
  }
  snprintf(err, err_cap, "D0Error: UnknownItems");
  return false;
}

static inline bool gslt_d0_packet_sexpr_to_ir_str(GsltArena *a, const GsltSexpr *pkt_sexpr,
                                                  uint32_t pkt_idx, GsltByteStr *out_ir,
                                                  GsltPacketProvenance *out_prov,
                                                  char *err, size_t err_cap) {
  const GsltSexpr *root = gslt_packet_unwrap_result(pkt_sexpr);
  if (!root) root = pkt_sexpr;
  GsltPacketProvenance prov;
  memset(&prov, 0, sizeof(prov));
  if (!gslt_packet_inspect(a, root, pkt_idx, &prov)) {
    snprintf(err, err_cap, "invalid D0 packet tree or scalar codepoint");
    return false;
  }
  if (out_prov) *out_prov = prov;
  GsltByteStr lbl;
  const GsltSexpr *fields = NULL;
  if (!gslt_packet_is_node(root, &lbl, &fields) || !gslt_str_eq_cstr(lbl, "dl-src:program")) {
    snprintf(err, err_cap, "D0Error: UnknownProgram");
    return false;
  }
  const GsltSexpr **ch = NULL;
  uint32_t nch = 0;
  if (!gslt_d0_pkt_fields(a, fields, &ch, &nch) || nch != 1) {
    snprintf(err, err_cap, "D0Error: UnknownProgram");
    return false;
  }
  GsltStrBuf sb;
  gslt_sb_init(a, &sb, 512);
  gslt_sb_append_cstr(a, &sb, "(D0Program (");
  bool first_stmt = true;
  if (!gslt_d0_pkt_items(a, ch[0], &sb, &first_stmt, err, err_cap)) return false;
  gslt_sb_append_cstr(a, &sb, "))");
  out_ir->bytes = sb.buf;
  out_ir->len = (uint32_t)sb.len;
  return true;
}

static inline bool gslt_d0_packet_to_ir_str(GsltArena *a, const char *src, size_t len,
                                            GsltByteStr *out_ir, GsltPacketProvenance *out_prov,
                                            char *err, size_t err_cap) {
  GsltSexpr *sexpr = gslt_sexpr_parse_all(a, src, len, err, err_cap);
  if (!sexpr) return false;
  return gslt_d0_packet_sexpr_to_ir_str(a, sexpr, 0, out_ir, out_prov, err, err_cap);
}

/* Multi-packet SourceValuesV1 catalogue reader for D0:
 * Verifies non-empty catalogue, lowers every packet to canonical (D0Program ...),
 * and requires exact semantic IR agreement across all parse trees! */
static inline bool gslt_d0_catalogue_to_ir_str(GsltArena *a, const char *src, size_t len,
                                               GsltByteStr *out_ir, uint32_t *out_npackets,
                                               GsltPacketProvenance **out_provs,
                                               char *err, size_t err_cap) {
  GsltSexpr *cat = gslt_sexpr_parse_all(a, src, len, err, err_cap);
  if (!cat) return false;
  if (cat->kind != GSLT_SEXPR_LIST || cat->nitems < 2 ||
      cat->items[0]->kind != GSLT_SEXPR_SYM ||
      !gslt_str_eq_cstr(cat->items[0]->text, "SourceValuesV1")) {
    snprintf(err, err_cap, "expected non-empty (SourceValuesV1 (result ...) ...) D0 catalogue");
    return false;
  }
  uint32_t npkts = cat->nitems - 1;
  GsltPacketProvenance *provs = (GsltPacketProvenance *)gslt_arena_alloc(a, npkts * sizeof(GsltPacketProvenance));
  GsltByteStr first_ir = { "", 0 };
  for (uint32_t i = 0; i < npkts; i++) {
    const GsltSexpr *pkt = cat->items[i + 1];
    if (!gslt_packet_unwrap_result(pkt)) {
      snprintf(err, err_cap, "D0 catalogue item %u is not a (result <node> nil) packet", i);
      return false;
    }
    GsltByteStr cur_ir = { "", 0 };
    if (!gslt_d0_packet_sexpr_to_ir_str(a, pkt, i, &cur_ir, &provs[i], err, err_cap)) {
      return false;
    }
    if (i == 0) {
      first_ir = cur_ir;
    } else if (!gslt_str_eq(first_ir, cur_ir)) {
      snprintf(err, err_cap,
               "ambiguous D0 SourceValuesV1 catalogue: packet %u lowers to a different D0Program than packet 0",
               i);
      return false;
    }
  }
  *out_ir = first_ir;
  if (out_npackets) *out_npackets = npkts;
  if (out_provs) *out_provs = provs;
  return true;
}

/* Lean Mettapedia.Languages.Datalog.IRCodec (Program [...]) -> (D0Program (...)) bridge */
static inline bool gslt_d0_lean_qname(GsltArena *a, const GsltSexpr *s, GsltStrBuf *sb) {
  /* Either (Relation (QualifiedName [parts...])) or (QualifiedName [parts...]) */
  const GsltSexpr *qn = s;
  if (qn->kind == GSLT_SEXPR_LIST && qn->nitems == 2 &&
      qn->items[0]->kind == GSLT_SEXPR_SYM && gslt_str_eq_cstr(qn->items[0]->text, "Relation")) {
    qn = qn->items[1];
  }
  if (qn->kind != GSLT_SEXPR_LIST || qn->nitems != 2 ||
      qn->items[0]->kind != GSLT_SEXPR_SYM || !gslt_str_eq_cstr(qn->items[0]->text, "QualifiedName") ||
      qn->items[1]->kind != GSLT_SEXPR_LIST) {
    return false;
  }
  const GsltSexpr *vec = qn->items[1];
  for (uint32_t i = 0; i < vec->nitems; i++) {
    if (i > 0) gslt_sb_append_char(a, sb, ' ');
    const GsltSexpr *p = vec->items[i];
    GsltByteStr txt = (p->kind == GSLT_SEXPR_LIST && p->nitems == 1) ? p->items[0]->text : p->text;
    gslt_sb_append_ir_quoted(a, sb, txt);
  }
  return true;
}

static inline bool gslt_d0_lean_val(GsltArena *a, const GsltSexpr *s, GsltStrBuf *sb) {
  if (s->kind != GSLT_SEXPR_LIST || s->nitems != 2 || s->items[0]->kind != GSLT_SEXPR_SYM) return false;
  GsltByteStr tag = s->items[0]->text;
  const GsltSexpr *pay = s->items[1];
  GsltByteStr txt = (pay->kind == GSLT_SEXPR_LIST && pay->nitems == 1) ? pay->items[0]->text : pay->text;
  if (gslt_str_eq_cstr(tag, "SymbolValue")) {
    gslt_sb_append_cstr(a, sb, "(D0SymbolValue ");
    gslt_sb_append_ir_quoted(a, sb, txt);
    gslt_sb_append_char(a, sb, ')');
    return true;
  }
  if (gslt_str_eq_cstr(tag, "IntegerValue")) {
    C0BigInt bi;
    int64_t iv = 0;
    if (!c0_bigint_parse_dec(txt.bytes, txt.len, &bi) || !c0_bigint_to_i64(&bi, &iv)) return false;
    /* Canonical decimal check matching IRCodec.integer? */
    char cbuf[64];
    snprintf(cbuf, sizeof(cbuf), "%" PRId64, iv);
    if (!gslt_str_eq_cstr(txt, cbuf)) return false;
    gslt_sb_append_cstr(a, sb, "(D0NumberValue ");
    gslt_sb_append_cstr(a, sb, cbuf);
    gslt_sb_append_char(a, sb, ')');
    return true;
  }
  if (gslt_str_eq_cstr(tag, "UnsignedValue")) {
    C0BigInt bi;
    uint64_t uv = 0;
    if (!c0_bigint_parse_dec(txt.bytes, txt.len, &bi) || !c0_bigint_to_u64(&bi, &uv)) return false;
    char cbuf[64];
    snprintf(cbuf, sizeof(cbuf), "%" PRIu64, uv);
    if (!gslt_str_eq_cstr(txt, cbuf)) return false;
    gslt_sb_append_cstr(a, sb, "(D0UnsignedValue ");
    gslt_sb_append_cstr(a, sb, cbuf);
    gslt_sb_append_char(a, sb, ')');
    return true;
  }
  return false;
}

static inline bool gslt_d0_lean_arg(GsltArena *a, const GsltSexpr *s, GsltStrBuf *sb) {
  if (s->kind == GSLT_SEXPR_SYM && gslt_str_eq_cstr(s->text, "AnonymousArgument")) {
    gslt_sb_append_cstr(a, sb, "D0Anonymous");
    return true;
  }
  if (s->kind != GSLT_SEXPR_LIST || s->nitems < 1 || s->items[0]->kind != GSLT_SEXPR_SYM) return false;
  GsltByteStr tag = s->items[0]->text;
  if (gslt_str_eq_cstr(tag, "AnonymousArgument") && s->nitems == 1) {
    gslt_sb_append_cstr(a, sb, "D0Anonymous");
    return true;
  }
  if (gslt_str_eq_cstr(tag, "ValueArgument") && s->nitems == 2) {
    gslt_sb_append_cstr(a, sb, "(D0Literal ");
    if (!gslt_d0_lean_val(a, s->items[1], sb)) return false;
    gslt_sb_append_char(a, sb, ')');
    return true;
  }
  if (gslt_str_eq_cstr(tag, "VariableArgument") && s->nitems == 2) {
    const GsltSexpr *v = s->items[1];
    GsltByteStr vname = v->text;
    if (v->kind == GSLT_SEXPR_LIST && v->nitems == 2 &&
        v->items[0]->kind == GSLT_SEXPR_SYM && gslt_str_eq_cstr(v->items[0]->text, "Variable")) {
      const GsltSexpr *vn = v->items[1];
      vname = (vn->kind == GSLT_SEXPR_LIST && vn->nitems == 1) ? vn->items[0]->text : vn->text;
    }
    gslt_sb_append_cstr(a, sb, "(D0Var ");
    gslt_sb_append_ir_quoted(a, sb, vname);
    gslt_sb_append_char(a, sb, ')');
    return true;
  }
  return false;
}

static inline bool gslt_d0_lean_ir_sexpr_to_d0_ir_str(GsltArena *a, const GsltSexpr *root,
                                                      GsltByteStr *out_ir, char *err, size_t err_cap) {
  if (root->kind != GSLT_SEXPR_LIST || root->nitems != 2 ||
      root->items[0]->kind != GSLT_SEXPR_SYM || !gslt_str_eq_cstr(root->items[0]->text, "Program") ||
      root->items[1]->kind != GSLT_SEXPR_LIST) {
    snprintf(err, err_cap, "expected Lean IRCodec (Program [...])");
    return false;
  }
  const GsltSexpr *stmts = root->items[1];
  GsltStrBuf sb;
  gslt_sb_init(a, &sb, 512);
  gslt_sb_append_cstr(a, &sb, "(D0Program (");
  for (uint32_t i = 0; i < stmts->nitems; i++) {
    if (i > 0) gslt_sb_append_char(a, &sb, ' ');
    const GsltSexpr *st = stmts->items[i];
    if (st->kind != GSLT_SEXPR_LIST || st->nitems < 2 || st->items[0]->kind != GSLT_SEXPR_SYM) {
      snprintf(err, err_cap, "invalid statement in Lean D0 IRCodec");
      return false;
    }
    GsltByteStr stag = st->items[0]->text;
    if (gslt_str_eq_cstr(stag, "Declaration") && st->nitems == 2) {
      const GsltSexpr *rd = st->items[1];
      if (rd->kind != GSLT_SEXPR_LIST || rd->nitems != 3 ||
          !gslt_str_eq_cstr(rd->items[0]->text, "RelationDeclaration") ||
          rd->items[2]->kind != GSLT_SEXPR_LIST) {
        snprintf(err, err_cap, "invalid RelationDeclaration in Lean D0 IRCodec");
        return false;
      }
      gslt_sb_append_cstr(a, &sb, "(D0Declaration (");
      if (!gslt_d0_lean_qname(a, rd->items[1], &sb)) return false;
      gslt_sb_append_cstr(a, &sb, ") (");
      const GsltSexpr *attrs = rd->items[2];
      for (uint32_t j = 0; j < attrs->nitems; j++) {
        if (j > 0) gslt_sb_append_char(a, &sb, ' ');
        const GsltSexpr *at = attrs->items[j];
        if (at->kind != GSLT_SEXPR_LIST || at->nitems != 3 ||
            !gslt_str_eq_cstr(at->items[0]->text, "Attribute")) return false;
        GsltByteStr aname = (at->items[1]->kind == GSLT_SEXPR_LIST && at->items[1]->nitems == 1)
                            ? at->items[1]->items[0]->text : at->items[1]->text;
        GsltByteStr atype = (at->items[2]->kind == GSLT_SEXPR_LIST && at->items[2]->nitems == 1)
                            ? at->items[2]->items[0]->text : at->items[2]->text;
        const char *dt = NULL;
        if (gslt_str_eq_cstr(atype, "SymbolType")) dt = "D0Symbol";
        else if (gslt_str_eq_cstr(atype, "NumberType")) dt = "D0Number";
        else if (gslt_str_eq_cstr(atype, "UnsignedType")) dt = "D0Unsigned";
        else if (gslt_str_eq_cstr(atype, "FloatType")) dt = "D0Float";
        else return false;
        gslt_sb_append_cstr(a, &sb, "(D0Attribute ");
        gslt_sb_append_ir_quoted(a, &sb, aname);
        gslt_sb_append_char(a, &sb, ' ');
        gslt_sb_append_cstr(a, &sb, dt);
        gslt_sb_append_char(a, &sb, ')');
      }
      gslt_sb_append_cstr(a, &sb, "))");
    } else if (gslt_str_eq_cstr(stag, "GroundFact") && st->nitems == 3) {
      gslt_sb_append_cstr(a, &sb, "(D0Fact (");
      if (!gslt_d0_lean_qname(a, st->items[1], &sb)) return false;
      gslt_sb_append_cstr(a, &sb, ") (");
      const GsltSexpr *gt = st->items[2];
      if (gt->kind != GSLT_SEXPR_LIST || gt->nitems != 2 ||
          !gslt_str_eq_cstr(gt->items[0]->text, "GroundTuple") ||
          gt->items[1]->kind != GSLT_SEXPR_LIST) return false;
      const GsltSexpr *vals = gt->items[1];
      for (uint32_t j = 0; j < vals->nitems; j++) {
        if (j > 0) gslt_sb_append_char(a, &sb, ' ');
        if (!gslt_d0_lean_val(a, vals->items[j], &sb)) return false;
      }
      gslt_sb_append_cstr(a, &sb, "))");
    } else if (gslt_str_eq_cstr(stag, "PositiveRule") && st->nitems == 2) {
      const GsltSexpr *cl = st->items[1];
      if (cl->kind != GSLT_SEXPR_LIST || cl->nitems != 4 ||
          !gslt_str_eq_cstr(cl->items[0]->text, "Clause") ||
          cl->items[3]->kind != GSLT_SEXPR_LIST) return false;
      const GsltSexpr *htup = cl->items[2];
      if (htup->kind != GSLT_SEXPR_LIST || htup->nitems != 2 ||
          !gslt_str_eq_cstr(htup->items[0]->text, "Tuple") ||
          htup->items[1]->kind != GSLT_SEXPR_LIST) return false;
      gslt_sb_append_cstr(a, &sb, "(D0Rule (D0Atom (");
      if (!gslt_d0_lean_qname(a, cl->items[1], &sb)) return false;
      gslt_sb_append_cstr(a, &sb, ") (");
      for (uint32_t j = 0; j < htup->items[1]->nitems; j++) {
        if (j > 0) gslt_sb_append_char(a, &sb, ' ');
        if (!gslt_d0_lean_arg(a, htup->items[1]->items[j], &sb)) return false;
      }
      gslt_sb_append_cstr(a, &sb, ")) (");
      const GsltSexpr *body = cl->items[3];
      for (uint32_t j = 0; j < body->nitems; j++) {
        if (j > 0) gslt_sb_append_char(a, &sb, ' ');
        const GsltSexpr *pr = body->items[j];
        if (pr->kind != GSLT_SEXPR_LIST || pr->nitems < 2) return false;
        if (gslt_str_eq_cstr(pr->items[0]->text, "PositiveAtom") && pr->nitems == 3) {
          const GsltSexpr *ptup = pr->items[2];
          if (ptup->kind != GSLT_SEXPR_LIST || ptup->nitems != 2 ||
              !gslt_str_eq_cstr(ptup->items[0]->text, "Tuple") ||
              ptup->items[1]->kind != GSLT_SEXPR_LIST) return false;
          gslt_sb_append_cstr(a, &sb, "(D0Positive (D0Atom (");
          if (!gslt_d0_lean_qname(a, pr->items[1], &sb)) return false;
          gslt_sb_append_cstr(a, &sb, ") (");
          for (uint32_t k = 0; k < ptup->items[1]->nitems; k++) {
            if (k > 0) gslt_sb_append_char(a, &sb, ' ');
            if (!gslt_d0_lean_arg(a, ptup->items[1]->items[k], &sb)) return false;
          }
          gslt_sb_append_cstr(a, &sb, ")))");
        } else if (gslt_str_eq_cstr(pr->items[0]->text, "Comparison") && pr->nitems == 2) {
          const GsltSexpr *cmp = pr->items[1];
          if (cmp->kind != GSLT_SEXPR_LIST || cmp->nitems != 3) return false;
          GsltByteStr ctag = cmp->items[0]->text;
          const char *cop = NULL;
          if (gslt_str_eq_cstr(ctag, "Equal")) cop = "D0Equal";
          else if (gslt_str_eq_cstr(ctag, "Different")) cop = "D0Different";
          else if (gslt_str_eq_cstr(ctag, "Less")) cop = "D0Less";
          else if (gslt_str_eq_cstr(ctag, "LessEqual")) cop = "D0LessEqual";
          else if (gslt_str_eq_cstr(ctag, "Greater")) cop = "D0Greater";
          else if (gslt_str_eq_cstr(ctag, "GreaterEqual")) cop = "D0GreaterEqual";
          else return false;
          gslt_sb_append_cstr(a, &sb, "(D0Compare ");
          gslt_sb_append_cstr(a, &sb, cop);
          gslt_sb_append_char(a, &sb, ' ');
          if (!gslt_d0_lean_arg(a, cmp->items[1], &sb)) return false;
          gslt_sb_append_char(a, &sb, ' ');
          if (!gslt_d0_lean_arg(a, cmp->items[2], &sb)) return false;
          gslt_sb_append_char(a, &sb, ')');
        } else {
          return false;
        }
      }
      gslt_sb_append_cstr(a, &sb, "))");
    } else if ((gslt_str_eq_cstr(stag, "InputRelation") || gslt_str_eq_cstr(stag, "OutputRelation")) && st->nitems == 2) {
      bool is_in = gslt_str_eq_cstr(stag, "InputRelation");
      gslt_sb_append_cstr(a, &sb, is_in ? "(D0Input (" : "(D0Output (");
      if (!gslt_d0_lean_qname(a, st->items[1], &sb)) return false;
      gslt_sb_append_cstr(a, &sb, "))");
    } else {
      snprintf(err, err_cap, "unknown statement '%.*s' in Lean D0 IRCodec",
               (int)stag.len, stag.bytes);
      return false;
    }
  }
  gslt_sb_append_cstr(a, &sb, "))");
  out_ir->bytes = sb.buf;
  out_ir->len = (uint32_t)sb.len;
  return true;
}

/* ---- D0 SyntaxGSLT Packet Synthesizer ((D0Program ...) -> (result (node dl-src:program ...) nil)) ---- */
static inline void gslt_d0_emit_pkt_text_leaf(GsltArena *a, GsltStrBuf *sb,
                                              const char *node_lbl, GsltByteStr text) {
  gslt_sb_append_cstr(a, sb, "(node ");
  gslt_sb_append_cstr(a, sb, node_lbl);
  gslt_sb_append_char(a, sb, ' ');
  for (uint32_t i = 0; i < text.len; i++) {
    gslt_sb_append_cstr(a, sb, "(pair (node dl-src:char (cp ");
    gslt_sb_append_u32(a, sb, (uint8_t)text.bytes[i]);
    gslt_sb_append_cstr(a, sb, ")) ");
  }
  gslt_sb_append_cstr(a, sb, "nil");
  for (uint32_t i = 0; i < text.len; i++) gslt_sb_append_char(a, sb, ')');
  gslt_sb_append_char(a, sb, ')');
}

static inline void gslt_d0_emit_pkt_qname(GsltArena *a, GsltStrBuf *sb, const GsltSexpr *qn) {
  for (uint32_t i = 0; i < qn->nitems; i++) {
    if (i + 1 < qn->nitems) {
      gslt_sb_append_cstr(a, sb, "(node dl-src:qualified-name-more (pair ");
      gslt_d0_emit_pkt_text_leaf(a, sb, "dl-src:identifier", qn->items[i]->text);
      gslt_sb_append_cstr(a, sb, " (pair ");
    } else {
      gslt_sb_append_cstr(a, sb, "(node dl-src:qualified-name-one (pair ");
      gslt_d0_emit_pkt_text_leaf(a, sb, "dl-src:identifier", qn->items[i]->text);
      gslt_sb_append_cstr(a, sb, " nil))");
    }
  }
  for (uint32_t i = 1; i < qn->nitems; i++) gslt_sb_append_cstr(a, sb, " nil)))");
}

static inline void gslt_d0_emit_pkt_constant(GsltArena *a, GsltStrBuf *sb, const GsltSexpr *val) {
  GsltByteStr vtag = val->items[0]->text;
  if (gslt_str_eq_cstr(vtag, "D0NumberValue")) {
    GsltByteStr txt = val->items[1]->text;
    if (txt.len > 0 && txt.bytes[0] == '-') {
      GsltByteStr mag = { txt.bytes + 1, txt.len - 1 };
      gslt_sb_append_cstr(a, sb, "(node dl-src:constant-integer (pair (node dl-src:integer-negative (pair ");
      gslt_d0_emit_pkt_text_leaf(a, sb, "dl-src:digits", mag);
      gslt_sb_append_cstr(a, sb, " nil)) nil))");
    } else {
      gslt_sb_append_cstr(a, sb, "(node dl-src:constant-integer (pair (node dl-src:integer-decimal (pair ");
      gslt_d0_emit_pkt_text_leaf(a, sb, "dl-src:digits", txt);
      gslt_sb_append_cstr(a, sb, " nil)) nil))");
    }
  } else if (gslt_str_eq_cstr(vtag, "D0UnsignedValue")) {
    gslt_sb_append_cstr(a, sb, "(node dl-src:constant-unsigned (pair (node dl-src:unsigned-decimal (pair ");
    gslt_d0_emit_pkt_text_leaf(a, sb, "dl-src:digits", val->items[1]->text);
    gslt_sb_append_cstr(a, sb, " nil)) nil))");
  } else {
    GsltByteStr txt = val->items[1]->text;
    gslt_sb_append_cstr(a, sb, "(node dl-src:constant-symbol (pair (node dl-src:symbol (pair ");
    uint32_t closes = 0;
    for (uint32_t i = 0; i < txt.len; i++) {
      uint8_t c = (uint8_t)txt.bytes[i];
      if (c == '"') {
        gslt_sb_append_cstr(a, sb, "(node dl-src:symbol-escape (pair (node dl-src:escape-quote nil) (pair ");
        closes++;
      } else if (c == '\\') {
        gslt_sb_append_cstr(a, sb, "(node dl-src:symbol-escape (pair (node dl-src:escape-slash nil) (pair ");
        closes++;
      } else if (c == '\n') {
        gslt_sb_append_cstr(a, sb, "(node dl-src:symbol-escape (pair (node dl-src:escape-newline nil) (pair ");
        closes++;
      } else if (c == '\t') {
        gslt_sb_append_cstr(a, sb, "(node dl-src:symbol-escape (pair (node dl-src:escape-tab nil) (pair ");
        closes++;
      } else {
        gslt_sb_append_cstr(a, sb, "(node dl-src:symbol-body (pair (node dl-src:char (cp ");
        gslt_sb_append_u32(a, sb, c);
        gslt_sb_append_cstr(a, sb, ")) (pair ");
        closes++;
      }
    }
    gslt_sb_append_cstr(a, sb, "(node dl-src:symbol-empty nil)");
    for (uint32_t i = 0; i < closes; i++) gslt_sb_append_cstr(a, sb, " nil)))");
    gslt_sb_append_cstr(a, sb, " nil)) nil))");
  }
}

static inline void gslt_d0_emit_pkt_term(GsltArena *a, GsltStrBuf *sb, const GsltSexpr *t) {
  if (t->kind == GSLT_SEXPR_SYM && gslt_str_eq_cstr(t->text, "D0Anonymous")) {
    gslt_sb_append_cstr(a, sb, "(node dl-src:term-anonymous nil)");
    return;
  }
  GsltByteStr tag = t->items[0]->text;
  if (gslt_str_eq_cstr(tag, "D0Var")) {
    gslt_sb_append_cstr(a, sb, "(node dl-src:term-variable (pair ");
    gslt_d0_emit_pkt_text_leaf(a, sb, "dl-src:identifier", t->items[1]->text);
    gslt_sb_append_cstr(a, sb, " nil))");
  } else {
    gslt_sb_append_cstr(a, sb, "(node dl-src:term-constant (pair ");
    gslt_d0_emit_pkt_constant(a, sb, t->items[1]);
    gslt_sb_append_cstr(a, sb, " nil))");
  }
}

static inline void gslt_d0_emit_pkt_atom(GsltArena *a, GsltStrBuf *sb, const GsltSexpr *at) {
  const GsltSexpr *qn = at->items[1];
  const GsltSexpr *args = at->items[2];
  gslt_sb_append_cstr(a, sb, "(node dl-src:atom (pair ");
  gslt_d0_emit_pkt_qname(a, sb, qn);
  gslt_sb_append_cstr(a, sb, " (pair ");
  if (args->nitems == 0) {
    gslt_sb_append_cstr(a, sb, "(node dl-src:terms-empty nil)");
  } else {
    for (uint32_t i = 0; i < args->nitems; i++) {
      if (i + 1 < args->nitems) {
        gslt_sb_append_cstr(a, sb, "(node dl-src:terms-more (pair ");
        gslt_d0_emit_pkt_term(a, sb, args->items[i]);
        gslt_sb_append_cstr(a, sb, " (pair ");
      } else {
        gslt_sb_append_cstr(a, sb, "(node dl-src:terms-one (pair ");
        gslt_d0_emit_pkt_term(a, sb, args->items[i]);
        gslt_sb_append_cstr(a, sb, " nil))");
      }
    }
    for (uint32_t i = 1; i < args->nitems; i++) gslt_sb_append_cstr(a, sb, " nil)))");
  }
  gslt_sb_append_cstr(a, sb, " nil)))");
}

static inline GsltByteStr gslt_d0_ir_to_packet_str(GsltArena *a, const char *ir_src, size_t ir_len,
                                                   char *err, size_t err_cap) {
  GsltByteStr empty = { "", 0 };
  GsltSexpr *root = gslt_sexpr_parse_all(a, ir_src, ir_len, err, err_cap);
  if (!root || root->kind != GSLT_SEXPR_LIST || root->nitems != 2 ||
      !gslt_str_eq_cstr(root->items[0]->text, "D0Program") ||
      root->items[1]->kind != GSLT_SEXPR_LIST) {
    snprintf(err, err_cap, "expected (D0Program ...) for packet synthesis");
    return empty;
  }
  const GsltSexpr *stmts = root->items[1];
  GsltStrBuf sb;
  gslt_sb_init(a, &sb, 1024);
  gslt_sb_append_cstr(a, &sb, "(result (node dl-src:program (pair ");
  for (uint32_t i = 0; i < stmts->nitems; i++) {
    const GsltSexpr *st = stmts->items[i];
    GsltByteStr stag = st->items[0]->text;
    gslt_sb_append_cstr(a, &sb, "(node dl-src:items-more (pair ");
    if (gslt_str_eq_cstr(stag, "D0Declaration")) {
      const GsltSexpr *qn = st->items[1];
      const GsltSexpr *attrs = st->items[2];
      gslt_sb_append_cstr(a, &sb, "(node dl-src:item-declaration (pair (node dl-src:declaration (pair (node dl-src:relations-one (pair ");
      gslt_d0_emit_pkt_text_leaf(a, &sb, "dl-src:identifier", qn->items[0]->text);
      gslt_sb_append_cstr(a, &sb, " nil)) (pair ");
      if (attrs->nitems == 0) {
        gslt_sb_append_cstr(a, &sb, "(node dl-src:attributes-empty nil)");
      } else {
        for (uint32_t j = 0; j < attrs->nitems; j++) {
          const GsltSexpr *at = attrs->items[j];
          const char *tlbl = "dl-src:type-symbol";
          if (gslt_str_eq_cstr(at->items[2]->text, "D0Number")) tlbl = "dl-src:type-number";
          else if (gslt_str_eq_cstr(at->items[2]->text, "D0Unsigned")) tlbl = "dl-src:type-unsigned";
          else if (gslt_str_eq_cstr(at->items[2]->text, "D0Float")) tlbl = "dl-src:type-float";
          gslt_sb_append_cstr(a, &sb, (j + 1 < attrs->nitems) ? "(node dl-src:attributes-more (pair " : "(node dl-src:attributes-one (pair ");
          gslt_sb_append_cstr(a, &sb, "(node dl-src:attr (pair ");
          gslt_d0_emit_pkt_text_leaf(a, &sb, "dl-src:identifier", at->items[1]->text);
          gslt_sb_append_cstr(a, &sb, " (pair (node ");
          gslt_sb_append_cstr(a, &sb, tlbl);
          gslt_sb_append_cstr(a, &sb, " nil) nil)))");
          gslt_sb_append_cstr(a, &sb, (j + 1 < attrs->nitems) ? " (pair " : " nil))");
        }
        for (uint32_t j = 1; j < attrs->nitems; j++) gslt_sb_append_cstr(a, &sb, " nil)))");
      }
      gslt_sb_append_cstr(a, &sb, " nil))) nil))");
    } else if (gslt_str_eq_cstr(stag, "D0Fact")) {
      const GsltSexpr *qn = st->items[1];
      const GsltSexpr *vals = st->items[2];
      gslt_sb_append_cstr(a, &sb, "(node dl-src:item-fact (pair (node dl-src:fact (pair (node dl-src:ground-atom (pair ");
      gslt_d0_emit_pkt_qname(a, &sb, qn);
      gslt_sb_append_cstr(a, &sb, " (pair ");
      if (vals->nitems == 0) {
        gslt_sb_append_cstr(a, &sb, "(node dl-src:constants-empty nil)");
      } else {
        for (uint32_t j = 0; j < vals->nitems; j++) {
          gslt_sb_append_cstr(a, &sb, (j + 1 < vals->nitems) ? "(node dl-src:constants-more (pair " : "(node dl-src:constants-one (pair ");
          gslt_d0_emit_pkt_constant(a, &sb, vals->items[j]);
          gslt_sb_append_cstr(a, &sb, (j + 1 < vals->nitems) ? " (pair " : " nil))");
        }
        for (uint32_t j = 1; j < vals->nitems; j++) gslt_sb_append_cstr(a, &sb, " nil)))");
      }
      gslt_sb_append_cstr(a, &sb, " nil))) nil)) nil))");
    } else if (gslt_str_eq_cstr(stag, "D0Rule")) {
      const GsltSexpr *hd = st->items[1];
      const GsltSexpr *body = st->items[2];
      gslt_sb_append_cstr(a, &sb, "(node dl-src:item-rule (pair (node dl-src:rule (pair ");
      gslt_d0_emit_pkt_atom(a, &sb, hd);
      gslt_sb_append_cstr(a, &sb, " (pair ");
      for (uint32_t j = 0; j < body->nitems; j++) {
        const GsltSexpr *pr = body->items[j];
        gslt_sb_append_cstr(a, &sb, (j + 1 < body->nitems) ? "(node dl-src:body-more (pair " : "(node dl-src:body-one (pair ");
        if (gslt_str_eq_cstr(pr->items[0]->text, "D0Positive")) {
          gslt_sb_append_cstr(a, &sb, "(node dl-src:positive-atom (pair ");
          gslt_d0_emit_pkt_atom(a, &sb, pr->items[1]);
          gslt_sb_append_cstr(a, &sb, " nil))");
        } else {
          const char *olbl = "dl-src:comparison-equal";
          if (gslt_str_eq_cstr(pr->items[1]->text, "D0Different")) olbl = "dl-src:comparison-different";
          else if (gslt_str_eq_cstr(pr->items[1]->text, "D0Less")) olbl = "dl-src:comparison-less";
          else if (gslt_str_eq_cstr(pr->items[1]->text, "D0LessEqual")) olbl = "dl-src:comparison-less-equal";
          else if (gslt_str_eq_cstr(pr->items[1]->text, "D0Greater")) olbl = "dl-src:comparison-greater";
          else if (gslt_str_eq_cstr(pr->items[1]->text, "D0GreaterEqual")) olbl = "dl-src:comparison-greater-equal";
          gslt_sb_append_cstr(a, &sb, "(node dl-src:positive-comparison (pair (node dl-src:comparison (pair ");
          gslt_d0_emit_pkt_term(a, &sb, pr->items[2]);
          gslt_sb_append_cstr(a, &sb, " (pair (node ");
          gslt_sb_append_cstr(a, &sb, olbl);
          gslt_sb_append_cstr(a, &sb, " nil) (pair ");
          gslt_d0_emit_pkt_term(a, &sb, pr->items[3]);
          gslt_sb_append_cstr(a, &sb, " nil)))) nil))");
        }
        gslt_sb_append_cstr(a, &sb, (j + 1 < body->nitems) ? " (pair " : " nil))");
      }
      for (uint32_t j = 1; j < body->nitems; j++) gslt_sb_append_cstr(a, &sb, " nil)))");
      gslt_sb_append_cstr(a, &sb, " nil))) nil))");
    } else if (gslt_str_eq_cstr(stag, "D0Input") || gslt_str_eq_cstr(stag, "D0Output")) {
      bool is_in = gslt_str_eq_cstr(stag, "D0Input");
      gslt_sb_append_cstr(a, &sb, is_in
          ? "(node dl-src:item-input (pair (node dl-src:input (pair "
          : "(node dl-src:item-output (pair (node dl-src:output (pair ");
      gslt_d0_emit_pkt_qname(a, &sb, st->items[1]);
      gslt_sb_append_cstr(a, &sb, " nil)) nil))");
    }
    gslt_sb_append_cstr(a, &sb, " (pair ");
  }
  gslt_sb_append_cstr(a, &sb, "(node dl-src:items-empty nil)");
  for (uint32_t i = 0; i < stmts->nitems; i++) gslt_sb_append_cstr(a, &sb, " nil)))");
  gslt_sb_append_cstr(a, &sb, " nil)) nil)");
  GsltByteStr out = { sb.buf, (uint32_t)sb.len };
  return out;
}

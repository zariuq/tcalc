/* Semantic mutator for HOLRPLY1 streams.
 *
 * usage: mutate_holr IN.holr OUT.holr RECORD ARG DELTA
 *        mutate_holr IN.holr --count
 *        mutate_holr IN.holr --show RECORD
 *
 * Adds DELTA to the ARG-th numeric operand (0-based, counting every identifier
 * operand of the record in order, list elements included) of record number RECORD
 * (0-based), re-encodes the stream and recomputes the END record's checksum, so the
 * mutant is a well-formed stream that differs in exactly one reference.  Exit status
 * 3 when RECORD has no such operand or the result would be negative.  `--count`
 * prints the number of records before END.
 *
 * Record layouts follow the format's operation table: N name id, Y type id, T term id,
 * H theorem id, u plain number, b byte string, *X list, %XY list of pairs, c checksum. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct { unsigned char op; const char *layout; } Op;
static const Op ops[] = {
  {0x01, "b"}, {0x02, "N"}, {0x03, "N*Y"}, {0x04, "NY"}, {0x05, "NY"}, {0x06, "TT"}, {0x07, "TT"},
  {0x10, "T"}, {0x11, "HH"}, {0x12, "HH"}, {0x13, "TH"}, {0x14, "T"}, {0x15, "T"}, {0x16, "HH"},
  {0x17, "HH"}, {0x18, "%YYH"}, {0x19, "%TTH"},
  {0x20, "Nu"}, {0x21, "NY"}, {0x22, "T"}, {0x23, "T"}, {0x24, "NNNH"}, {0x25, "u"},
  {0x30, "H*TT"}, {0x31, "HN"}, {0x32, "H"}, {0x33, ""}, {0x34, "H*H"}, {0x35, "H*TT"},
  {0x40, "y"}, {0x41, "t"}, {0x42, "h"}, {0x7f, "uc"}
};

static unsigned char *in, *out;
static size_t in_len, pos, out_len;

static const char *layout_of(unsigned char op) {
  for (size_t i = 0; i < sizeof ops / sizeof ops[0]; i++) if (ops[i].op == op) return ops[i].layout;
  return NULL;
}
static uint64_t get_uv(void) {
  uint64_t v = 0;
  for (unsigned i = 0; i < 9 && pos < in_len; i++) {
    unsigned char b = in[pos++];
    v |= (uint64_t)(b & 0x7f) << (7 * i);
    if (!(b & 0x80)) return v;
  }
  fprintf(stderr, "bad number at byte %zu\n", pos); exit(2);
}
static void put_uv(uint64_t v) {
  do { unsigned char b = v & 0x7f; v >>= 7; if (v) b |= 0x80; out[out_len++] = b; } while (v);
}

int main(int argc, char **argv) {
  if (argc != 3 && argc != 4 && argc != 6) {
    fprintf(stderr, "usage: %s IN OUT RECORD ARG DELTA | IN --count | IN --show RECORD\n", argv[0]);
    return 2;
  }
  long show_rec = (argc == 4) ? atol(argv[3]) : -1;
  FILE *f = fopen(argv[1], "rb");
  if (!f) { perror(argv[1]); return 2; }
  fseek(f, 0, SEEK_END); in_len = (size_t)ftell(f); fseek(f, 0, SEEK_SET);
  in = malloc(in_len + 1); out = malloc(in_len + 64);
  if (fread(in, 1, in_len, f) != in_len) { fprintf(stderr, "short read\n"); return 2; }
  fclose(f);
  int count_only = (argc == 3 || argc == 4);
  long want_rec = count_only ? -1 : atol(argv[3]);
  long want_arg = count_only ? -1 : atol(argv[4]);
  long delta = count_only ? 0 : atol(argv[5]);
  int done = 0;

  pos = 40; memcpy(out, in, 40); out_len = 40;
  for (int i = 0; i < 4; i++) put_uv(get_uv());      /* version, profile, policy, flags */
  long rec = 0;
  while (pos < in_len) {
    unsigned char op = in[pos++];
    const char *lay = layout_of(op);
    if (!lay) { fprintf(stderr, "unknown operation 0x%02x at record %ld\n", op, rec); return 2; }
    if (op == 0x7f) {
      uint64_t n = get_uv();
      uint64_t h = 0xcbf29ce484222325ULL;
      for (size_t i = 0; i < out_len; i++) { h ^= out[i]; h *= 0x100000001b3ULL; }
      out[out_len++] = op; put_uv(n);
      for (int i = 0; i < 8; i++) out[out_len++] = (unsigned char)(h >> (8 * i));
      break;
    }
    out[out_len++] = op;
    long arg = 0;
    if (show_rec == rec) printf("record %ld: operation 0x%02x layout \"%s\" operands:", rec, op, lay);
    for (const char *p = lay; *p; p++) {
      if (*p == 'b') {
        uint64_t n = get_uv(); put_uv(n);
        memcpy(out + out_len, in + pos, n); out_len += n; pos += n;
      } else if (*p == '*' || *p == '%') {
        int pairs = (*p == '%');
        p += pairs ? 2 : 1;
        uint64_t n = get_uv(); put_uv(n);
        for (uint64_t i = 0; i < (pairs ? 2 * n : n); i++) {
          uint64_t v = get_uv();
          if (show_rec == rec) printf(" %llu", (unsigned long long)v);
          if (rec == want_rec && arg == want_arg) {
            if ((long)v + delta < 0) return 3;
            v = (uint64_t)((long)v + delta); done = 1;
          }
          arg++; put_uv(v);
        }
      } else {
        uint64_t v = get_uv();
        if (show_rec == rec) printf(" %llu", (unsigned long long)v);
        if (*p != 'u') {
          if (rec == want_rec && arg == want_arg) {
            if ((long)v + delta < 0) return 3;
            v = (uint64_t)((long)v + delta); done = 1;
          }
          arg++;
        }
        put_uv(v);
      }
    }
    if (show_rec == rec) printf("\n");
    rec++;
  }
  if (show_rec >= 0) return 0;
  if (count_only) { printf("%ld\n", rec); return 0; }
  if (!done) return 3;
  f = fopen(argv[2], "wb");
  if (!f || fwrite(out, 1, out_len, f) != out_len) { perror(argv[2]); return 2; }
  fclose(f);
  return 0;
}

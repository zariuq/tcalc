/* test_callbacks: differential harness for the five binary callbacks
 * add64, sub64, and64, or64, xor64 (bool fn(const uint64_t *in, uint64_t *out),
 * 34 bytes each: ENDBR64 and the 30-byte body).
 *
 *   test_callbacks DIR [N [SEED]]
 *
 * Loads DIR/NAME.bin, checks its 34 bytes against the bytes below (the ones
 * the HOL proofs state), and runs each image from its own executable page:
 *   - called through a C function pointer, bool fn(const uint64_t *, uint64_t *):
 *     the result is true and out[0] is the C reference on uint64_t;
 *   - called through cb_probe, which loads every general register with a
 *     random pattern first: RAX = 1 (the whole register), out[0] is the
 *     reference, and RBX RCX RSI RDI RBP R8..R15, RSP and every RFLAGS bit
 *     other than CF PF AF ZF SF OF are as they were (RDX is not checked:
 *     the contract lets it change);
 *   - in both: in[0], in[1] and the words on either side of out[0] unchanged.
 * Inputs: all pairs of 16 edge values, then N random pairs (default 200000)
 * from a splitmix64 stream (default seed 0x5EED).
 * Controls: add64's bytes with the ALU byte 0x01 replaced by sub's 0x29 must
 * miss add64's reference on some input (the first miss is printed); a stub
 * that clears RCX and writes out[1] must show both changes through the probe.
 * Exit status 0 when every check holds and both controls come out as said.
 */
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

extern uint64_t cb_probe(void *fn, const uint64_t *in, uint64_t *out,
                         const uint64_t *pre, uint64_t *post);

enum { NOPS = 5, LEN = 34, ALU = 19 };
static const char *names[NOPS] = {"add64", "sub64", "and64", "or64", "xor64"};
static const unsigned char alu[NOPS] = {0x01, 0x29, 0x21, 0x09, 0x31};
static const unsigned char body[LEN] = {
    0xf3, 0x0f, 0x1e, 0xfa,                   /* endbr64 */
    0x48, 0x8b, 0x87, 0x00, 0x00, 0x00, 0x00, /* mov rax, [rdi+0] */
    0x48, 0x8b, 0x97, 0x08, 0x00, 0x00, 0x00, /* mov rdx, [rdi+8] */
    0x48, 0x00, 0xd0,                         /* op rax, rdx (byte 19 = ALU) */
    0x48, 0x89, 0x86, 0x00, 0x00, 0x00, 0x00, /* mov [rsi+0], rax */
    0xb8, 0x01, 0x00, 0x00, 0x00,             /* mov eax, 1 */
    0xc3};                                    /* ret */

static uint64_t reference(int op, uint64_t x, uint64_t y) {
  switch (op) {
  case 0: return x + y;
  case 1: return x - y;
  case 2: return x & y;
  case 3: return x | y;
  default: return x ^ y;
  }
}

static uint64_t rng;
static uint64_t next(void) {
  uint64_t z = (rng += 0x9E3779B97F4A7C15ull);
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
  z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
  return z ^ (z >> 31);
}

static void *load_page(const unsigned char *bytes) {
  long pg = sysconf(_SC_PAGESIZE);
  unsigned char *p = mmap(NULL, (size_t)pg, PROT_READ | PROT_WRITE,
                          MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (p == MAP_FAILED) { perror("mmap"); exit(2); }
  memset(p, 0xcc, (size_t)pg);
  memcpy(p, bytes, LEN);
  if (mprotect(p, (size_t)pg, PROT_READ | PROT_EXEC) != 0) { perror("mprotect"); exit(2); }
  return p;
}

static void read_bin(const char *dir, const char *name, unsigned char *out) {
  char path[4096];
  snprintf(path, sizeof path, "%s/%s.bin", dir, name);
  FILE *f = fopen(path, "rb");
  if (!f) { perror(path); exit(2); }
  unsigned char extra;
  size_t n = fread(out, 1, LEN, f);
  if (n != LEN || fread(&extra, 1, 1, f) != 0) {
    fprintf(stderr, "%s: not %d bytes\n", path, LEN); exit(2);
  }
  fclose(f);
}

typedef bool (*callback)(const uint64_t *, uint64_t *);

static const uint64_t S_LO = 0xA5A5A5A5DEADBEEFull, S_HI = 0x5A5A5A5AFEEDFACEull;
enum { FLAGS_ARITH = 0x8D5 }; /* CF PF AF ZF SF OF */

/* One input through both calling routes; returns the number of failed checks
   (0 or more), printing the first few. */
static long failures, printed;
static void fail(const char *name, const char *what, uint64_t x, uint64_t y,
                 uint64_t got, uint64_t want) {
  failures++;
  if (printed++ < 20)
    printf("FAIL %s %s: x=%016llx y=%016llx got=%016llx want=%016llx\n", name, what,
           (unsigned long long)x, (unsigned long long)y,
           (unsigned long long)got, (unsigned long long)want);
}

static void check(int op, void *page, uint64_t x, uint64_t y) {
  const char *name = names[op];
  uint64_t want = reference(op, x, y);
  _Alignas(16) uint64_t inb[4] = {S_LO, x, y, S_HI};
  _Alignas(16) uint64_t outb[4] = {S_LO, next(), S_HI, S_LO};
  bool r = ((callback)page)(&inb[1], &outb[1]);
  if (!r) fail(name, "bool result", x, y, r, 1);
  if (outb[1] != want) fail(name, "out[0] (pointer call)", x, y, outb[1], want);
  if (inb[0] != S_LO || inb[1] != x || inb[2] != y || inb[3] != S_HI)
    fail(name, "input words changed (pointer call)", x, y, inb[1], x);
  if (outb[0] != S_LO || outb[2] != S_HI || outb[3] != S_LO)
    fail(name, "words beside out[0] changed (pointer call)", x, y, outb[2], S_HI);

  uint64_t pre[13], post[19];
  for (int i = 0; i < 13; i++) pre[i] = next();
  outb[1] = next();
  cb_probe(page, &inb[1], &outb[1], pre, post);
  if (post[0] != 1) fail(name, "RAX", x, y, post[0], 1);
  if (outb[1] != want) fail(name, "out[0] (probe)", x, y, outb[1], want);
  /* post: rax rbx rcx rdx rsi rdi rbp r8..r15; pre: rbx rbp r8..r15 rax rdx rcx */
  if (post[1] != pre[0]) fail(name, "RBX", x, y, post[1], pre[0]);
  if (post[2] != pre[12]) fail(name, "RCX", x, y, post[2], pre[12]);
  if (post[4] != (uint64_t)(uintptr_t)&outb[1]) fail(name, "RSI", x, y, post[4], (uintptr_t)&outb[1]);
  if (post[5] != (uint64_t)(uintptr_t)&inb[1]) fail(name, "RDI", x, y, post[5], (uintptr_t)&inb[1]);
  if (post[6] != pre[1]) fail(name, "RBP", x, y, post[6], pre[1]);
  for (int k = 0; k < 8; k++)
    if (post[7 + k] != pre[2 + k]) fail(name, "R8..R15", x, y, post[7 + k], pre[2 + k]);
  if (post[16] != post[15]) fail(name, "RSP", x, y, post[16], post[15]);
  if (((post[17] ^ post[18]) & ~(uint64_t)FLAGS_ARITH) != 0)
    fail(name, "RFLAGS outside CF PF AF ZF SF OF", x, y, post[18], post[17]);
  if (inb[0] != S_LO || inb[1] != x || inb[2] != y || inb[3] != S_HI)
    fail(name, "input words changed (probe)", x, y, inb[1], x);
  if (outb[0] != S_LO || outb[2] != S_HI || outb[3] != S_LO)
    fail(name, "words beside out[0] changed (probe)", x, y, outb[2], S_HI);
}

/* The probe's own control: a stub that clears RCX and writes the word after
   out[0] must show both changes, or the register and memory checks above
   would be vacuous. */
static bool probe_selftest(void) {
  static const unsigned char stub[LEN] = {
      0xf3, 0x0f, 0x1e, 0xfa,       /* endbr64 */
      0x48, 0x31, 0xc9,             /* xor rcx, rcx */
      0x48, 0x89, 0x46, 0x08,       /* mov [rsi+8], rax */
      0xb8, 0x01, 0x00, 0x00, 0x00, /* mov eax, 1 */
      0xc3};                        /* ret (the rest is padding) */
  void *p = load_page(stub);
  _Alignas(16) uint64_t inb[2] = {1, 2}, outb[2] = {0, S_HI};
  uint64_t pre[13], post[19];
  for (int i = 0; i < 13; i++) pre[i] = next() | 1;
  cb_probe(p, inb, outb, pre, post);
  bool rcx_seen = post[2] != pre[12], beside_seen = outb[1] != S_HI;
  printf("probe control (stub clearing RCX and writing out[1]): RCX change %s, out[1] change %s\n",
         rcx_seen ? "detected" : "MISSED", beside_seen ? "detected" : "MISSED");
  return rcx_seen && beside_seen;
}

static void cet_state(void) {
  FILE *f = fopen("/proc/self/status", "r");
  char line[256];
  bool seen = false;
  if (f) {
    while (fgets(line, sizeof line, f))
      if (!strncmp(line, "x86_Thread_features", 19)) {
        line[strcspn(line, "\n")] = 0;
        printf("cet: %s\n", line);
        seen = true;
      }
    fclose(f);
  }
  if (!seen) printf("cet: no x86_Thread_features in /proc/self/status\n");
}

static const uint64_t edge[16] = {
    0, 1, 2, 3, 0x7f, 0x80, 0xff, 0x100,
    0x7fffffffffffffffull, 0x8000000000000000ull, 0xfffffffffffffffeull,
    0xffffffffffffffffull, 0x5555555555555555ull, 0xaaaaaaaaaaaaaaaaull,
    0x0123456789abcdefull, 0xfedcba9876543210ull};

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: %s DIR [N [SEED]]\n", argv[0]); return 2; }
  long n = argc > 2 ? strtol(argv[2], NULL, 0) : 200000;
  rng = argc > 3 ? strtoull(argv[3], NULL, 0) : 0x5EED;
  printf("seed 0x%llx, %ld random pairs per image, 256 edge pairs\n",
         (unsigned long long)rng, n);
  cet_state();
  bool probe_ok = probe_selftest();
  void *pages[NOPS];
  for (int op = 0; op < NOPS; op++) {
    unsigned char want[LEN], got[LEN];
    memcpy(want, body, LEN);
    want[ALU] = alu[op];
    read_bin(argv[1], names[op], got);
    if (memcmp(want, got, LEN) != 0) {
      printf("FAIL %s.bin: bytes differ from the proved bytes\n", names[op]);
      return 1;
    }
    pages[op] = load_page(got);
  }
  for (int op = 0; op < NOPS; op++) {
    long before = failures, calls = 0;
    for (int i = 0; i < 16; i++)
      for (int j = 0; j < 16; j++) { check(op, pages[op], edge[i], edge[j]); calls++; }
    for (long k = 0; k < n; k++) {
      uint64_t x = next(), y = next();
      switch (k & 3) { /* also results 0 and carries/borrows at the edges */
      case 1: y = (uint64_t)0 - x; break;
      case 2: y = x; break;
      default: break;
      }
      check(op, pages[op], x, y);
      calls++;
    }
    printf("%s: %ld inputs, each by pointer and by probe; failures %ld\n", names[op],
           calls, failures - before);
  }
  /* Control: add64 with sub's ALU byte must miss add64's reference. */
  unsigned char mut[LEN];
  memcpy(mut, body, LEN);
  mut[ALU] = alu[1];
  void *mp = load_page(mut);
  long misses = 0, tried = 0;
  uint64_t fx = 0, fy = 0, fgot = 0;
  for (int i = 0; i < 16; i++)
    for (int j = 0; j < 16; j++) {
      _Alignas(16) uint64_t in[2] = {edge[i], edge[j]}, out[1] = {0};
      ((callback)mp)(in, out);
      tried++;
      if (out[0] != reference(0, edge[i], edge[j])) {
        if (misses++ == 0) { fx = edge[i]; fy = edge[j]; fgot = out[0]; }
      }
    }
  if (misses > 0)
    printf("control add64-with-0x29: refused, %ld of %ld edge inputs miss add64's reference;"
           " first x=%016llx y=%016llx gives %016llx, add64 wants %016llx\n",
           misses, tried, (unsigned long long)fx, (unsigned long long)fy,
           (unsigned long long)fgot, (unsigned long long)reference(0, fx, fy));
  else
    printf("control add64-with-0x29: ACCEPTED (wrong)\n");
  printf("TOTAL failures %ld, control %s, probe control %s\n", failures,
         misses > 0 ? "refused" : "ACCEPTED", probe_ok ? "ok" : "FAILED");
  return (failures == 0 && misses > 0 && probe_ok) ? 0 : 1;
}

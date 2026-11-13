/* admission_native.c: the proved native producers add64, sub64, and64, or64, xor64 (tisa/native_alu.S)
   in the sealed function registry: their bytes, their registration, and the kernel's call into them.
   Built twice: as admission_native, and with -DTISA_NATIVE_ALU_PATCHED (one byte of add64's .text copy
   changed), where registration must refuse. Each check prints "holds" or "VIOLATED"; exit 1 if any is
   violated, 2 if a scene could not be set up.
   usage: admission_native [SHA256SUMS]   (default tisa/native_alu/SHA256SUMS, from the tcalc tree) */
#include "../tisa_core.c"
#include <stdio.h>

static int violations, setups;
#define HOLDS(c, what) do { if (c) printf("  holds     %s\n", what); else { printf("  VIOLATED  %s\n", what); violations++; } } while (0)
#define SETUP(c) do { if (!(c)) { printf("  NO SCENE  line %d: %s\n", __LINE__, #c); setups++; return; } } while (0)

extern bool tisa_test_cb_probe(const uint64_t *in, uint64_t *out);
extern const uint8_t tisa_test_cb_probe_end[];
extern uint64_t tisa_test_cb_seen[5];
/* add64 as C, for the control that a test-only registry substituting add64 still opens */
static bool fn_reference_add64(const uint64_t *in, uint64_t *out) { out[0] = in[0] + in[1]; return true; }

static const struct { const char *name; uint8_t subop; TcFn fn; } OPS[] = {
    { "add64", TISA_BIN_ADD, tisa_native_add64 }, { "sub64", TISA_BIN_SUB, tisa_native_sub64 },
    { "and64", TISA_BIN_AND, tisa_native_and64 }, { "or64", TISA_BIN_OR, tisa_native_or64 },
    { "xor64", TISA_BIN_XOR, tisa_native_xor64 },
};
static __attribute__((unused)) uint64_t reference(int k, uint64_t x, uint64_t y) {
    switch (k) { case 0: return x + y; case 1: return x - y; case 2: return x & y; case 3: return x | y; default: return x ^ y; }
}

/* v3 = v1 OP v2; return v3 */
typedef struct { TcIsaProgram prog; TcIsaArena arena; } Prog;
static void prog_op(Prog *p, uint8_t subop) {
    tisa_arena_free(&p->arena);
    memset(p, 0, sizeof *p);
    tisa_arena_init(&p->arena, 64);
    p->prog.name = "admission_native"; p->prog.prog_id = 401u;
    p->prog.init_reg_mask = (uint16_t)((1u << TISA_V0) | (1u << TISA_V1) | (1u << TISA_V2));
    for (int r = 0; r <= TISA_V2; r++) p->prog.init_reg_types[r] = TISA_TYPE_U64;
    TcIsaStmt *s = tisa_stmt_instr(&p->arena, (TcIsaInstr){ .op = TISA_OP_BIN, .subop = subop, .ty = TISA_TYPE_U64,
                                                            .dst = TISA_V3, .src1 = TISA_V1, .src2 = TISA_V2 });
    p->prog.root = tisa_stmt_seq(&p->arena, s, tisa_stmt_return(&p->arena, TISA_OUTCOME_FIRED, TISA_V3));
}
static Prog P;
/* one hosted run of P on x, y: true with v3 when it reached a verdict */
static bool run(uint64_t x, uint64_t y, uint64_t *v3) {
    TcIsaRuntimeFrame frame;
    memset(&frame, 0, sizeof frame);
    uint64_t regs[TISA_NUM_VREGS] = { 0 };
    regs[TISA_V0] = (uint64_t)(uintptr_t)&frame; regs[TISA_V1] = x; regs[TISA_V2] = y;
    TcIsaHostedRunResult res;
    if (!tisa_try_eval_tcalc(&P.prog, &frame, regs, &res) || !res.has_verdict) return false;
    *v3 = regs[TISA_V3];
    return true;
}
/* an activation opened with test options (the test-only registry) */
static TcIsaHostedCtx H;
static TcIsaRecipeTable RT;
static TcIsaRuntimeFrame FR;
static uint64_t REGS[TISA_NUM_VREGS];
static bool open_with(const TcIsaHostedOptions *opt, uint64_t x, uint64_t y) {
    char err[256];
    tisa_hosted_close(&H);
    memset(&FR, 0, sizeof FR); memset(REGS, 0, sizeof REGS);
    REGS[TISA_V0] = (uint64_t)(uintptr_t)&FR; REGS[TISA_V1] = x; REGS[TISA_V2] = y;
    return tisa_lower_recipes(&P.prog, &RT, err, sizeof err) &&
           tisa_validate_frame(&P.prog, &FR, REGS, err, sizeof err) == TISA_OUTCOME_FIRED &&
           tisa_hosted_open(&H, &P.prog, &RT, &FR, REGS, 1u << 16, 1u << 14, opt);
}
static bool canonical_area(uint64_t a, uint64_t n) { return a <= UINT64_MAX - n && a + n <= (1ull << 47); }
static bool apart(uint64_t a, uint64_t n, uint64_t b, uint64_t m) { return a + n <= b || b + m <= a; }

static void hex(const uint8_t *d, char *out) { for (int i = 0; i < 32; i++) sprintf(out + 2 * i, "%02x", d[i]); }
/* the digest SHA256SUMS gives for NAME.bin, or "" */
static void sums_digest(const char *sums, const char *name, char *out) {
    out[0] = 0;
    FILE *f = fopen(sums, "r");
    char line[512], want[64];
    snprintf(want, sizeof want, "/%s.bin", name);
    while (f && fgets(line, sizeof line, f)) {
        char d[80], path[400];
        if (sscanf(line, "%79s %399s", d, path) != 2) continue;
        size_t n = strlen(path), m = strlen(want);
        if (n >= m && !strcmp(path + n - m, want) && strlen(d) == 64) { strcpy(out, d); break; }
    }
    if (f) fclose(f);
}

static void bytes_controls(const char *sums) {
    printf("the native images\n");
    bool entries = true, bytes = true, digests = true;
    for (int k = 0; k < 5; k++) {
        int slot = TISA_NATIVE[k].slot;
        entries &= TISA_FNS[slot].fn == OPS[k].fn && !strcmp(TISA_FNS[slot].name + 8, OPS[k].name);
        uint8_t d[32]; char h[65], s[80];
        tisa_sha256((const uint8_t *)(uintptr_t)OPS[k].fn, TISA_NATIVE_LEN, d);
        hex(d, h);
        sums_digest(sums, OPS[k].name, s);
#ifdef TISA_NATIVE_ALU_PATCHED
        bool same = tisa_native_bytes_ok(k, OPS[k].fn);
        bytes &= k == 0 ? !same : same;
        digests &= k == 0 ? strcmp(h, s) != 0 : !strcmp(h, s);
#else
        bytes &= tisa_native_bytes_ok(k, OPS[k].fn);
        digests &= !strcmp(h, s);
#endif
        digests &= !strcmp(TISA_NATIVE[k].image_sha256, s) && s[0];
    }
    HOLDS(entries, "the registry's add64, sub64, and64, or64 and xor64 entries are the native functions tisa_native_NAME");
#ifdef TISA_NATIVE_ALU_PATCHED
    HOLDS(bytes, "(patched build) add64's 34 bytes differ from its expected copy; the other four equal theirs");
    HOLDS(digests, "(patched build) the digest recorded beside each entry is the SHA256SUMS line; the bytes at add64 no longer hash to it, the other four do");
#else
    HOLDS(bytes, "each native function's 34 bytes equal its expected copy");
    HOLDS(digests, "the bytes at each native function, the digest recorded beside its entry and its SHA256SUMS line are one SHA-256");
#endif
}

#ifdef TISA_NATIVE_ALU_PATCHED
static void registration_controls(void) {
    printf("registration (patched build)\n");
    prog_op(&P, TISA_BIN_ADD);
    uint64_t v = 0;
    HOLDS(!run(7, 7, &v), "registration refuses add64's patched bytes: the production path gives no verdict");
    HOLDS(!open_with(NULL, 7, 7), "a production open fails before the seal");
    TcIsaHostedOptions sub = { .fault_slot = TFN_ADD64, .fault_fn = fn_reference_add64 };
    HOLDS(open_with(&sub, 7, 7), "(control: a test-only registry with add64 replaced opens, so the refusal is the image check's)");
}
#else
static void registration_controls(void) {
    printf("registration and the production path\n");
    (void)fn_reference_add64;
    prog_op(&P, TISA_BIN_ADD);
    SETUP(open_with(NULL, 7, 7));
    bool held = true;
    for (int k = 0; k < 5; k++) { TcFnInfo fi; held &= tc_fn_info(H.fn[TISA_NATIVE[k].slot], &fi) && fi.fn == OPS[k].fn; }
    HOLDS(held, "registration admits the images: the production registry holds the five native functions");
    static const uint64_t edge[] = { 0, 1, 2, 7, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 1ull << 32, INT64_MAX, (uint64_t)INT64_MIN, UINT64_MAX - 1, UINT64_MAX };
    for (int k = 0; k < 5; k++) {
        prog_op(&P, OPS[k].subop);
        int bad = 0, n = 0;
        for (size_t i = 0; i < sizeof edge / sizeof edge[0]; i++)
            for (size_t j = 0; j < sizeof edge / sizeof edge[0]; j++) {
                uint64_t v = 0;
                n++;
                if (!run(edge[i], edge[j], &v) || v != reference(k, edge[i], edge[j])) bad++;
            }
        char what[160];
        snprintf(what, sizeof what, "v3 = v1 %s v2 through the production path agrees with the arithmetic on %d word pairs", OPS[k].name, n);
        HOLDS(bad == 0, what);
    }
}
#endif

/* the kernel's call into a registered function, observed: a probe registered in add64's place (a
   test-only registry) records the pointers it is given and the return word's address */
static void call_site_controls(void) {
    printf("the kernel's call into a registered function (observed)\n");
    prog_op(&P, TISA_BIN_ADD);
    memset(tisa_test_cb_seen, 0, 5 * sizeof tisa_test_cb_seen[0]);
    TcIsaHostedOptions probe = { .fault_slot = TFN_ADD64, .fault_fn = tisa_test_cb_probe };
    SETUP(open_with(&probe, 7, 7));
    TcIsaOutcome oc = TISA_OUTCOME_REFUSED; uint64_t hp = 0, v3 = 0;
    SETUP(tisa_hosted_run(&H, &oc, &hp) == 1 && tisa_tcalc_read_cell_word(&H, H.reg_occ[3], &v3));
    uint64_t in = tisa_test_cb_seen[0], out = tisa_test_cb_seen[1], sp = tisa_test_cb_seen[2], ra = tisa_test_cb_seen[3];
    HOLDS(v3 == 14 && tisa_test_cb_seen[4] >= 1, "the kernel called the probe when it fired the step (7 + 7 = 14)");
    HOLDS(in % 8 == 0 && out % 8 == 0 && sp % 8 == 0, "in, out and the return word's address are 8-byte aligned");
    HOLDS(canonical_area(in, 16) && canonical_area(out, 8) && canonical_area(sp, 8) && canonical_area(sp + 8, 1) && ra < (1ull << 47),
          "in[0..15], out[0..7] and the return word lie in canonical user space without wrap; so do the return address and the stack after return");
    bool code_apart = apart(out, 8, (uint64_t)(uintptr_t)tisa_test_cb_probe,
                            (uint64_t)((uintptr_t)tisa_test_cb_probe_end - (uintptr_t)tisa_test_cb_probe));
    for (int k = 0; k < 5; k++) code_apart &= apart(out, 8, (uint64_t)(uintptr_t)OPS[k].fn, TISA_NATIVE_LEN);
    HOLDS(apart(out, 8, in, 16) && apart(out, 8, sp, 8) && code_apart,
          "out[0..7] is apart from in[0..15], from the return word, and from the probe's and the five images' code");
}

int main(int argc, char **argv) {
    const char *sums = argc > 1 ? argv[1] : "tisa/native_alu/SHA256SUMS";
    bytes_controls(sums);
    registration_controls();
    call_site_controls();
    printf("admission_native%s: %s (%d violated, %d scenes not set up)\n",
#ifdef TISA_NATIVE_ALU_PATCHED
           "_patched",
#else
           "",
#endif
           violations || setups ? "VIOLATED" : "holds", violations, setups);
    return violations ? 1 : setups ? 2 : 0;
}

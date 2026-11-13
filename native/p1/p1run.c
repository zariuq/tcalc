/*
 * p1run.c -- a t-ISA p1 program from its text, run by the p1 reference
 * evaluator (tisa_ref.c) and as native code (tisa_x86.c), side by side.
 *
 *   p1run [--hoist] [--quiet] [--image FILE NAME] PROGRAM [TESTS]
 *
 * PROGRAM is a program text in either style (p1_load.h). It is admitted,
 * emitted (with bounds hoisting under --hoist) and mapped executable. Every
 * run of TESTS starts the reference and the native code on equal copies of
 * one state and compares what they leave: outcome, status, ret_val,
 * fuel_used, and every region byte for byte, with guard bytes around each
 * region that neither may touch. One line per run says SAME or DIFF, and
 * whether the run met its expectations; --quiet prints only the runs that
 * differ or miss an expectation. --image writes the HOL image record of the
 * program (tisa_print_image_record) for the image prover.
 *
 * TESTS, one directive per line ('#' starts a comment; numbers are decimal
 * or 0x hexadecimal):
 *
 *   case NAME [chain]     a new case: its regions start empty, its frame
 *                         words and registers zero. With chain, each run
 *                         continues from the state the previous run of the
 *                         case left (each side from its own); without, every
 *                         run starts from the state the directives built.
 *   region R LEN          region R holds LEN zero bytes
 *   fill R B              every byte of region R is B
 *   bytes R OFF B ...     bytes from offset OFF
 *   hex R OFF HEX         bytes from offset OFF, as hexadecimal digits
 *   words R OFF W ...     64-bit little-endian words from offset OFF
 *   file R PATH           region R holds the file's bytes
 *   arg0 V | arg1 V       frame words 22 and 23
 *   budget V | used V     fuel_budget and fuel_used (the receipt)
 *   reg N V               entry register vN (1..5)
 *   regptr N R OFF        entry register vN points OFF bytes into region R
 *   expect OUTCOME [RET]  the next run ends with OUTCOME (FIRED REFUSED
 *                         UNSUPPORTED INVALID EXHAUSTED or 0..4), and RET
 *   want R OFF W          after the next run, the word at OFF of region R is W
 *   run [K=V ...]         one run; K is arg0 arg1 budget used or v1..v5
 *
 * Exit status: 0 iff every run is SAME and meets its expectations; 1 if
 * not; 2 if the program or TESTS cannot be used.
 */
#include "p1_load.h"
#include "tisa_ref.h"
#include "tisa_x86.h"

#include <errno.h>
#include <inttypes.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { NREG = TISA_MAX_REGIONS, GUARD = 64, GUARD_BYTE = 0xA5, MAX_WANTS = 64 };

static const char *outcome_name(TcIsaOutcome o) {
    static const char *names[] = {"REFUSED", "FIRED", "UNSUPPORTED", "INVALID", "EXHAUSTED"};
    return (unsigned)o < 5 ? names[o] : "?";
}

/* ---- region stores ---------------------------------------------------------- */

typedef struct {
    uint8_t *alloc, *base;   /* base: the region's first byte, GUARD bytes into the allocation and more */
    size_t   len;
} Region;

typedef struct { Region r[NREG]; } Store;

static size_t align_of(const TcIsaProgram *p, unsigned r) {
    size_t a = r < p->nregions && p->regions[r].align_bytes > 64 ? p->regions[r].align_bytes : 64;
    return a;
}

static bool region_alloc(Region *g, size_t len, size_t align) {
    free(g->alloc);
    g->alloc = malloc(len + 2 * GUARD + align);
    if (!g->alloc) { g->base = NULL; g->len = 0; return false; }
    uintptr_t at = ((uintptr_t)g->alloc + GUARD + align - 1) / align * align;
    g->base = (uint8_t *)at;
    g->len = len;
    memset(g->base - GUARD, GUARD_BYTE, GUARD);
    memset(g->base, 0, len);
    memset(g->base + len, GUARD_BYTE, GUARD);
    return true;
}

static void store_free(Store *s) {
    for (unsigned r = 0; r < NREG; ++r) free(s->r[r].alloc);
    memset(s, 0, sizeof *s);
}

static bool store_copy(Store *d, const Store *s, const TcIsaProgram *p) {
    store_free(d);
    for (unsigned r = 0; r < NREG; ++r) {
        if (!s->r[r].alloc) continue;
        if (!region_alloc(&d->r[r], s->r[r].len, align_of(p, r))) return false;
        memcpy(d->r[r].base, s->r[r].base, s->r[r].len);
    }
    return true;
}

static bool guards_intact(const Store *s, unsigned *which) {
    for (unsigned r = 0; r < NREG; ++r) {
        const Region *g = &s->r[r];
        if (!g->alloc) continue;
        for (unsigned k = 0; k < GUARD; ++k)
            if (g->base[-1 - (int)k] != GUARD_BYTE || g->base[g->len + k] != GUARD_BYTE) { *which = r; return false; }
    }
    return true;
}

/* ---- one case ------------------------------------------------------------------ */

typedef struct {
    char     name[128];
    bool     chain, started;
    Store    init;                 /* the state the directives built */
    Store    ref, nat;             /* the states the last runs left (chain) */
    uint64_t arg0, arg1, budget, used;
    uint64_t ref_used, nat_used;   /* the receipts the last runs left (chain) */
    uint64_t reg[6];
    int      ptr_region[6];        /* -1: reg[] is a value; else a region, reg[] its offset */
    unsigned runs;
    /* expectations for the next run */
    bool     has_expect, has_ret;
    TcIsaOutcome expect;
    uint64_t expect_ret;
    unsigned nwants;
    struct { unsigned region; uint64_t off, word; } wants[MAX_WANTS];
} Case;

typedef struct {
    const TcIsaProgram *prog;
    const TcIsaX86     *code;
    bool                quiet;
    const char         *tests;
    unsigned            line;
    unsigned long       runs, same, differ, expect_checked, expect_failed;
    unsigned long       outcomes[5];
} Harness;

static void case_reset(Case *c) {
    store_free(&c->init); store_free(&c->ref); store_free(&c->nat);
    memset(c, 0, sizeof *c);
    for (unsigned k = 0; k < 6; ++k) c->ptr_region[k] = -1;
}

static void frame_for(TcIsaRuntimeFrame *f, uint64_t regs[TISA_NUM_VREGS], const Case *c, const Store *s,
                      uint64_t used) {
    memset(f, 0, sizeof *f);
    for (unsigned r = 0; r < NREG; ++r) {
        uint64_t *w = (uint64_t *)f;
        w[2 * r] = s->r[r].alloc ? (uint64_t)(uintptr_t)s->r[r].base : 0;
        w[2 * r + 1] = s->r[r].alloc ? s->r[r].len : 0;
    }
    f->arg0 = c->arg0; f->arg1 = c->arg1;
    f->fuel_budget = c->budget; f->fuel_used = used;
    memset(regs, 0, TISA_NUM_VREGS * sizeof regs[0]);
    regs[0] = (uint64_t)(uintptr_t)f;
    for (unsigned k = 1; k <= 5; ++k)
        regs[k] = c->ptr_region[k] < 0 ? c->reg[k]
                : (s->r[c->ptr_region[k]].alloc ? (uint64_t)(uintptr_t)s->r[c->ptr_region[k]].base : 0) + c->reg[k];
}

static void say_run(const Case *c, const char *verdict, const char *detail) {
    printf("%s/%u %s%s%s\n", c->name, c->runs, verdict, *detail ? " " : "", detail);
}

static bool run_case(Harness *h, Case *c) {
    const TcIsaProgram *p = h->prog;
    Store ref = {0}, nat = {0};
    bool fresh = !c->chain || !c->started;
    if (!store_copy(&ref, fresh ? &c->init : &c->ref, p) || !store_copy(&nat, fresh ? &c->init : &c->nat, p)) {
        fprintf(stderr, "p1run: out of memory\n");
        exit(2);
    }
    uint64_t ref_used0 = fresh ? c->used : c->ref_used, nat_used0 = fresh ? c->used : c->nat_used;
    TcIsaRuntimeFrame fr, fn;
    uint64_t rr[TISA_NUM_VREGS], rn[TISA_NUM_VREGS];
    frame_for(&fr, rr, c, &ref, ref_used0);
    frame_for(&fn, rn, c, &nat, nat_used0);
    TcIsaOutcome oref = tisa_run(p, &fr, rr);
    TcIsaOutcome onat = tisa_x86_run(p, h->code, &fn, rn);
    c->runs++;
    h->runs++;
    if ((unsigned)oref < 5) h->outcomes[oref]++;

    char detail[512];
    size_t k = 0;
    detail[0] = 0;
#define ADD(...) (k += (size_t)snprintf(detail + k, k < sizeof detail ? sizeof detail - k : 0, __VA_ARGS__))
    bool same = oref == onat && fr.status == fn.status && fr.ret_val == fn.ret_val && fr.fuel_used == fn.fuel_used;
    if (!same)
        ADD("ref %s status=%" PRIu64 " ret=%" PRIu64 " used=%" PRIu64 " | x86 %s status=%" PRIu64 " ret=%" PRIu64
            " used=%" PRIu64 ";", outcome_name(oref), fr.status, fr.ret_val, fr.fuel_used, outcome_name(onat),
            fn.status, fn.ret_val, fn.fuel_used);
    for (unsigned r = 0; r < NREG; ++r) {
        const Region *a = &ref.r[r], *b = &nat.r[r];
        if (!a->alloc) continue;
        for (size_t q = 0; q < a->len; ++q)
            if (a->base[q] != b->base[q]) {
                if (same) same = false;
                ADD(" region %u byte %zu: ref %02x x86 %02x;", r, q, a->base[q], b->base[q]);
                break;
            }
    }
    unsigned which;
    if (!guards_intact(&ref, &which)) { same = false; ADD(" ref wrote outside region %u;", which); }
    if (!guards_intact(&nat, &which)) { same = false; ADD(" x86 wrote outside region %u;", which); }
    if (same) {
        h->same++;
        ADD("%s ret=%" PRIu64 " used=%" PRIu64, outcome_name(oref), fr.ret_val, fr.fuel_used);
    } else h->differ++;

    /* Expectations, on the reference's state. */
    bool met = true, any = c->has_expect || c->nwants;
    if (c->has_expect) {
        bool ok = oref == c->expect && (!c->has_ret || fr.ret_val == c->expect_ret);
        if (!ok) {
            met = false;
            ADD("; EXPECTED %s", outcome_name(c->expect));
            if (c->has_ret) ADD(" ret=%" PRIu64, c->expect_ret);
        }
    }
    for (unsigned w = 0; w < c->nwants; ++w) {
        const Region *g = &ref.r[c->wants[w].region];
        uint64_t got = 0;
        bool inside = g->alloc && c->wants[w].off + 8 <= g->len;
        if (inside) memcpy(&got, g->base + c->wants[w].off, 8);
        if (!inside || got != c->wants[w].word) {
            met = false;
            ADD("; WANTED region %u word at %" PRIu64 " = %" PRIu64 ", found %" PRIu64, c->wants[w].region,
                c->wants[w].off, c->wants[w].word, got);
        }
    }
#undef ADD
    if (any) { h->expect_checked++; if (!met) h->expect_failed++; }
    if (!same) say_run(c, "DIFF", detail);
    else if (!met) say_run(c, "SAME-BUT-UNEXPECTED", detail);
    else if (!h->quiet) say_run(c, any ? "SAME expected" : "SAME", detail);

    c->has_expect = c->has_ret = false;
    c->nwants = 0;
    if (c->chain) {
        store_free(&c->ref); store_free(&c->nat);
        c->ref = ref; c->nat = nat;
        c->ref_used = fr.fuel_used; c->nat_used = fn.fuel_used;
        c->started = true;
    } else { store_free(&ref); store_free(&nat); }
    return same && met;
}

/* ---- the description --------------------------------------------------------- */

static void bad(Harness *h, const char *format, ...) {
    va_list args;
    fprintf(stderr, "%s:%u: ", h->tests, h->line);
    va_start(args, format);
    vfprintf(stderr, format, args);
    va_end(args);
    fputc('\n', stderr);
    exit(2);
}

static uint64_t number(Harness *h, const char *t) {
    if (!t) bad(h, "a number is missing");
    char *end;
    errno = 0;
    uint64_t v = strtoull(t, &end, 0);
    if (errno || *end || *t == '-' || *t == '+' || !*t) bad(h, "\"%s\" is not a number", t);
    return v;
}

static unsigned region_no(Harness *h, const char *t) {
    uint64_t r = number(h, t);
    if (r >= NREG) bad(h, "region %" PRIu64 ": there are regions 0..%u", r, NREG - 1);
    return (unsigned)r;
}

static TcIsaOutcome outcome_of(Harness *h, const char *t) {
    for (unsigned o = 0; o < 5; ++o)
        if (t && !strcmp(t, outcome_name((TcIsaOutcome)o))) return (TcIsaOutcome)o;
    uint64_t v = number(h, t);
    if (v > 4) bad(h, "outcome %" PRIu64 ": outcomes are 0..4", v);
    return (TcIsaOutcome)v;
}

static Region *region_for_write(Harness *h, Case *c, unsigned r, uint64_t off, uint64_t n) {
    Region *g = &c->init.r[r];
    if (!g->alloc) bad(h, "region %u has no length yet (region %u LEN)", r, r);
    if (off > g->len || n > g->len - off) bad(h, "bytes %" PRIu64 "..%" PRIu64 " lie outside region %u (%zu bytes)",
                                              off, off + n, r, g->len);
    return g;
}

static void read_tests(Harness *h, FILE *in) {
    Case c;
    memset(&c, 0, sizeof c);
    case_reset(&c);
    bool have_case = false;
    char *line = NULL;
    size_t cap = 0;
    ssize_t got;
    while ((got = getline(&line, &cap, in)) >= 0) {
        h->line++;
        char *hash = strchr(line, '#');
        if (hash) *hash = 0;
        char *save = NULL, *word = strtok_r(line, " \t\r\n", &save);
        if (!word) continue;
#define NEXT() strtok_r(NULL, " \t\r\n", &save)
        if (!strcmp(word, "case")) {
            case_reset(&c);
            const char *name = NEXT();
            if (!name) bad(h, "case needs a name");
            snprintf(c.name, sizeof c.name, "%s", name);
            const char *mode = NEXT();
            if (mode && strcmp(mode, "chain")) bad(h, "case %s: \"%s\" is not chain", name, mode);
            c.chain = mode != NULL;
            have_case = true;
            continue;
        }
        if (!have_case) bad(h, "\"%s\" before the first case", word);
        if (c.started && strcmp(word, "run") && strcmp(word, "expect") && strcmp(word, "want") &&
            strcmp(word, "arg0") && strcmp(word, "arg1") && strcmp(word, "budget"))
            bad(h, "\"%s\" after the first run of chained case %s: only runs and expectations follow", word, c.name);
        if (!strcmp(word, "region")) {
            unsigned r = region_no(h, NEXT());
            uint64_t len = number(h, NEXT());
            if (!region_alloc(&c.init.r[r], len, align_of(h->prog, r))) bad(h, "out of memory");
        } else if (!strcmp(word, "fill")) {
            unsigned r = region_no(h, NEXT());
            uint64_t b = number(h, NEXT());
            if (b > 255) bad(h, "a byte is 0..255");
            Region *g = region_for_write(h, &c, r, 0, 0);
            memset(g->base, (int)b, g->len);
        } else if (!strcmp(word, "bytes") || !strcmp(word, "words")) {
            bool words = word[0] == 'w';
            unsigned r = region_no(h, NEXT());
            uint64_t off = number(h, NEXT());
            for (const char *t; (t = NEXT()); off += words ? 8 : 1) {
                uint64_t v = number(h, t);
                if (!words && v > 255) bad(h, "a byte is 0..255");
                Region *g = region_for_write(h, &c, r, off, words ? 8 : 1);
                if (words) for (unsigned b = 0; b < 8; ++b) g->base[off + b] = (uint8_t)(v >> (8 * b));
                else g->base[off] = (uint8_t)v;
            }
        } else if (!strcmp(word, "hex")) {
            unsigned r = region_no(h, NEXT());
            uint64_t off = number(h, NEXT());
            const char *t = NEXT();
            size_t n = t ? strlen(t) : 0;
            if (!t || n % 2) bad(h, "hex needs an even number of hexadecimal digits");
            Region *g = region_for_write(h, &c, r, off, n / 2);
            for (size_t q = 0; q < n / 2; ++q) {
                unsigned v;
                if (sscanf(t + 2 * q, "%2x", &v) != 1) bad(h, "\"%.2s\" is not hexadecimal", t + 2 * q);
                g->base[off + q] = (uint8_t)v;
            }
        } else if (!strcmp(word, "file")) {
            unsigned r = region_no(h, NEXT());
            const char *path = NEXT();
            FILE *f = path ? fopen(path, "rb") : NULL;
            if (!f) bad(h, "cannot read %s", path ? path : "(no path)");
            fseek(f, 0, SEEK_END);
            long n = ftell(f);
            fseek(f, 0, SEEK_SET);
            if (n < 0 || !region_alloc(&c.init.r[r], (size_t)n, align_of(h->prog, r))) bad(h, "cannot hold %s", path);
            if (fread(c.init.r[r].base, 1, (size_t)n, f) != (size_t)n) bad(h, "cannot read %s", path);
            fclose(f);
        } else if (!strcmp(word, "arg0")) c.arg0 = number(h, NEXT());
        else if (!strcmp(word, "arg1")) c.arg1 = number(h, NEXT());
        else if (!strcmp(word, "budget")) c.budget = number(h, NEXT());
        else if (!strcmp(word, "used")) c.used = number(h, NEXT());
        else if (!strcmp(word, "reg") || !strcmp(word, "regptr")) {
            uint64_t n = number(h, NEXT());
            if (n < 1 || n > 5) bad(h, "entry registers are v1..v5");
            if (word[3] == 'p') { c.ptr_region[n] = (int)region_no(h, NEXT()); c.reg[n] = number(h, NEXT()); }
            else { c.ptr_region[n] = -1; c.reg[n] = number(h, NEXT()); }
        } else if (!strcmp(word, "expect")) {
            c.has_expect = true;
            c.expect = outcome_of(h, NEXT());
            const char *ret = NEXT();
            c.has_ret = ret != NULL;
            if (ret) c.expect_ret = number(h, ret);
        } else if (!strcmp(word, "want")) {
            if (c.nwants == MAX_WANTS) bad(h, "more than %u wants for one run", MAX_WANTS);
            c.wants[c.nwants].region = region_no(h, NEXT());
            c.wants[c.nwants].off = number(h, NEXT());
            c.wants[c.nwants].word = number(h, NEXT());
            c.nwants++;
        } else if (!strcmp(word, "run")) {
            for (char *t; (t = NEXT()); ) {
                char *eq = strchr(t, '=');
                if (!eq) bad(h, "\"%s\": run takes KEY=VALUE", t);
                *eq = 0;
                uint64_t v = number(h, eq + 1);
                if (!strcmp(t, "arg0")) c.arg0 = v;
                else if (!strcmp(t, "arg1")) c.arg1 = v;
                else if (!strcmp(t, "budget")) c.budget = v;
                else if (!strcmp(t, "used")) c.used = v;
                else if (t[0] == 'v' && t[1] >= '1' && t[1] <= '5' && !t[2]) { c.ptr_region[t[1] - '0'] = -1; c.reg[t[1] - '0'] = v; }
                else bad(h, "\"%s\" is not a run setting", t);
            }
            run_case(h, &c);
        } else bad(h, "\"%s\" is not a directive", word);
#undef NEXT
    }
    free(line);
    case_reset(&c);
}

int main(int argc, char **argv) {
    bool hoist = false, quiet = false;
    const char *image = NULL, *image_name = NULL;
    int a = 1;
    for (; a < argc && argv[a][0] == '-' && argv[a][1] == '-'; ++a) {
        if (!strcmp(argv[a], "--hoist")) hoist = true;
        else if (!strcmp(argv[a], "--quiet")) quiet = true;
        else if (!strcmp(argv[a], "--image") && a + 2 < argc) { image = argv[++a]; image_name = argv[++a]; }
        else { fprintf(stderr, "p1run: unknown option %s\n", argv[a]); return 2; }
    }
    if (a >= argc || argc - a > 2) {
        fprintf(stderr, "usage: p1run [--hoist] [--quiet] [--image FILE NAME] PROGRAM [TESTS]\n");
        return 2;
    }
    const char *path = argv[a], *tests = a + 1 < argc ? argv[a + 1] : NULL;
    P1Program loaded;
    P1Error err;
    TcIsaTextStyle style;
    if (!p1_load_file(path, &loaded, &style, &err)) { p1_print_error(stderr, path, &err); return 2; }
    TcIsaProgram *prog = &loaded.prog;
    prog->name = path;
    char why[256];
    TcIsaAdmission adm;
    if (!tisa_admit(prog, &adm, why, sizeof why)) { fprintf(stderr, "%s: not admitted: %s\n", path, why); return 2; }
    TcIsaX86 code;
    TcIsaX86Options opts = {.hoist_bounds = hoist};
    if (!tisa_x86_emit_with(prog, &opts, &code, why, sizeof why) || !tisa_x86_load(&code, why, sizeof why)) {
        fprintf(stderr, "%s: no native code: %s\n", path, why);
        return 2;
    }
    unsigned hoisted = 0;
    for (size_t l = 0; l < code.nloops; ++l) hoisted += code.loops[l].hoisted;
    printf("p1run: %s (%s text): %zu statements, nesting %zu, %u regions, admitted (max receipt %s%" PRIu64 "); "
           "x86 %zu bytes, %zu spans, %zu loops (%u hoisted)\n",
           path, style == TISA_TEXT_HOL ? "HOL" : "S-expression", loaded.nstmts, loaded.depth,
           (unsigned)prog->nregions, adm.max_receipt_fits ? "" : "over 2^64, shown as ",
           adm.max_receipt, code.len, code.nspans, code.nloops, hoisted);
    if (image) {
        FILE *f = fopen(image, "w");
        if (!f || !tisa_print_image_record(f, image_name, prog, &code)) {
            fprintf(stderr, "%s: no image record (tisa_print_image_record refused it)\n", image);
            if (f) fclose(f);
            return 2;
        }
        fclose(f);
    }
    int status = 0;
    if (tests) {
        FILE *in = fopen(tests, "r");
        if (!in) { fprintf(stderr, "%s: cannot read\n", tests); return 2; }
        Harness h = {.prog = prog, .code = &code, .quiet = quiet, .tests = tests};
        read_tests(&h, in);
        fclose(in);
        printf("p1run: %lu runs, %lu SAME, %lu DIFF; reference outcomes FIRED %lu, REFUSED %lu, UNSUPPORTED %lu, "
               "INVALID %lu, EXHAUSTED %lu; expectations %lu checked, %lu missed\n",
               h.runs, h.same, h.differ, h.outcomes[TISA_OUTCOME_FIRED], h.outcomes[TISA_OUTCOME_REFUSED],
               h.outcomes[TISA_OUTCOME_UNSUPPORTED], h.outcomes[TISA_OUTCOME_INVALID_INPUT],
               h.outcomes[TISA_OUTCOME_EXHAUSTED], h.expect_checked, h.expect_failed);
        status = h.differ || h.expect_failed ? 1 : 0;
    }
    tisa_x86_free(&code);
    p1_free(&loaded);
    return status;
}

/* intern_p1.c - find-or-make (interning) of 16-byte rows as a t-ISA p1 program.
 *
 * Regions: 0 rows (RW, 16-byte rows), 1 table (RW, 8-byte slots: 0 empty,
 * id+1 occupied), 2 header (RW, word 0 = row count). The key is (arg0, arg1).
 * FIRED returns an id whose row equals the key: an existing row below the
 * count, or a row appended at the count. Nothing about the table is trusted:
 * a slot is used only after its id is checked against the count, and the
 * count only after it is checked against the rows' capacity.
 *
 * This file builds the program, admits it, emits x86 with the t-ISA emitter,
 * compares the p1 reference with the native code on random and corrupted
 * inputs, checks interning behaviour, and prints the image record that the
 * HOL Light generator proves. */
#include "../../tisa/tisa.h"
#include "../../tisa/tisa_ref.h"
#include "../../tisa/tisa_x86.h"
#include "../../tisa/tisa_print.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ---- a small statement builder ------------------------------------------ */

static TcIsaStmt pool[256];
static size_t npool;

static TcIsaStmt *new_stmt(TcIsaCtrlKind k) {
    if (npool >= sizeof pool / sizeof pool[0]) { fprintf(stderr, "pool full\n"); exit(2); }
    TcIsaStmt *s = &pool[npool++];
    memset(s, 0, sizeof *s);
    s->kind = k;
    return s;
}
static TcIsaStmt *ins(TcIsaInstr i) { TcIsaStmt *s = new_stmt(TISA_CTRL_INSTR); s->u.instr = i; return s; }
static TcIsaStmt *seq(TcIsaStmt *a, TcIsaStmt *b) {
    TcIsaStmt *s = new_stmt(TISA_CTRL_SEQ); s->u.seq.first = a; s->u.seq.second = b; return s;
}
static TcIsaStmt *seqv(TcIsaStmt **v, size_t n) {   /* right-nested sequence */
    TcIsaStmt *acc = v[n - 1];
    for (size_t i = n - 1; i-- > 0; ) acc = seq(v[i], acc);
    return acc;
}
#define SEQ(...) seqv((TcIsaStmt *[]){__VA_ARGS__}, sizeof((TcIsaStmt *[]){__VA_ARGS__}) / sizeof(TcIsaStmt *))
static TcIsaStmt *iff(uint8_t c, TcIsaStmt *a, TcIsaStmt *b) {
    TcIsaStmt *s = new_stmt(TISA_CTRL_IF);
    s->u.if_cond.cond_reg = c; s->u.if_cond.then_branch = a; s->u.if_cond.else_branch = b; return s;
}
static TcIsaStmt *count_loop(uint8_t x, uint8_t n, uint32_t cap, TcIsaStmt *body) {
    TcIsaStmt *s = new_stmt(TISA_CTRL_COUNT_LOOP);
    s->u.count_loop.idx_reg = x; s->u.count_loop.bound_reg = n;
    s->u.count_loop.max_iters = cap; s->u.count_loop.body = body; return s;
}
static TcIsaStmt *ret(TcIsaOutcome o, uint8_t r) {
    TcIsaStmt *s = new_stmt(TISA_CTRL_RETURN); s->u.ret.outcome = o; s->u.ret.ret_reg = r; return s;
}

static TcIsaInstr I_imm(uint8_t d, uint64_t k) {
    TcIsaInstr i = {0}; i.op = TISA_OP_IMM; i.ty = TISA_TYPE_U64; i.dst = d; i.imm64 = k; return i;
}
static TcIsaInstr I_bin(TcIsaBinOp op, uint8_t d, uint8_t a, uint8_t b) {
    TcIsaInstr i = {0}; i.op = TISA_OP_BIN; i.ty = TISA_TYPE_U64; i.subop = op;
    i.dst = d; i.src1 = a; i.src2 = b; return i;
}
static TcIsaInstr I_shift(TcIsaShiftOp op, uint8_t d, uint8_t a, uint8_t amount) {
    TcIsaInstr i = {0}; i.op = TISA_OP_SHIFT; i.ty = TISA_TYPE_U64; i.subop = op;
    i.dst = d; i.src1 = a; i.bit_width = amount; return i;
}
static TcIsaInstr I_cmp_reg(TcIsaCmpCond c, uint8_t d, uint8_t a, uint8_t b) {
    TcIsaInstr i = {0}; i.op = TISA_OP_CMP; i.ty = TISA_TYPE_U64; i.subop = c;
    i.dst = d; i.src1 = a; i.src2 = b; return i;
}
static TcIsaInstr I_cmp_imm(TcIsaCmpCond c, uint8_t d, uint8_t a, uint64_t k) {
    TcIsaInstr i = {0}; i.op = TISA_OP_CMP; i.ty = TISA_TYPE_U64; i.subop = c;
    i.dst = d; i.src1 = a; i.bit_width = 1; i.imm64 = k; return i;
}
static TcIsaInstr I_frame(TcIsaValType t, uint8_t d, unsigned word) {
    TcIsaInstr i = {0}; i.op = TISA_OP_LOAD; i.ty = t; i.subop = TISA_MEM_U64;
    i.region_id = TISA_REGION_FRAME; i.dst = d; i.src1 = 0; i.disp32 = (int32_t)(8 * word); return i;
}
static TcIsaInstr I_addr(uint8_t r, uint8_t d, uint8_t p, uint8_t idx, uint8_t scale) {
    TcIsaInstr i = {0}; i.op = TISA_OP_ADDR; i.ty = TISA_TYPE_PTR; i.region_id = r;
    i.dst = d; i.src1 = p; i.src2 = idx; i.scale_lg2 = scale; i.disp32 = 0; return i;
}
static TcIsaInstr I_load(uint8_t r, uint8_t d, uint8_t p, int32_t off) {
    TcIsaInstr i = {0}; i.op = TISA_OP_LOAD; i.ty = TISA_TYPE_U64; i.subop = TISA_MEM_U64;
    i.region_id = r; i.dst = d; i.src1 = p; i.disp32 = off; return i;
}
static TcIsaInstr I_store(uint8_t r, uint8_t p, int32_t off, uint8_t v) {
    TcIsaInstr i = {0}; i.op = TISA_OP_STORE; i.ty = TISA_TYPE_U64; i.subop = TISA_MEM_U64;
    i.region_id = r; i.src1 = p; i.disp32 = off; i.src2 = v; return i;
}

/* Registers: v1 k0, v2 k1, v3 count, v4 mask, v5 hash, v6 slots (loop bound),
 * v7 probe index; v8..v11 temporaries. Frame words: 2r region r base,
 * 2r+1 its length, 22 arg0, 23 arg1. */
enum { ROWS = 0, TABLE = 1, HEADER = 2, CAP = 1u << 24 };

static TcIsaProgram build(void) {
    npool = 0;
    TcIsaStmt *append = SEQ(
        ins(I_shift(TISA_SHIFT_SHL, 10, 3, 1)),        /* v10 = 2 count */
        ins(I_frame(TISA_TYPE_PTR, 11, 2 * ROWS)),       /* v11 = rows base */
        ins(I_addr(ROWS, 11, 11, 10, 3)),                /* v11 = &rows[count] */
        ins(I_store(ROWS, 11, 0, 1)),
        ins(I_store(ROWS, 11, 8, 2)),
        ins(I_imm(10, 1)),
        ins(I_bin(TISA_BIN_ADD, 10, 3, 10)),             /* v10 = count + 1 */
        ins(I_store(TABLE, 9, 0, 10)),                   /* slot = count + 1 */
        ins(I_frame(TISA_TYPE_PTR, 11, 2 * HEADER)),
        ins(I_store(HEADER, 11, 0, 10)),                 /* count = count + 1 */
        ret(TISA_OUTCOME_FIRED, 3));
    TcIsaStmt *empty = SEQ(
        ins(I_frame(TISA_TYPE_U64, 10, 2 * ROWS + 1)),
        ins(I_shift(TISA_SHIFT_SHRU, 10, 10, 4)),        /* v10 = capacity in rows */
        ins(I_cmp_reg(TISA_CMP_ULT, 11, 3, 10)),         /* count < capacity */
        iff(11, append, ret(TISA_OUTCOME_UNSUPPORTED, 3)));
    TcIsaStmt *second = SEQ(
        ins(I_load(ROWS, 11, 8, 8)),
        ins(I_cmp_reg(TISA_CMP_EQ, 11, 11, 2)),
        iff(11, ret(TISA_OUTCOME_FIRED, 10), NULL));
    TcIsaStmt *checkrow = SEQ(
        ins(I_shift(TISA_SHIFT_SHL, 11, 10, 1)),        /* v11 = 2 id */
        ins(I_frame(TISA_TYPE_PTR, 8, 2 * ROWS)),
        ins(I_addr(ROWS, 8, 8, 11, 3)),                  /* v8 = &rows[id] */
        ins(I_load(ROWS, 11, 8, 0)),
        ins(I_cmp_reg(TISA_CMP_EQ, 11, 11, 1)),
        iff(11, second, NULL));
    TcIsaStmt *occupied = SEQ(
        ins(I_imm(11, 1)),
        ins(I_bin(TISA_BIN_SUB, 10, 10, 11)),            /* v10 = id = slot - 1 */
        ins(I_cmp_reg(TISA_CMP_ULT, 11, 10, 3)),         /* id < count */
        iff(11, checkrow, NULL));
    TcIsaStmt *body = SEQ(
        ins(I_bin(TISA_BIN_ADD, 8, 5, 7)),
        ins(I_bin(TISA_BIN_AND, 8, 8, 4)),               /* v8 = slot index */
        ins(I_frame(TISA_TYPE_PTR, 9, 2 * TABLE)),
        ins(I_addr(TABLE, 9, 9, 8, 3)),                  /* v9 = &table[slot index] */
        ins(I_load(TABLE, 10, 9, 0)),                    /* v10 = slot */
        ins(I_cmp_imm(TISA_CMP_EQ, 11, 10, 0)),
        iff(11, empty, occupied));
    TcIsaStmt *prologue = SEQ(
        ins(I_frame(TISA_TYPE_U64, 1, 22)),
        ins(I_frame(TISA_TYPE_U64, 2, 23)),
        ins(I_frame(TISA_TYPE_PTR, 8, 2 * HEADER)),
        ins(I_load(HEADER, 3, 8, 0)),                    /* v3 = count */
        ins(I_frame(TISA_TYPE_U64, 9, 2 * ROWS + 1)),
        ins(I_shift(TISA_SHIFT_SHRU, 9, 9, 4)),          /* v9 = capacity in rows */
        ins(I_cmp_reg(TISA_CMP_ULT, 10, 9, 3)),          /* capacity < count: a bad header */
        iff(10, ret(TISA_OUTCOME_UNSUPPORTED, 3), NULL),
        ins(I_frame(TISA_TYPE_U64, 6, 2 * TABLE + 1)),
        ins(I_shift(TISA_SHIFT_SHRU, 6, 6, 3)),          /* v6 = slots */
        ins(I_imm(9, 1)),
        ins(I_bin(TISA_BIN_SUB, 4, 6, 9)),               /* v4 = mask = slots - 1 */
        ins(I_bin(TISA_BIN_XOR, 5, 1, 2)),
        ins(I_imm(9, 0x9E3779B97F4A7C15ull)),
        ins(I_bin(TISA_BIN_MULLO, 5, 5, 9)),
        ins(I_shift(TISA_SHIFT_SHRU, 9, 5, 29)),
        ins(I_bin(TISA_BIN_XOR, 5, 5, 9)));              /* v5 = hash */
    /* Three parts, so that the proof takes them one at a time. */
    TcIsaStmt *root = SEQ(prologue, count_loop(7, 6, CAP, body), ret(TISA_OUTCOME_UNSUPPORTED, 3));
    TcIsaProgram p;
    memset(&p, 0, sizeof p);
    p.name = "intern16";
    p.nregions = 3;
    p.regions[ROWS]   = (TcIsaRegionDecl){ ROWS,   TISA_CAP_RW, 16, 8, "rows" };
    p.regions[TABLE]  = (TcIsaRegionDecl){ TABLE,  TISA_CAP_RW,  8, 8, "table" };
    p.regions[HEADER] = (TcIsaRegionDecl){ HEADER, TISA_CAP_RW,  8, 8, "header" };
    p.root = root;
    return p;
}

/* ---- tests ---------------------------------------------------------------- */

static uint64_t rng = 0x243F6A8885A308D3ull;
static uint64_t next(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

typedef struct { uint64_t *rows, *table, *header; size_t nrows, nslots; } Store;

static void frame_for(TcIsaRuntimeFrame *f, Store *s, uint64_t k0, uint64_t k1) {
    memset(f, 0, sizeof *f);
    f->s0_ptr = (uint64_t)(uintptr_t)s->rows;   f->s0_len = 16 * s->nrows;
    f->s1_ptr = (uint64_t)(uintptr_t)s->table;  f->s1_len = 8 * s->nslots;
    f->s2_ptr = (uint64_t)(uintptr_t)s->header; f->s2_len = 8;
    f->arg0 = k0; f->arg1 = k1;
}

static void store_new(Store *s, size_t nrows, size_t nslots) {
    s->nrows = nrows; s->nslots = nslots;
    s->rows = calloc(2 * nrows, 8); s->table = calloc(nslots, 8); s->header = calloc(1, 8);
}
static void store_copy(Store *d, const Store *s) {
    store_new(d, s->nrows, s->nslots);
    memcpy(d->rows, s->rows, 16 * s->nrows); memcpy(d->table, s->table, 8 * s->nslots);
    d->header[0] = s->header[0];
}
static void store_free(Store *s) { free(s->rows); free(s->table); free(s->header); }
static int store_eq(const Store *a, const Store *b) {
    return a->header[0] == b->header[0] && !memcmp(a->rows, b->rows, 16 * a->nrows) &&
           !memcmp(a->table, b->table, 8 * a->nslots);
}

static TcIsaOutcome run_ref(const TcIsaProgram *p, Store *s, uint64_t k0, uint64_t k1, uint64_t *rv) {
    TcIsaRuntimeFrame f; frame_for(&f, s, k0, k1);
    uint64_t regs[TISA_NUM_VREGS] = {0}; regs[0] = (uint64_t)(uintptr_t)&f;
    TcIsaOutcome o = tisa_run(p, &f, regs);
    *rv = f.ret_val; return o;
}
static TcIsaOutcome run_x86(const TcIsaProgram *p, const TcIsaX86 *x, Store *s, uint64_t k0, uint64_t k1, uint64_t *rv) {
    TcIsaRuntimeFrame f; frame_for(&f, s, k0, k1);
    uint64_t regs[TISA_NUM_VREGS] = {0}; regs[0] = (uint64_t)(uintptr_t)&f;
    TcIsaOutcome o = tisa_x86_run(p, x, &f, regs);
    *rv = f.ret_val; return o;
}

int main(int argc, char **argv) {
    TcIsaProgram p = build();
    char err[256];
    TcIsaAdmission adm;
    if (!tisa_admit(&p, &adm, err, sizeof err)) { fprintf(stderr, "not admitted: %s\n", err); return 1; }
    TcIsaX86 x;
    if (!tisa_x86_emit(&p, &x, err, sizeof err) || !tisa_x86_load(&x, err, sizeof err)) {
        fprintf(stderr, "emission failed: %s\n", err); return 1;
    }
    long runs = 0, fired = 0, appended = 0, bad = 0;

    /* 1. Differential: p1 reference against native code, random stores including
     *    corrupted tables and headers; outcome, return value and all bytes equal. */
    for (int t = 0; t < 4000; t++) {
        size_t nrows = 1 + next() % 24, nslots = 1 + next() % 40;
        Store s; store_new(&s, nrows, nslots);
        size_t count = next() % (nrows + 3);              /* sometimes above capacity */
        s.header[0] = count;
        for (size_t i = 0; i < 2 * nrows; i++) s.rows[i] = next() % 4;
        for (size_t i = 0; i < nslots; i++) {
            uint64_t r = next() % 5;
            s.table[i] = r == 0 ? 0 : r == 1 ? next() : 1 + next() % (count + 2);
        }
        for (int q = 0; q < 6; q++) {
            uint64_t k0 = next() % 4, k1 = next() % 4;
            Store a, b; store_copy(&a, &s); store_copy(&b, &s);
            uint64_t ra = 0, rb = 0;
            TcIsaOutcome oa = run_ref(&p, &a, k0, k1, &ra), ob = run_x86(&p, &x, &b, k0, k1, &rb);
            runs++;
            if (oa != ob || ra != rb || !store_eq(&a, &b)) {
                bad++;
                if (bad < 5) fprintf(stderr, "DIFF t=%d q=%d ref=%d/%" PRIu64 " x86=%d/%" PRIu64 "\n", t, q, oa, ra, ob, rb);
            }
            /* Soundness on every FIRED run: the returned row is the key, earlier rows kept. */
            if (oa == TISA_OUTCOME_FIRED) {
                fired++;
                uint64_t c0 = s.header[0], c1 = a.header[0];
                int ok = ra < c1 && a.rows[2 * ra] == k0 && a.rows[2 * ra + 1] == k1 &&
                         (c1 == c0 || c1 == c0 + 1) && !memcmp(a.rows, s.rows, 16 * (c0 < nrows ? c0 : nrows));
                if (c1 == c0 + 1) { appended++; ok = ok && ra == c0; }
                if (!ok) { bad++; fprintf(stderr, "UNSOUND t=%d q=%d\n", t, q); }
            }
            store_free(&a); store_free(&b);
        }
        store_free(&s);
    }

    /* 2. Interning behaviour on a clean store: equal keys get equal ids,
     *    distinct keys distinct ids, and the rows hold the keys. */
    Store s; store_new(&s, 512, 1024);
    uint64_t ids[64][4];
    for (int round = 0; round < 3; round++)
        for (int k0 = 0; k0 < 64; k0++)
            for (int k1 = 0; k1 < 4; k1++) {
                uint64_t r = 0;
                TcIsaOutcome o = run_x86(&p, &x, &s, (uint64_t)k0 * 7919, (uint64_t)k1, &r);
                if (o != TISA_OUTCOME_FIRED) { bad++; continue; }
                if (round == 0) ids[k0][k1] = r;
                else if (ids[k0][k1] != r) bad++;
            }
    if (s.header[0] != 256) bad++;
    for (int k0 = 0; k0 < 64; k0++)
        for (int k1 = 0; k1 < 4; k1++) {
            uint64_t r = ids[k0][k1];
            if (s.rows[2 * r] != (uint64_t)k0 * 7919 || s.rows[2 * r + 1] != (uint64_t)k1) bad++;
        }
    store_free(&s);

    printf("intern16: %zu bytes, admitted, %ld differential runs (%ld fired, %ld appended), interning checked, %ld failures\n",
           x.len, runs, fired, appended, bad);
    if (argc > 1) {
        FILE *f = fopen(argv[1], "w");
        if (!f || !tisa_print_image_record(f, "intern16", &p, &x)) { fprintf(stderr, "cannot write %s\n", argv[1]); return 1; }
        fclose(f);
    }
    tisa_x86_free(&x);
    return bad ? 1 : 0;
}

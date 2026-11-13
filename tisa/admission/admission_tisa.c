/* admission_tisa.c: hosted t-ISA admission controls, through the production sealed path with an
   untrusted caller. Each check prints "holds" or "VIOLATED"; exit 1 if any is violated, 2 if a scene
   could not be set up. Includes tisa_core.c to fire single STEPs by hand and to use its test seams
   (TcIsaHostedOptions). */
#include "../tisa_core.c"
#include <stdio.h>

static int violations, setups;
#define HOLDS(c, what) do { if (c) printf("  holds     %s\n", what); else { printf("  VIOLATED  %s\n", what); violations++; } } while (0)
#define SETUP(c) do { if (!(c)) { printf("  NO SCENE  line %d: %s\n", __LINE__, #c); setups++; return; } } while (0)

/* ---- programs ---- */
typedef struct { TcIsaProgram prog; TcIsaArena arena; } Prog;
static void prog_base(Prog *p, const char *name, uint32_t id, uint16_t init) {
    tisa_arena_free(&p->arena);
    memset(p, 0, sizeof *p);
    tisa_arena_init(&p->arena, 64);
    p->prog.name = name; p->prog.prog_id = id;
    p->prog.init_reg_mask = (uint16_t)((1u << TISA_V0) | init);
    p->prog.init_reg_types[TISA_V0] = TISA_TYPE_U64;
    for (int r = 1; r < TISA_NUM_VREGS; r++) if (init >> r & 1u) p->prog.init_reg_types[r] = TISA_TYPE_U64;
}
static TcIsaStmt *seq(TcIsaArena *a, TcIsaStmt *s, TcIsaInstr i) { return tisa_stmt_seq(a, s, tisa_stmt_instr(a, i)); }
/* v3 = v1 + v2; return v3 (the probe's 7 + 7) */
static void prog_add(Prog *p) {
    prog_base(p, "admission_add", 301u, (1u << TISA_V1) | (1u << TISA_V2));
    TcIsaStmt *s = seq(&p->arena, NULL, (TcIsaInstr){ .op = TISA_OP_BIN, .subop = TISA_BIN_ADD, .ty = TISA_TYPE_U64, .dst = TISA_V3, .src1 = TISA_V1, .src2 = TISA_V2 });
    p->prog.root = tisa_stmt_seq(&p->arena, s, tisa_stmt_return(&p->arena, TISA_OUTCOME_FIRED, TISA_V3));
}
/* v1 = v1 + v1 (the destination is both operands) */
static void prog_alias(Prog *p) {
    prog_base(p, "admission_alias", 302u, 1u << TISA_V1);
    TcIsaStmt *s = seq(&p->arena, NULL, (TcIsaInstr){ .op = TISA_OP_BIN, .subop = TISA_BIN_ADD, .ty = TISA_TYPE_U64, .dst = TISA_V1, .src1 = TISA_V1, .src2 = TISA_V1 });
    p->prog.root = tisa_stmt_seq(&p->arena, s, tisa_stmt_return(&p->arena, TISA_OUTCOME_FIRED, TISA_V1));
}
/* region 0 of 32 bytes at v1: v2 = 0x1122334455667788; store 8 bytes at 0; load 8 bytes at 0 into v3; load
   4 signed bytes at 4 into v4; return v3 */
static void prog_mem(Prog *p) {
    prog_base(p, "admission_mem", 303u, 0);
    p->prog.nregions = 1u;
    p->prog.regions[0] = (TcIsaRegionDecl){ 0, TISA_CAP_RW, 32, 8, "buf" };
    p->prog.init_reg_mask |= 1u << TISA_V1;
    p->prog.init_reg_types[TISA_V1] = TISA_TYPE_PTR; p->prog.init_reg_region[TISA_V1] = 0u;
    TcIsaArena *a = &p->arena;
    TcIsaStmt *s = seq(a, NULL, (TcIsaInstr){ .op = TISA_OP_IMM, .ty = TISA_TYPE_U64, .dst = TISA_V2, .imm64 = 0x1122334455667788ull });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_STORE, .subop = TISA_MEM_U64, .ty = TISA_TYPE_U64, .src1 = TISA_V1, .src2 = TISA_V2, .region_id = 0u, .disp32 = 0 });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_LOAD, .subop = TISA_MEM_U64, .ty = TISA_TYPE_U64, .dst = TISA_V3, .src1 = TISA_V1, .region_id = 0u, .disp32 = 0 });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_LOAD, .subop = TISA_MEM_U32, .ty = TISA_TYPE_I32S, .dst = TISA_V4, .src1 = TISA_V1, .region_id = 0u, .disp32 = 4 });
    p->prog.root = tisa_stmt_seq(a, s, tisa_stmt_return(a, TISA_OUTCOME_FIRED, TISA_V3));
}
/* v4 = 0; for v3 in 0 .. v2: v4 = v4 + v3; return v4 */
static void prog_loop(Prog *p, TcIsaOutcome oc) {
    prog_base(p, "admission_loop", 304u, 1u << TISA_V2);
    TcIsaArena *a = &p->arena;
    TcIsaStmt *body = tisa_stmt_instr(a, (TcIsaInstr){ .op = TISA_OP_BIN, .subop = TISA_BIN_ADD, .ty = TISA_TYPE_U64, .dst = TISA_V4, .src1 = TISA_V4, .src2 = TISA_V3 });
    TcIsaStmt *s = seq(a, NULL, (TcIsaInstr){ .op = TISA_OP_IMM, .ty = TISA_TYPE_U64, .dst = TISA_V4, .imm64 = 0 });
    s = tisa_stmt_seq(a, s, tisa_stmt_count_loop(a, TISA_V3, TISA_V2, 8u, body));
    p->prog.root = tisa_stmt_seq(a, s, tisa_stmt_return(a, oc, TISA_V4));
}

/* ---- an activation, stepped by hand ---- */
typedef struct {
    TcIsaHostedCtx   h;
    TcIsaRecipeTable rt;
    TcIsaRuntimeFrame frame;
    uint64_t         regs[TISA_NUM_VREGS], buf[4];
} Act;
static Act A_;
static bool act_open(Act *a, const TcIsaProgram *prog, uint64_t r1, uint64_t r2, uint64_t fuel,
                     const TcIsaHostedOptions *opt, bool seal) {
    char err[256];
    tisa_hosted_close(&a->h);
    memset(a, 0, sizeof *a);
    if (prog->nregions) { a->frame.s0_ptr = (uint64_t)(uintptr_t)a->buf; a->frame.s0_len = sizeof a->buf; }
    a->frame.fuel_budget = fuel;
    a->regs[TISA_V0] = (uint64_t)(uintptr_t)&a->frame;
    a->regs[TISA_V1] = prog->nregions ? a->frame.s0_ptr : r1;
    a->regs[TISA_V2] = r2;
    if (!tisa_lower_recipes(prog, &a->rt, err, sizeof err)) return false;
    if (tisa_validate_frame(prog, &a->frame, a->regs, err, sizeof err) != TISA_OUTCOME_FIRED) return false;
    if (!tisa_hosted_prepare(&a->h, prog, &a->rt, &a->frame, a->regs, 1u << 16, 1u << 14, opt)) return false;
    return !seal || tisa_hosted_seal(&a->h);
}
static uint64_t act_pc(Act *a) { uint64_t pc = UINT64_MAX; tisa_tcalc_read_cell_word(&a->h, a->h.ctrl_occ, &pc); return pc; }
static uint64_t act_reg(Act *a, int r) { uint64_t v = UINT64_MAX; tisa_tcalc_read_cell_word(&a->h, a->h.reg_occ[r], &v); return v; }
/* steps until the control cell stands at a point of recipe kind `kind` (and opcode `op` for INSTR) */
static bool act_run_to(Act *a, TcIsaRecipeKind kind, int op) {
    for (int n = 0; n < 4096; n++) {
        uint64_t pc = act_pc(a);
        if (pc >= a->rt.npoints) return false;
        const TcIsaPointRecipe *r = &a->rt.recipes[pc];
        if (r->kind == kind && (op < 0 || (int)r->instr.op == op)) return true;
        if (!tisa_hosted_step(&a->h, pc)) return false;
    }
    return false;
}
/* The honest STEP at the current point: the case the host picks, its words, the firing's premises,
   and the holes of the written value and of next in the rule as installed. */
typedef struct {
    uint64_t pc; const TisaPoint *p; const TisaForm *f; int ci; const TisaCase *cs; TisaEnv e; TisaFiring fr;
    int out_hole, next_hole; bool out_is_op;
} Pick;
static int pat_arg_hole(Term pat, int i) {
    uint8_t k; uint32_t hd; int ar; const Term *args;
    tc_node(pat, &k, &hd, &ar, &args);
    if (k != K_APP || i >= ar) return -1;
    Term a = args[i];
    tc_node(a, &k, &hd, &ar, &args);
    return k == K_VAR ? (int)hd : -1;
}
static bool act_pick(Act *a, Pick *k) {
    memset(k, 0, sizeof *k);
    k->out_hole = k->next_hole = -1;
    k->pc = act_pc(a);
    if (k->pc >= a->rt.npoints) return false;
    k->p = &a->h.pt[k->pc];
    if (k->p->form < 0) return false;
    k->f = &a->h.forms[k->p->form];
    if (!tisa_point_env(&a->h, k->p, &k->e)) return false;
    while (k->ci < k->f->ncase && !tisa_case_holds(&a->h, &k->f->cs[k->ci], &k->e)) k->ci++;
    if (k->ci == k->f->ncase) return false;
    k->cs = &k->f->cs[k->ci];
    if (!tisa_step_firing(&a->h, k->p, k->ci, &k->e, &k->fr)) return false;
    TcInspectRule ir;
    if (!tc_inspect_rule(k->fr.rule, &ir, NULL)) return false;
    k->next_hole = pat_arg_hole(ir.decl_rule.make.t, 2);
    if (ir.decl_rule.nmake_extra) {
        k->out_hole = pat_arg_hole(ir.decl_rule.make_extra[0].t, 2);
        k->out_is_op = ir.decl_rule.nop && ir.decl_rule.op[ir.decl_rule.nop - 1].out[0] == k->out_hole;
    }
    return true;
}

/* ---- the board ---- */
typedef struct { Occ hi; bool alive[8192]; Term term[8192]; uint64_t names; } Snap;
static Snap S0, S1;
static void snap(Snap *s) {
    s->names = tc_next_name(); s->hi = 0;
    for (Occ o = 1; o < 8192; o++) { s->alive[o] = tc_alive(o); s->term[o] = s->alive[o] ? tc_term(o) : 0; if (s->alive[o]) s->hi = o; }
}
static bool unchanged(const Snap *s) {
    snap(&S1);
    if (s->names != S1.names) return false;
    for (Occ o = 1; o < 8192; o++) if (s->alive[o] != S1.alive[o] || s->term[o] != S1.term[o]) return false;
    return true;
}
/* live facts of constructor con, and live control cells */
static int count_live(int con) {
    int n = 0;
    for (Occ o = 1; o < 8192; o++) if (tc_alive(o)) {
        uint8_t k; uint32_t head; int ar; const Term *args;
        tc_node(tc_term(o), &k, &head, &ar, &args);
        if (k == K_APP && (int)head == con) n++;
    }
    return n;
}
static int count_ctrl(const TcIsaHostedCtx *h) {
    int n = 0;
    for (Occ o = 1; o < 8192; o++) { uint64_t w[3]; if (tc_alive(o) && tisa_fact_words(o, h->c_cell, 3, w) && w[0] == TISA_KEY_KIND_CTRL) n++; }
    return n;
}
/* the live register cells for r on the board (their number; the value of the last in *v) */
static int board_reg(const TcIsaHostedCtx *h, uint64_t r, uint64_t *v) {
    int n = 0;
    for (Occ o = 1; o < 8192; o++) {
        uint64_t w[3];
        if (tc_alive(o) && tisa_fact_words(o, h->c_cell, 3, w) && w[0] == TISA_KEY_KIND_REG && w[1] == r) { n++; *v = w[2]; }
    }
    return n;
}

/* ---- the routes that commit a firing ---- */
typedef struct { int rule; const Occ *take, *keep; const Term *inst; } Fire;
static Fire honest(const Pick *k) { return (Fire){ k->fr.rule, k->fr.take, k->fr.keep, NULL }; }
static Occ r_fire(Fire f) { return tc_fire(f.rule, f.take, f.keep, f.inst); }
static Occ r_reach(Fire f) {
    Term s[2] = { tc_space_term(TISA_SPACE_STATE), tc_space_term(TISA_SPACE_PROGRAM) };
    return tc_fire_reach(f.rule, f.take, f.keep, f.inst, s, 2);
}
static Occ r_prepared(Fire f) {
    TcPreparedStep st = { .rule = f.rule, .take = f.take, .keep = f.keep, .inst = f.inst };
    Occ o = 0;
    return tc_eval_prepared_ex(&st, false, false, false, false, true, NULL, NULL, NULL, NULL, &o) == TC_PREP_OK ? o : 0;
}
static Occ r_commit(Fire f) {
    TcPreparedStep st = { .rule = f.rule, .take = f.take, .keep = f.keep, .inst = f.inst };
    TcAdmissionReceipt rc;
    return tc_commit_prepared(&st, &rc) ? rc.out : 0;
}
static TcPreparedStep cur_step;
static int cur_left;
static bool cur_next(void *c, TcPreparedStep *o) { (void)c; if (!cur_left) return false; cur_left--; *o = cur_step; return true; }
static Occ r_cursor(Fire f) {
    cur_step = (TcPreparedStep){ .rule = f.rule, .take = f.take, .keep = f.keep, .inst = f.inst };
    cur_left = 1;
    TcCandidateCursor c = { NULL, cur_next };
    TcAdmissionReceipt rc;
    return tc_step_cursor(&c, &rc) == 1 ? rc.out : 0;
}
static int eval_only(Fire f) {
    TcPreparedStep st = { .rule = f.rule, .take = f.take, .keep = f.keep, .inst = f.inst };
    return tc_eval_prepared_ex(&st, false, false, false, false, false, NULL, NULL, NULL, NULL, NULL);
}
typedef Occ (*Route)(Fire);
static const struct { const char *name; Route r; } ROUTES[] = {
    { "tc_fire", r_fire }, { "tc_fire_reach", r_reach }, { "tc_eval_prepared_ex commit", r_prepared },
    { "tc_commit_prepared", r_commit }, { "tc_step_cursor", r_cursor },
};
#define NROUTES (int)(sizeof ROUTES / sizeof ROUTES[0])
static Occ r_search(int rule) {
    Term s[2] = { tc_space_term(TISA_SPACE_STATE), tc_space_term(TISA_SPACE_PROGRAM) };
    return tc_search_reach(rule, s, 2);
}
/* every route refuses f and leaves the board as it was */
static void refused_everywhere(Fire f, const char *what, int want_code) {
    char line[240];
    for (int i = 0; i < NROUTES; i++) {
        snap(&S0);
        Occ o = ROUTES[i].r(f);
        snprintf(line, sizeof line, "%s: %s, and nothing changes", ROUTES[i].name, what);
        HOLDS(o == 0 && unchanged(&S0), line);
    }
    snap(&S0);
    int rc = eval_only(f);
    snprintf(line, sizeof line, "tc_eval_prepared_ex evaluation-only: %s (code %d)", what, rc);
    HOLDS(rc != TC_PREP_OK && (want_code == 0 || rc == want_code) && unchanged(&S0), line);
}

static Prog P;
static TcIsaRuntimeFrame F2;

/* ---- the probe: 7 + 7 cannot be made 15 ---- */
static void probe_controls(void) {
    printf("probe (7 + 7 with a proposed 15)\n");
    /* (a) the probe's own rule: TAKE ctrl and dst, KEEP one cell, MAKE ctrl(next) and dst(new value) with
       next and the new value bound by nothing */
    for (int mode = 0; mode < 3; mode++) {      /* 0: protected first; 1: protected after the rule; 2: never protected */
        SETUP(tc_init(4096, 256));
        if (mode == 0) tc_protect(1);
        int s_key = tc_sort(0), s_word = tc_sort(0), s_cell = tc_sort(SORT_PROVABLE);
        Binder ca[5] = { { (uint16_t)s_key, 0, 0 }, { (uint16_t)s_word, 0, 0 }, { (uint16_t)s_word, 0, 0 }, { (uint16_t)s_word, 0, 0 }, { (uint16_t)s_word, 0, 0 } };
        int c_cell = tc_con((uint16_t)s_cell, 0, 5, ca);
        Binder vars[19];
        for (int i = 0; i < 19; i++) vars[i] = (Binder){ (uint16_t)s_word, 0, 0 };
        vars[0].sort = vars[7].sort = vars[14].sort = (uint16_t)s_key;
        SETUP(c_cell >= 0 && tc_ctx(19, vars));
        Rule r; memset(&r, 0, sizeof r);
        r.fresh = -1; r.ntake = 2; r.nkeep = 1; r.nmake_extra = 1;
        Term oc[5] = { tc_v(0), tc_v(1), tc_v(2), tc_v(3), tc_v(4) }, od[5] = { tc_v(7), tc_v(8), tc_v(9), tc_v(10), tc_v(11) };
        Term kp[5] = { tc_v(14), tc_v(15), tc_v(16), tc_v(17), tc_v(18) };
        Term nc[5] = { tc_v(0), tc_v(1), tc_v(2), tc_v(5), tc_v(6) }, nd[5] = { tc_v(7), tc_v(8), tc_v(9), tc_v(12), tc_v(13) };
        r.take[0] = (Pat){ tc_app(c_cell, oc), 1 }; r.take[1] = (Pat){ tc_app(c_cell, od), 1 };
        r.keep[0] = (Pat){ tc_app(c_cell, kp), 1 };
        r.make = (Pat){ tc_app(c_cell, nc), 1 }; r.make_extra[0] = (Pat){ tc_app(c_cell, nd), 1 };
        int rid = tc_rule(&r);
        if (mode == 0) { HOLDS(rid < 0, "the probe's edge rule (next and new value bound by nothing) is refused by tc_rule"); continue; }
        SETUP(rid >= 0);
        if (mode == 1) tc_protect(1);
#define W_(v) tc_name((uint16_t)s_word, (1ull << 62) | (v))
#define K_(v) tc_name((uint16_t)s_key, (1ull << 62) | (v))
        Term ctrl[5] = { K_(0), W_(0), W_(0), W_(7), W_(0) }, r0[5] = { K_(1), W_(0), W_(0), W_(7), W_(0) }, r1[5] = { K_(1), W_(1), W_(0), W_(7), W_(0) };
        Occ oc_ = tc_post(1, tc_app(c_cell, ctrl)), o0 = tc_post(1, tc_app(c_cell, r0)), o1 = tc_post(1, tc_app(c_cell, r1));
        SETUP(oc_ && o0 && o1);
        tc_seal();
        if (mode == 1) HOLDS(tc_rule_barred(rid), "installed before its space was protected, the seal bars it");
        else HOLDS(!tc_rule_barred(rid), "(control: in a space never protected the same rule is not barred)");
        for (int proposed = mode == 2 ? 15 : 14; proposed <= 15; proposed++) {
            Term inst[19] = { K_(0), W_(0), W_(0), W_(7), W_(0), W_(8), W_(0), K_(1), W_(0), W_(0), W_(7), W_(0), W_(proposed), W_(0),
                              K_(1), W_(1), W_(0), W_(7), W_(0) };
            Occ take[2] = { oc_, o0 }, keep[1] = { o1 };
            char what[120];
            if (mode == 1) {
                snprintf(what, sizeof what, "the barred probe rule with proposed %d does not fire (the shape is gone)", proposed);
                HOLDS(tc_fire(rid, take, keep, inst) == 0 && tc_alive(o0), what);
                continue;
            }
            Term w15 = W_(15);
            Occ nc2 = tc_fire(rid, take, keep, inst), nd2 = nc2 ? tc_last_extra(0) : 0;
            bool is15 = false;
            if (nd2) { uint8_t kd; uint32_t hd; int ar; const Term *args; tc_node(tc_term(nd2), &kd, &hd, &ar, &args); is15 = kd == K_APP && ar == 5 && args[3] == w15; }
            HOLDS(nc2 && is15, "(control: where nothing is protected the same rule and instantiation make 15, the gap the seal closes)");
        }
#undef W_
#undef K_
    }
    /* (b) the production path: 14 */
    prog_add(&P);
    uint64_t regs[TISA_NUM_VREGS] = { 0 };
    memset(&F2, 0, sizeof F2);
    regs[TISA_V0] = (uint64_t)(uintptr_t)&F2; regs[TISA_V1] = 7; regs[TISA_V2] = 7;
    TcIsaHostedRunResult res;
    HOLDS(tisa_try_eval_tcalc(&P.prog, &F2, regs, &res) && res.board_halted && res.outcome == TISA_OUTCOME_FIRED &&
          regs[TISA_V3] == 14 && F2.ret_val == 14, "7 + 7 gives 14 through the production sealed path");
    /* (c) by hand: every way to make it 15 */
    Act *a = &A_;
    SETUP(act_open(a, &P.prog, 7, 7, 0, NULL, true) && act_run_to(a, TISA_RECIPE_INSTR, TISA_OP_BIN));
    Pick k;
    SETUP(act_pick(a, &k) && k.out_hole >= 0 && k.out_is_op && k.next_hole >= 0);
    TcIsaHostedCtx *h = &a->h;
    Term w15 = tisa_w(h, 15);
    Term bind[TC_VARS] = { 0 };
    bind[k.out_hole] = w15;
    refused_everywhere((Fire){ k.fr.rule, k.fr.take, k.fr.keep, bind }, "STEP with the written value bound to 15 by the caller is refused", TC_PREP_SHAPE_UNIFY);
    bind[k.out_hole] = tisa_w(h, 14);
    refused_everywhere((Fire){ k.fr.rule, k.fr.take, k.fr.keep, bind }, "STEP with the written value bound by the caller, even to the right 14, is refused", TC_PREP_SHAPE_UNIFY);
    Term nbind[TC_VARS] = { 0 };
    nbind[k.next_hole] = tisa_w(h, k.pc);
    refused_everywhere((Fire){ k.fr.rule, k.fr.take, k.fr.keep, nbind }, "STEP with next bound by the caller to another point is refused", TC_PREP_SHAPE_UNIFY);
    Term cell15 = tisa_cell_pat(h, tisa_w(h, TISA_KEY_KIND_REG), tisa_w(h, 3), w15);
    Term ia[TI_N];
    for (int i = 0; i < TI_N; i++) ia[i] = tisa_w(h, k.p->w[i]);
    ia[TI_PC] = tisa_w(h, 99);
    Term instr99 = tc_app(h->c_instr, ia);
    HOLDS(cell15 && !tc_post(TISA_SPACE_STATE, cell15) && !tc_post_at(tc_space_term(TISA_SPACE_STATE), cell15, false),
          "a register cell holding 15, posted directly (tc_post, tc_post_at), is refused");
    HOLDS(instr99 && !tc_post(TISA_SPACE_PROGRAM, instr99), "an Instr posted directly is refused");
    Term c15[3] = { tisa_w(h, TISA_KEY_KIND_REG), tisa_w(h, 3), w15 };
    snap(&S0);
    HOLDS(!tc_flat_put(h->reg_occ[3], TISA_SPACE_STATE, h->c_cell, c15) && !tc_flat_out(h->reg_occ[3], TISA_SPACE_STATE, h->c_cell, c15) &&
          !tc_flat_put(0, TISA_SPACE_STATE, h->c_cell, c15) && !tc_flat_make(TISA_SPACE_STATE, (uint32_t)h->c_cell, h->s_cell, 3, c15) &&
          unchanged(&S0), "flat writes of a cell holding 15 (in place over v3's cell, or appended) are refused");
    Rule fresh_rule; memset(&fresh_rule, 0, sizeof fresh_rule);
    fresh_rule.fresh = -1; fresh_rule.make = (Pat){ cell15, TISA_SPACE_STATE };
    HOLDS(tc_rule(&fresh_rule) < 0, "a new rule making it is refused (rules close at the seal)");
    tc_ctx(0, NULL);
    tc_lemma(0, TISA_SPACE_STATE); tc_lemma_hyp(cell15);
    HOLDS(tc_lemma_end(-1) < 0, "a derived rule into STATE is refused");
    tc_lemma(0, TISA_SPACE_PROGRAM); tc_lemma_hyp(instr99);
    HOLDS(tc_lemma_end(-1) < 0, "a derived rule into PROGRAM is refused");
    tc_lemma(0, 9); tc_lemma_hyp(cell15);
    HOLDS(tc_lemma_end(-1) >= 0, "(control: the same derived rule into an open space is admitted after the seal)");
    Conv refl = { .kind = CV_REFL };
    HOLDS(tc_convert(h->reg_occ[3], &refl, tc_term(h->reg_occ[3])) == 0, "no conversion rewrites a cell");
    Occ old_ctrl = k.fr.take[0], old_dst = k.fr.take[1];
    Occ ncl = tc_fire(k.fr.rule, k.fr.take, k.fr.keep, NULL);
    Occ ndst = tc_last_extra(0);
    uint64_t v = 0;
    HOLDS(ncl && ndst && tisa_tcalc_read_cell_word(h, ndst, &v) && v == 14 && !tc_alive(old_ctrl) && !tc_alive(old_dst),
          "the honest STEP takes the control and destination cells and writes 14 into v3");
    snap(&S0);
    HOLDS(tc_fire(k.fr.rule, k.fr.take, k.fr.keep, NULL) == 0 && unchanged(&S0), "the consumed control and destination cells cannot be used again");
}

/* ---- every route admits the honest STEP, so the refusals elsewhere are the checks' doing
   (tc_search_reach, which tries every combination of live occurrences, is too slow for a hosted board;
   its positive control is in admission_kernel, its refusals of non-producers in rule_set_controls) ---- */
static void route_controls(void) {
    printf("every route admits the honest step (7 + 7)\n");
    for (int i = 0; i < NROUTES; i++) {
        Act *a = &A_;
        prog_add(&P);
        SETUP(act_open(a, &P.prog, 7, 7, 0, NULL, true) && act_run_to(a, TISA_RECIPE_INSTR, TISA_OP_BIN));
        Pick k;
        SETUP(act_pick(a, &k));
        TcIsaHostedCtx *h = &a->h;
        int rc = eval_only(honest(&k));
        Occ nc = ROUTES[i].r(honest(&k));
        uint64_t v = 0;
        bool ok = rc == TC_PREP_OK && nc && board_reg(h, 3, &v) == 1 && v == 14 && count_ctrl(h) == 1;
        char what[160];
        snprintf(what, sizeof what, "%s: the honest STEP writes 14 into v3 and moves the one control cell (evaluation-only agrees)", ROUTES[i].name);
        HOLDS(ok, what);
    }
}

/* ---- rule sets: the STEP rules admitted and the producers of STATE; an alternate producer barred ---- */
static void rule_set_controls(void) {
    printf("rule set\n");
    prog_mem(&P);
    Act *a = &A_;
    SETUP(act_open(a, &P.prog, 0, 0, 0, NULL, true));
    bool ok = true;
    for (int rid = 0; rid < tc_rule_count(); rid++) {
        TcInspectRule ir;
        ok &= tc_inspect_rule(rid, &ir, NULL) && ir.decl_rule.inputs == 0 && !tc_rule_barred(rid);
    }
    char what[200];
    snprintf(what, sizeof what, "every hosted rule (%d STEP rules for %d forms) is installed, range restricted with an empty input list, and not barred",
             tc_rule_count(), a->h.nforms);
    HOLDS(ok && tc_rule_count() > 0, what);
    int st = tc_space_publishers(TISA_SPACE_STATE, NULL, 0), pr = tc_space_publishers(TISA_SPACE_PROGRAM, NULL, 0);
    HOLDS(st == tc_rule_count() && pr == 0 && tc_space_publishers(3, NULL, 0) == -1 && tc_space_publishers(4, NULL, 0) == -1,
          "STATE's producers are the STEP rules, PROGRAM has none, and there is no other evidence space");
    int fns[8];
    bool fnbits = true;
    for (int rid = 0; rid < tc_rule_count(); rid++)
        if (tc_rule_fns(rid, fns, 8) > 0) fnbits &= (tc_rule_fibre(rid) & FIBRE_FN) != 0;
    HOLDS(fnbits, "every rule calling a sealed function carries FIBRE_FN");
    HOLDS(tisa_hosted_audit(&a->h), "the audit of the sealed rule set passes: each rule moves the one control cell and keeps one cell per key");
    /* alternate producers of a cell, installed before the seal but outside STATE's producer set */
    SETUP(act_open(a, &P.prog, 0, 0, 0, NULL, false));
    TcIsaHostedCtx *h = &a->h;
    Binder b[2] = { { h->s_word, 0, 0 }, { h->s_word, 0, 0 } };
    tc_ctx(2, b);
    Term reg = tisa_w(h, TISA_KEY_KIND_REG);
    Rule rogue; memset(&rogue, 0, sizeof rogue);
    rogue.fresh = -1; rogue.ntake = 1; rogue.take[0] = (Pat){ tisa_cell_pat(h, reg, tc_v(0), tc_v(1)), TISA_SPACE_STATE };
    rogue.make = (Pat){ tisa_cell_pat(h, reg, tc_v(0), tisa_w(h, 15)), TISA_SPACE_STATE };
    int rr = tc_rule(&rogue);
    SETUP(rr >= 0);
    Rule rogue2 = rogue;
    rogue2.ntake = 0; rogue2.nkeep = 1; rogue2.keep[0] = rogue.take[0];
    memset(&rogue2.take[0], 0, sizeof rogue2.take[0]);
    int rr2 = tc_rule(&rogue2);
    SETUP(rr2 >= 0);
    HOLDS(!tisa_hosted_seal(h), "the audit refuses a sealed rule set holding a barred rule");
    HOLDS(tc_rule_barred(rr) && tc_rule_barred(rr2), "the alternate producers (taking a cell, and keep-only) are barred by the seal");
    Occ t = h->reg_occ[3];
    refused_everywhere((Fire){ rr, &t, NULL, NULL }, "the alternate producer of a cell does not commit", TC_PREP_PUBLISH_GUARD);
    refused_everywhere((Fire){ rr2, NULL, &t, NULL }, "the keep-only alternate producer does not commit", TC_PREP_PUBLISH_GUARD);
    snap(&S0);
    HOLDS(tc_flat_fire(rr2, &t, NULL, 0) == 0 && unchanged(&S0), "tc_flat_fire: the keep-only alternate producer does not commit, and nothing changes");
    snap(&S0);
    HOLDS(r_search(rr) == 0 && r_search(rr2) == 0 && unchanged(&S0), "tc_search_reach: neither alternate producer commits, and nothing changes");
}

/* ---- wrong recipes, widths, destinations, stale and duplicate cells ---- */
static void recipe_controls(void) {
    printf("recipes, widths, destinations, stale and duplicate cells\n");
    prog_mem(&P);
    Act *a = &A_;
    SETUP(act_open(a, &P.prog, 0, 0, 0, NULL, true) && act_run_to(a, TISA_RECIPE_INSTR, TISA_OP_LOAD));
    TcIsaHostedCtx *h = &a->h;
    Pick k;
    SETUP(act_pick(a, &k) && k.cs->nbytes == 8 && k.cs->status == TISA_CASE_UPDATE);
    /* wrong recipe at the same point: every other form's STEP rules, with this point's premises */
    bool all = true;
    int tried = 0;
    for (int fi = 0; fi < h->nforms; fi++) {
        if (fi == k.p->form) continue;
        for (int ci = 0; ci < h->forms[fi].ncase; ci++) for (int m = 0; m < 16; m++) {
            int rid = h->r_step[fi][ci][m];
            if (rid < 0) continue;
            TcInspectRule ir;
            if (!tc_inspect_rule(rid, &ir, NULL)) { all = false; continue; }
            Occ take1[1] = { k.fr.take[0] };
            snap(&S0);
            all &= tc_fire(rid, ir.decl_rule.ntake == 2 ? k.fr.take : take1, k.fr.keep, NULL) == 0 && unchanged(&S0);
            tried++;
        }
    }
    char what[200];
    snprintf(what, sizeof what, "the STEP rules of every other form (another opcode, width or variant: %d rules over %d forms) refuse this point's premises", tried, h->nforms - 1);
    HOLDS(all && tried >= 4, what);
    Occ keep_other[TC_HYPS];
    memcpy(keep_other, k.fr.keep, sizeof keep_other);
    keep_other[0] = h->pt[0].instr;
    snap(&S0);
    HOLDS(tc_fire(k.fr.rule, k.fr.take, keep_other, NULL) == 0 && unchanged(&S0), "this form's STEP refuses the Instr of another point");
    /* changed width: the bytes one address on (the load guard fails after pack8 ran) */
    Occ shifted[TC_HYPS];
    memcpy(shifted, k.fr.keep, sizeof shifted);
    int nb0 = k.fr.nkeep - 8;
    for (int b = 0; b < 8; b++) {
        Occ *s = tisa_cell_slot(h, TISA_KEY_KIND_BYTE, k.e.v[HK0 + b] + 1u);
        shifted[nb0 + b] = s ? *s : 0;
    }
    refused_everywhere((Fire){ k.fr.rule, k.fr.take, shifted, NULL }, "STEP of the load with the bytes one address on (a late guard failure) is refused", TC_PREP_FN_GUARD);
    /* another destination than the recipe's */
    Occ wrong_dst[2] = { k.fr.take[0], h->reg_occ[4] };
    refused_everywhere((Fire){ k.fr.rule, wrong_dst, k.fr.keep, NULL }, "STEP writing another register than the recipe's destination is refused", TC_PREP_SHAPE_UNIFY);
    /* the honest STEP, then its consumed cells again */
    Occ old[2] = { k.fr.take[0], k.fr.take[1] };
    Occ nc = tc_fire(k.fr.rule, k.fr.take, k.fr.keep, NULL);
    SETUP(nc);
    Occ nd = tc_last_extra(0);
    tisa_cell_moved(h, k.fr.dkind, k.fr.dkey, old[1], nd);
    h->ctrl_occ = nc;
    HOLDS(act_reg(a, 3) == 0x1122334455667788ull, "the honest STEP loads the stored word");
    Occ stale1[2] = { old[0], nd }, stale2[2] = { nc, old[1] };
    snap(&S0);
    HOLDS(tc_fire(k.fr.rule, stale1, k.fr.keep, NULL) == 0 && tc_fire(k.fr.rule, stale2, k.fr.keep, NULL) == 0 && unchanged(&S0),
          "a consumed control cell or destination cell is refused");
    /* the destination is both operands */
    prog_alias(&P);
    SETUP(act_open(a, &P.prog, 21, 0, 0, NULL, true));
    TcIsaOutcome oc = TISA_OUTCOME_REFUSED; uint64_t hp = 0;
    HOLDS(tisa_hosted_run(&a->h, &oc, &hp) == 1 && oc == TISA_OUTCOME_FIRED && act_reg(a, 1) == 42, "v1 = v1 + v1 runs (destination aliasing both operands): 42");
    /* a second cell for a register, possible only when initialisation's uniqueness check is skipped */
    prog_add(&P);
    TcIsaHostedOptions o = { .fault_slot = -1, .dup_reg = true, .dup_reg_idx = 2, .dup_reg_val = 8, .skip_validation = true };
    SETUP(act_open(a, &P.prog, 7, 7, 0, &o, true) && act_run_to(a, TISA_RECIPE_INSTR, TISA_OP_BIN));
    h = &a->h;
    SETUP(act_pick(a, &k));
    Occ dupkeep[TC_HYPS];
    memcpy(dupkeep, k.fr.keep, sizeof dupkeep);
    for (int i = 0; i < k.fr.nkeep; i++) if (dupkeep[i] == h->reg_occ[2]) dupkeep[i] = h->extra_occ[0];
    nc = tc_fire(k.fr.rule, k.fr.take, dupkeep, NULL);
    uint64_t v = 0;
    HOLDS(nc && tisa_tcalc_read_cell_word(h, tc_last_extra(0), &v) && v == 15,
          "with validation skipped, a second cell for v2 (8) makes 7 + 8 = 15 admissible: one cell per key at initialisation is a trust item");
}

/* ---- a forced callback refusal and a late guard failure on every route ---- */
static bool fn_refuse(const uint64_t *in, uint64_t *out) { (void)in; (void)out; return false; }
static bool fn_add64_wrong(const uint64_t *in, uint64_t *out) { out[0] = in[0] + in[1] + 1u; return true; }
static void atomicity_controls(void) {
    printf("forced callback refusal, late guard failure: every route\n");
    prog_add(&P);
    TcIsaHostedOptions o = { .fault_slot = TFN_ADD64, .fault_fn = fn_refuse };
    Act *a = &A_;
    SETUP(act_open(a, &P.prog, 7, 7, 0, &o, true) && act_run_to(a, TISA_RECIPE_INSTR, TISA_OP_BIN));
    Pick k;
    SETUP(act_pick(a, &k));
    refused_everywhere(honest(&k), "STEP whose operation refuses (forced) is refused", TC_PREP_FN_GUARD);
    HOLDS(tc_alive(k.fr.take[0]) && tc_alive(k.fr.take[1]) && count_ctrl(&a->h) == 1, "after the refusals the control and destination cells are live, one control cell");
    /* a store phase into another byte than its checked address */
    prog_mem(&P);
    SETUP(act_open(a, &P.prog, 0, 0, 0, NULL, true) && act_run_to(a, TISA_RECIPE_STORE_BYTE, -1));
    TcIsaHostedCtx *h = &a->h;
    SETUP(act_pick(a, &k) && k.cs->status == TISA_CASE_UPDATE);
    Occ *wrong = tisa_cell_slot(h, TISA_KEY_KIND_BYTE, k.fr.dkey + 1u);
    SETUP(wrong && *wrong);
    Occ bad[2] = { k.fr.take[0], *wrong };
    refused_everywhere((Fire){ k.fr.rule, bad, k.fr.keep, NULL }, "STEP storing into another byte than the checked address (a late guard failure) is refused", TC_PREP_FN_GUARD);
    HOLDS(tc_fire(k.fr.rule, k.fr.take, k.fr.keep, NULL) != 0, "the same STEP at the checked address is admitted");
}

/* ---- initialisation ---- */
static void init_controls(void) {
    printf("initialisation\n");
    prog_add(&P);
    Act *a = &A_;
    TcIsaHostedOptions d1 = { .fault_slot = -1, .dup_instr = true, .dup_pc = 1 };
    HOLDS(!act_open(a, &P.prog, 7, 7, 0, &d1, true), "a second recipe at a point is rejected");
    TcIsaHostedOptions d2 = { .fault_slot = -1, .dup_ctrl = true };
    HOLDS(!act_open(a, &P.prog, 7, 7, 0, &d2, true), "a second control cell is rejected");
    TcIsaHostedOptions d3 = { .fault_slot = -1, .dup_reg = true, .dup_reg_idx = 5, .dup_reg_val = 1 };
    HOLDS(!act_open(a, &P.prog, 7, 7, 0, &d3, true), "a second cell for a register is rejected");
    HOLDS(act_open(a, &P.prog, 7, 7, 0, NULL, true), "(control: the same program without a duplicate opens)");
    d1.skip_validation = d2.skip_validation = d3.skip_validation = true;
    HOLDS(act_open(a, &P.prog, 7, 7, 0, &d1, true) && act_open(a, &P.prog, 7, 7, 0, &d2, true) && act_open(a, &P.prog, 7, 7, 0, &d3, true),
          "(control: with the validation skipped each duplicate opens, so the validation is what rejects it)");
}

/* ---- the control cell per activation ---- */
static void accounting_controls(void) {
    printf("the control cell\n");
    Act *a = &A_;
    TcIsaOutcome outcomes[3] = { TISA_OUTCOME_FIRED, TISA_OUTCOME_REFUSED, TISA_OUTCOME_EXHAUSTED };
    for (int i = 0; i < 3; i++) {
        prog_loop(&P, outcomes[i] == TISA_OUTCOME_EXHAUSTED ? TISA_OUTCOME_FIRED : outcomes[i]);
        SETUP(act_open(a, &P.prog, 0, 3, outcomes[i] == TISA_OUTCOME_EXHAUSTED ? 2 : 0, NULL, true));   /* 4 instructions run: 2 exhausts */
        TcIsaHostedCtx *h = &a->h;
        int cells0 = count_live(h->c_cell), steps = 0;
        bool one = true;
        for (;;) {
            uint64_t pc = act_pc(a);
            one &= count_ctrl(h) == 1 && count_live(h->c_cell) == cells0 && h->fires == (uint64_t)steps;
            if (TISA_POINT_IS_HALT(pc) || pc >= a->rt.npoints) break;
            if (!tisa_hosted_step(h, pc)) { one = false; break; }
            steps++;
        }
        uint64_t pc = act_pc(a);
        char what[200];
        snprintf(what, sizeof what, "outcome %d: at every point one control cell, the same number of cells, one firing per executed point (%d steps)", (int)outcomes[i], steps);
        HOLDS(one && steps > 0, what);
        snprintf(what, sizeof what, "outcome %d: the halted activation's control cell stands at its HALT point (%#llx)", (int)outcomes[i], (unsigned long long)pc);
        HOLDS(TISA_POINT_IS_HALT(pc) && TISA_POINT_HALT_OUTCOME(pc) == outcomes[i], what);
    }
    /* a no-verdict stop: the cell budget is spent before a step that writes */
    prog_add(&P);
    uint64_t regs[TISA_NUM_VREGS] = { 0 };
    memset(&F2, 0, sizeof F2);
    regs[TISA_V0] = (uint64_t)(uintptr_t)&F2; regs[TISA_V1] = 7; regs[TISA_V2] = 7;
    TcIsaHostedRunResult res;
    HOLDS(!tisa_try_eval_tcalc_with_limits(&P.prog, &F2, regs, 2048u, 37u + 2u, &res) && !res.has_verdict && res.tcalc_fires == 1,
          "a budget of one cell update stops at the second point with no verdict, after one firing");
}

/* ---- the sealed functions: contracts, identities, cases ---- */
static uint64_t rng = 0x9E3779B97F4A7C15ull;
static uint64_t rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static uint64_t pick_word(void) {
    static const uint64_t edge[] = { 0, 1, 2, 7, 31, 32, 63, 64, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0x100000000ull, INT64_MAX, (uint64_t)INT64_MIN, UINT64_MAX };
    return (rnd() & 3) ? rnd() : edge[rnd() % (sizeof edge / sizeof edge[0])];
}
/* The reference for an ALU, shift or compare function: tisa_scalar_eval on the instruction it stands for. */
static bool reference_scalar(int slot, uint64_t x, uint64_t y, uint64_t *v) {
    static const struct { int slot; TcIsaOpcode op; uint8_t sub; TcIsaValType ty; } map[] = {
#define B3(o, S) { TFN_##o##64, TISA_OP_BIN, S, TISA_TYPE_U64 }, { TFN_##o##32Z, TISA_OP_BIN, S, TISA_TYPE_U32Z }, { TFN_##o##32S, TISA_OP_BIN, S, TISA_TYPE_I32S }
        B3(ADD, TISA_BIN_ADD), B3(SUB, TISA_BIN_SUB), B3(AND, TISA_BIN_AND), B3(OR, TISA_BIN_OR), B3(XOR, TISA_BIN_XOR), B3(MUL, TISA_BIN_MULLO),
#undef B3
        { TFN_SHL64, TISA_OP_SHIFT, TISA_SHIFT_SHL, TISA_TYPE_U64 }, { TFN_SHRU64, TISA_OP_SHIFT, TISA_SHIFT_SHRU, TISA_TYPE_U64 },
        { TFN_SHRS64, TISA_OP_SHIFT, TISA_SHIFT_SHRS, TISA_TYPE_U64 }, { TFN_SHL32Z, TISA_OP_SHIFT, TISA_SHIFT_SHL, TISA_TYPE_U32Z },
        { TFN_SHRU32Z, TISA_OP_SHIFT, TISA_SHIFT_SHRU, TISA_TYPE_U32Z }, { TFN_SHRS32Z, TISA_OP_SHIFT, TISA_SHIFT_SHRS, TISA_TYPE_U32Z },
        { TFN_SHL32S, TISA_OP_SHIFT, TISA_SHIFT_SHL, TISA_TYPE_I32S }, { TFN_SHRU32S, TISA_OP_SHIFT, TISA_SHIFT_SHRU, TISA_TYPE_I32S },
        { TFN_SHRS32S, TISA_OP_SHIFT, TISA_SHIFT_SHRS, TISA_TYPE_I32S },
#define C2(c, S) { TFN_##c##64, TISA_OP_CMP, S, TISA_TYPE_U64 }, { TFN_##c##32, TISA_OP_CMP, S, TISA_TYPE_U32Z }
        C2(EQ, TISA_CMP_EQ), C2(NE, TISA_CMP_NE), C2(ULT, TISA_CMP_ULT), C2(ULE, TISA_CMP_ULE), C2(SLT, TISA_CMP_SLT), C2(SLE, TISA_CMP_SLE),
#undef C2
    };
    for (size_t i = 0; i < sizeof map / sizeof map[0]; i++) if (map[i].slot == slot) {
        TcIsaInstr ins = { .op = map[i].op, .subop = map[i].sub, .ty = map[i].ty, .dst = 3, .src1 = 0, .src2 = 1 };
        uint64_t regs[TISA_NUM_VREGS] = { x, y };
        if (map[i].op == TISA_OP_SHIFT) { if (y > 255) return false; ins.bit_width = (uint8_t)y; }
        return tisa_scalar_eval(&ins, regs, v);
    }
    return false;
}
/* The contracts, written from the contract texts and independently of the functions under test (the
   ALU, compare and shift entries through tisa_scalar_eval, the structured reference evaluator). */
typedef unsigned __int128 u128;
typedef __int128 i128;
static uint64_t sx32(uint64_t d) { return (uint64_t)(int64_t)(int32_t)(uint32_t)d; }
static bool ref_addr(uint64_t p, uint64_t i, uint64_t base, uint64_t len, uint64_t s, uint64_t d) {
    if (s > 3 || p < base || p - base > len) return false;
    u128 scaled = (u128)i << s;
    if (scaled >> 64) return false;
    i128 off1 = (i128)(p - base) + (i128)scaled, off = off1 + (i128)(int64_t)sx32(d);
    i128 mid = (i128)p + (i128)scaled, fin = mid + (i128)(int64_t)sx32(d);
    return off1 <= (i128)len && off >= 0 && off <= (i128)len && mid <= (i128)UINT64_MAX && fin >= 0 && fin <= (i128)UINT64_MAX;
}
static bool ref_access(uint64_t base, uint64_t len, uint64_t p, uint64_t d, unsigned w) {
    if (p < base || p - base > len) return false;
    i128 off = (i128)(p - base) + (i128)(int64_t)sx32(d);
    return off >= 0 && off + (i128)w <= (i128)len;
}
static bool ref_keys(const uint64_t *in, unsigned w) {
    for (unsigned b = 0; b < w; b++) if (in[2 + b] != in[0] + sx32(in[1]) + b) return false;
    return true;
}
/* the contract of entry slot: true with out[0] for an operation that has a value, the predicate for a guard */
static bool contract(int slot, const uint64_t *in, uint64_t *out) {
    uint64_t x = in[0], y = in[1];
    switch (slot) {
        case TFN_ZEXT32: *out = x & 0xFFFFFFFFull; return true;
        case TFN_SEXT32: *out = sx32(x); return true;
        case TFN_LOWBIT: *out = x & 1u; return true;
        case TFN_INC64: *out = x + 1u; return true;
        case TFN_EXTRACT: {
            uint64_t lsb = in[1], w = in[2], r = 0;
            if (w < 1 || w > 64 || lsb > 64 || lsb + w > 64) return false;
            for (uint64_t b = 0; b < w; b++) r |= ((x >> (lsb + b)) & 1u) << b;
            *out = r; return true;
        }
        case TFN_ADDR_INDEX: if (in[2] > 3) return false; *out = x + y * ((uint64_t)1 << in[2]) + sx32(in[3]); return true;
        case TFN_ADDR_NOIDX: *out = x + sx32(y); return true;
        case TFN_PACK1: case TFN_PACK4: case TFN_PACK8: {
            unsigned n = slot == TFN_PACK1 ? 1 : slot == TFN_PACK4 ? 4 : 8;
            uint64_t r = 0;
            for (unsigned b = 0; b < n; b++) { if (in[b] > 255) return false; r += in[b] * ((uint64_t)1 << (8 * b)); }
            *out = r; return true;
        }
        case TFN_BYTE_OF: if (y > 7) return false; *out = (x / ((uint64_t)1 << (8 * y))) % 256; return true;
        case TFN_G_IS_ZERO: return x == 0;
        case TFN_G_IS_ONE: return x == 1;
        case TFN_G_IS_BOOL: return x <= 1;
        case TFN_G_ABOVE_ONE: return x > 1;
        case TFN_G_VALID_BYTE: return x <= 255;
        case TFN_G_VALID_U32Z: return x < ((uint64_t)1 << 32);
        case TFN_G_VALID_I32S: return x == sx32(x);
        case TFN_G_EQ: return x == y;
        case TFN_G_NE: return x != y;
        case TFN_G_ULT: return x < y;
        case TFN_G_ULE: return x <= y;
        case TFN_G_FUEL_AVAILABLE: return x == 0 || y < x;
        case TFN_G_FUEL_EXHAUSTED: return x != 0 && y >= x;
        case TFN_G_ADDR_ADMITTED: return ref_addr(in[0], in[1], in[2], in[3], in[4], in[5]);
        case TFN_G_ADDR_REFUSED: return !ref_addr(in[0], in[1], in[2], in[3], in[4], in[5]);
        case TFN_G_ADDR_NOIDX_ADMITTED: return ref_addr(in[0], 0, in[1], in[2], 0, in[3]);
        case TFN_G_ADDR_NOIDX_REFUSED: return !ref_addr(in[0], 0, in[1], in[2], 0, in[3]);
        case TFN_G_ACCESS_IN1: return ref_access(in[0], in[1], in[2], in[3], 1);
        case TFN_G_ACCESS_IN4: return ref_access(in[0], in[1], in[2], in[3], 4);
        case TFN_G_ACCESS_IN8: return ref_access(in[0], in[1], in[2], in[3], 8);
        case TFN_G_ACCESS_OUT1: return !ref_access(in[0], in[1], in[2], in[3], 1);
        case TFN_G_ACCESS_OUT4: return !ref_access(in[0], in[1], in[2], in[3], 4);
        case TFN_G_ACCESS_OUT8: return !ref_access(in[0], in[1], in[2], in[3], 8);
        case TFN_G_LOAD_KEYS1: return ref_keys(in, 1);
        case TFN_G_LOAD_KEYS4: return ref_keys(in, 4);
        case TFN_G_LOAD_KEYS8: return ref_keys(in, 8);
        case TFN_G_STORE_KEY: return in[3] == in[0] + sx32(in[1]) + in[2];
        default: return reference_scalar(slot, x, y, out);
    }
}
/* inputs for entry slot: boundary words, and the shapes that reach both answers */
static void contract_inputs(int slot, uint64_t *in) {
    for (int j = 0; j < TC_FN_IN; j++) in[j] = pick_word();
    uint64_t base = (rnd() & 3) ? 0x10000 + rnd() % 4096 : UINT64_MAX - rnd() % 96;
    switch (slot) {
        case TFN_SHL64: case TFN_SHRU64: case TFN_SHRS64: case TFN_SHL32Z: case TFN_SHRU32Z: case TFN_SHRS32Z:
        case TFN_SHL32S: case TFN_SHRU32S: case TFN_SHRS32S: in[1] = rnd() % 70; break;
        case TFN_EXTRACT: in[1] = rnd() % 70; in[2] = rnd() % 70; break;
        case TFN_ADDR_INDEX: in[2] = rnd() % 6; break;
        case TFN_PACK1: case TFN_PACK4: case TFN_PACK8: for (int b = 0; b < 8; b++) in[b] = (rnd() % 16) ? rnd() % 256 : 256 + rnd() % 4; break;
        case TFN_BYTE_OF: in[1] = rnd() % 9; break;
        case TFN_G_IS_ZERO: case TFN_G_IS_ONE: case TFN_G_IS_BOOL: case TFN_G_ABOVE_ONE: in[0] = (rnd() & 1) ? rnd() % 4 : in[0]; break;
        case TFN_G_VALID_BYTE: in[0] = (rnd() & 1) ? rnd() % 512 : in[0]; break;
        case TFN_G_VALID_I32S: if (rnd() & 1) in[0] = sx32(in[0]); break;
        case TFN_G_EQ: case TFN_G_NE: case TFN_G_ULT: case TFN_G_ULE: if (rnd() & 1) in[1] = in[0] + rnd() % 3 - 1; break;
        case TFN_G_FUEL_AVAILABLE: case TFN_G_FUEL_EXHAUSTED: in[0] = (rnd() % 4) ? rnd() % 64 : 0; in[1] = rnd() % 70; break;
        case TFN_G_ADDR_ADMITTED: case TFN_G_ADDR_REFUSED:              /* p, i, base, len, s, d */
            in[2] = base; in[3] = (rnd() & 7) ? rnd() % 128 : pick_word();
            in[0] = base + rnd() % 160 - 16; in[1] = (rnd() & 7) ? rnd() % 24 : pick_word(); in[4] = rnd() % 5;
            in[5] = (rnd() & 3) ? (uint64_t)(int64_t)(int32_t)(rnd() % 64 - 32) : pick_word(); break;
        case TFN_G_ADDR_NOIDX_ADMITTED: case TFN_G_ADDR_NOIDX_REFUSED:  /* p, base, len, d */
            in[1] = base; in[2] = (rnd() & 7) ? rnd() % 128 : pick_word(); in[0] = base + rnd() % 160 - 16;
            in[3] = (rnd() & 3) ? (uint64_t)(int64_t)(int32_t)(rnd() % 64 - 32) : pick_word(); break;
        case TFN_G_ACCESS_IN1: case TFN_G_ACCESS_IN4: case TFN_G_ACCESS_IN8:
        case TFN_G_ACCESS_OUT1: case TFN_G_ACCESS_OUT4: case TFN_G_ACCESS_OUT8:  /* base, len, p, d */
            in[0] = base; in[1] = (rnd() & 7) ? rnd() % 48 : pick_word(); in[2] = base + rnd() % 64 - 8;
            in[3] = (rnd() & 3) ? (uint64_t)(int64_t)(int32_t)(rnd() % 48 - 24) : pick_word(); break;
        case TFN_G_LOAD_KEYS1: case TFN_G_LOAD_KEYS4: case TFN_G_LOAD_KEYS8:
            for (int b = 0; b < 8; b++) in[2 + b] = in[0] + sx32(in[1]) + (uint64_t)b;
            if (rnd() & 1) in[2 + rnd() % (slot == TFN_G_LOAD_KEYS1 ? 1 : slot == TFN_G_LOAD_KEYS4 ? 4 : 8)] ^= (uint64_t)1 << (rnd() % 64);
            break;
        case TFN_G_STORE_KEY: in[2] = rnd() % 8; in[3] = in[0] + sx32(in[1]) + in[2]; if (rnd() & 1) in[3] += 1 + rnd() % 3; break;
        default: break;
    }
}
/* entry slot's callback fn against its contract over n inputs: the mismatches; *seen gets bit 0 when the
   contract holds (or has a value), bit 1 when it does not */
static int contract_mismatches(int slot, TcFn fn, int n, unsigned *seen) {
    int bad = 0;
    for (int t = 0; t < n; t++) {
        uint64_t in[TC_FN_IN], out[TC_FN_OUT] = { 0 }, want = 0;
        contract_inputs(slot, in);
        bool got = fn(in, out), ref = contract(slot, in, &want);
        if (seen) *seen |= ref ? 1u : 2u;
        if (got != ref || (got && TISA_FNS[slot].kind == TC_FN_OP && out[0] != want)) bad++;
    }
    return bad;
}
static void function_controls(void) {
    printf("sealed functions\n");
    uint8_t abc[32];
    static const uint8_t abc_want[32] = { 0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
                                          0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad };
    tisa_sha256((const uint8_t *)"abc", 3, abc);
    HOLDS(!memcmp(abc, abc_want, 32), "the contract hash is SHA-256 (FIPS 180-4 test vector \"abc\")");
    prog_add(&P);
    Act *a = &A_;
    SETUP(act_open(a, &P.prog, 7, 7, 0, NULL, true));
    bool ident = tc_fn_count() == TFN_COUNT;
    for (int i = 0; ident && i < TFN_COUNT; i++) {
        TcFnInfo fi; char text[1024]; uint8_t h[32];
        int len = tisa_fn_contract(i, text, sizeof text);
        tisa_sha256((const uint8_t *)text, (size_t)len, h);
        ident = tc_fn_info(a->h.fn[i], &fi) && !strcmp(fi.name, TISA_FNS[i].name) && fi.kind == TISA_FNS[i].kind &&
                fi.nin == TISA_FNS[i].nin && fi.nout == TISA_FNS[i].nout && fi.fn == TISA_FNS[i].fn && !memcmp(fi.contract_sha256, h, 32);
    }
    HOLDS(ident, "every registry entry carries its function's name, kind, arity, the reviewed callback and SHA-256 of its contract");
    HOLDS(tc_fn("late", TC_FN_OP, 2, 1, fn_add64_wrong, (const uint8_t[32]){ 0 }) < 0, "after the seal no function is registered");
}

/* ---- the trust demonstration: a wrong function, no stored row ---- */
static void trust_controls(void) {
    printf("trust demonstration (a wrong function, no stored row)\n");
    Act *a = &A_;
    prog_add(&P);
    TcIsaHostedOptions w = { .fault_slot = TFN_ADD64, .fault_fn = fn_add64_wrong };
    TcIsaOutcome oc = TISA_OUTCOME_REFUSED; uint64_t hp = 0;
    SETUP(act_open(a, &P.prog, 7, 7, 0, &w, true));
    TcFnInfo fi; char text[1024]; uint8_t hash[32];
    tisa_sha256((const uint8_t *)text, (size_t)tisa_fn_contract(TFN_ADD64, text, sizeof text), hash);
    HOLDS(tisa_hosted_run(&a->h, &oc, &hp) == 1 && oc == TISA_OUTCOME_FIRED && act_reg(a, 3) == 15 &&
          tc_fn_info(a->h.fn[TFN_ADD64], &fi) && !strcmp(fi.name, "tisa.op.add64") && !memcmp(fi.contract_sha256, hash, 32) &&
          fi.fn == fn_add64_wrong,
          "a test-only theory registering add64 as x + y + 1 (same name and contract hash) admits 7 + 7 = 15: the kernel trusts the function");
    unsigned seen = 0;
    HOLDS(contract_mismatches(TFN_ADD64, fn_add64_wrong, 20000, &seen) > 0, "that wrong add64 fails the add64 contract test");
    /* the production registry: opened without test options */
    SETUP(act_open(a, &P.prog, 7, 7, 0, NULL, true));
    bool reviewed = tc_fn_count() == TFN_COUNT;
    for (int i = 0; reviewed && i < TFN_COUNT; i++) reviewed = tc_fn_info(a->h.fn[i], &fi) && fi.fn == TISA_FNS[i].fn;
    HOLDS(reviewed, "the production registry holds the reviewed callbacks only (no test function is in it)");
    int pass = 0, ops = 0, guards = 0, both = 0;
    char failed[200] = "";
    for (int i = 0; i < TFN_COUNT; i++) {
        if (!tc_fn_info(a->h.fn[i], &fi)) continue;
        seen = 0;
        int bad = contract_mismatches(i, fi.fn, 20000, &seen);
        pass += bad == 0;
        both += seen == 3u || (TISA_FNS[i].kind == TC_FN_OP && (seen & 1u));
        if (TISA_FNS[i].kind == TC_FN_OP) ops++; else guards++;
        if (bad && strlen(failed) < 150) { strcat(failed, " "); strcat(failed, TISA_FNS[i].name); }
    }
    char what[320];
    snprintf(what, sizeof what, "every production registry entry passes its contract test: %d/%d (%d operations, %d guards), 20000 inputs each%s%s",
             pass, TFN_COUNT, ops, guards, failed[0] ? "; failing:" : "", failed);
    HOLDS(pass == TFN_COUNT, what);
    snprintf(what, sizeof what, "the inputs reach both answers: %d/%d entries (every guard true and false; every operation with a value)", both, TFN_COUNT);
    HOLDS(both == TFN_COUNT, what);
}

/* the number of cases whose guards hold on e (the last one in *which) */
static int cases_holding(const TisaForm *f, const TisaEnv *e, int *which) {
    int n = 0;
    for (int c = 0; c < f->ncase; c++) {
        bool all = true;
        for (int g = 0; g < f->cs[c].nguard; g++) {
            uint64_t in[TC_FN_IN] = { 0 }, sc[TC_FN_OUT];
            for (int j = 0; j < f->cs[c].guard[g].nin; j++) in[j] = e->v[f->cs[c].guard[g].in[j]];
            all &= TISA_FNS[f->cs[c].guard[g].slot].fn(in, sc);
        }
        if (all) { n++; *which = c; }
    }
    return n;
}
/* every form's cases partition its words: exactly one case's guards hold, or none where the
   recipe has no step (a later store phase outside its region, as before the change) */
static void case_controls(void) {
    printf("cases\n");
    static const TcIsaInstr ins[] = {
        { .op = TISA_OP_IMM, .ty = TISA_TYPE_BOOL, .dst = 3, .imm64 = 1 },
        { .op = TISA_OP_MOV, .ty = TISA_TYPE_BOOL, .dst = 3, .src1 = 1 },
        { .op = TISA_OP_BIN, .subop = TISA_BIN_XOR, .ty = TISA_TYPE_BOOL, .dst = 3, .src1 = 1, .src2 = 2 },
        { .op = TISA_OP_SELECT, .ty = TISA_TYPE_BOOL, .dst = 3, .src1 = 1, .src2 = 2, .src3 = 4 },
        { .op = TISA_OP_SELECT, .ty = TISA_TYPE_U32Z, .dst = 3, .src1 = 1, .src2 = 2, .src3 = 4 },
        { .op = TISA_OP_ADDR, .dst = 3, .src1 = 1, .src2 = 2, .region_id = 0, .scale_lg2 = 3, .disp32 = -8 },
        { .op = TISA_OP_ADDR, .dst = 3, .src1 = 1, .src2 = 0xFF, .region_id = 0, .disp32 = 16 },
        { .op = TISA_OP_LOAD, .subop = TISA_MEM_U32, .ty = TISA_TYPE_I32S, .dst = 3, .src1 = 1, .region_id = 0, .disp32 = 4 },
        { .op = TISA_OP_LOAD, .subop = TISA_MEM_U64, .ty = TISA_TYPE_U64, .dst = 3, .src1 = 0, .region_id = TISA_REGION_FRAME, .disp32 = 176 },
    };
    TcIsaProgram prog;
    memset(&prog, 0, sizeof prog);
    prog.nregions = 1;
    int checked = 0, bad = 0;
    TcIsaPointRecipe recs[16];
    int nrec = 0;
    for (size_t i = 0; i < sizeof ins / sizeof ins[0]; i++) {
        memset(&recs[nrec], 0, sizeof recs[nrec]);
        recs[nrec].kind = TISA_RECIPE_INSTR; recs[nrec].instr = ins[i];
        recs[nrec].next_point = 1; recs[nrec].alt_point = 2; recs[nrec].fail_point = 3; nrec++;
    }
    TcIsaPointRecipe r = { .kind = TISA_RECIPE_FUEL, .next_point = 1, .fail_point = 3 };                       recs[nrec++] = r;
    r = (TcIsaPointRecipe){ .kind = TISA_RECIPE_BRANCH, .cond_reg = 1, .next_point = 1, .alt_point = 2, .fail_point = 3 }; recs[nrec++] = r;
    r = (TcIsaPointRecipe){ .kind = TISA_RECIPE_LOOP_ENTRY, .idx_reg = 1, .bound_reg = 2, .max_iters = 8, .next_point = 1, .fail_point = 3 }; recs[nrec++] = r;
    r = (TcIsaPointRecipe){ .kind = TISA_RECIPE_LOOP_HEADER, .idx_reg = 1, .bound_reg = 2, .max_iters = 8, .next_point = 1, .alt_point = 2, .fail_point = 3 }; recs[nrec++] = r;
    r = (TcIsaPointRecipe){ .kind = TISA_RECIPE_LOOP_LATCH, .idx_reg = 1, .bound_reg = 2, .max_iters = 8, .next_point = 1, .fail_point = 3 }; recs[nrec++] = r;
    r = (TcIsaPointRecipe){ .kind = TISA_RECIPE_STORE_BYTE, .instr = { .op = TISA_OP_STORE, .subop = TISA_MEM_U32, .src1 = 1, .src2 = 2, .region_id = 0, .disp32 = 2 },
                            .byte_phase = 0, .byte_width = 4, .next_point = 1, .fail_point = 3 }; recs[nrec++] = r;
    TcIsaHostedCtx *h = &A_.h;
    for (int i = 0; i < nrec; i++) {
        TisaForm f; uint64_t wds[TI_N] = { 0 };
        if (!tisa_point_form(&prog, &recs[i], 0x1000, &f, wds)) { bad++; continue; }
        for (int t = 0; t < 3000; t++) {
            TisaEnv e;
            memset(&e, 0, sizeof e);
            e.v[HIMM] = wds[TI_IMM]; e.v[HDISP] = wds[TI_DISP]; e.v[HA1] = wds[TI_A1]; e.v[HA2] = wds[TI_A2];
            for (int j = 0; j < 4; j++) e.v[HV1 + j] = (rnd() & 1) ? rnd() % 4 : pick_word();
            if (recs[i].kind == TISA_RECIPE_INSTR && (ins[i].op == TISA_OP_ADDR || ins[i].op == TISA_OP_LOAD) && ins[i].region_id == 0) {
                e.v[HV3] = 0x10000 + (rnd() % 64); e.v[HV4] = rnd() % 48;          /* base, len near the pointer */
                e.v[HV1] = e.v[HV3] + (rnd() % 64) - 8; e.v[HV2] = rnd() % 8;
            }
            if (recs[i].kind == TISA_RECIPE_STORE_BYTE) { e.v[HV3] = 0x10000; e.v[HV4] = rnd() % 16; e.v[HV1] = 0x10000 + rnd() % 20 - 2; }
            if (ins[i].region_id == TISA_REGION_FRAME && recs[i].kind == TISA_RECIPE_INSTR && ins[i].op == TISA_OP_LOAD)
                e.v[HV1] = (rnd() & 1) ? 0x1000 : pick_word();
            uint64_t a = e.v[HV1] + (uint64_t)(int64_t)(int32_t)(int64_t)e.v[HDISP];
            for (int b = 0; b < 8; b++) { e.v[HK0 + b] = a + (uint64_t)b; e.v[HB0 + b] = rnd() & 0xFF; }
            int holds = 0;
            for (int c = 0; c < f.ncase; c++) {
                bool all = true;
                for (int g = 0; g < f.cs[c].nguard; g++) {
                    uint64_t in[TC_FN_IN] = { 0 }, sc[TC_FN_OUT];
                    for (int j = 0; j < f.cs[c].guard[g].nin; j++) in[j] = e.v[f.cs[c].guard[g].in[j]];
                    all &= TISA_FNS[f.cs[c].guard[g].slot].fn(in, sc);
                }
                holds += all;
            }
            checked++;
            if (holds != 1) bad++;
        }
    }
    (void)h;
    char what[200];
    snprintf(what, sizeof what, "%d word assignments over %d forms: exactly one case's guards hold each time (%d otherwise)", checked, nrec, bad);
    HOLDS(bad == 0 && checked > 0, what);
    /* a later store phase has no FAIL case: at most one case holds, and none exactly where phase 0 on the
       same words takes its FAIL case (so an honest run, which passed phase 0, always has a step) */
    TcIsaPointRecipe s0 = recs[nrec - 1], s1 = s0;
    s1.byte_phase = 1;
    TisaForm f0, f1; uint64_t w0[TI_N] = { 0 }, w1[TI_N] = { 0 };
    int later = 0, later_bad = 0, none = 0;
    if (s0.kind == TISA_RECIPE_STORE_BYTE && tisa_point_form(&prog, &s0, 0x1000, &f0, w0) && tisa_point_form(&prog, &s1, 0x1000, &f1, w1)) {
        for (int t = 0; t < 3000; t++) {
            TisaEnv e0, e1;
            memset(&e0, 0, sizeof e0);
            e0.v[HDISP] = w0[TI_DISP]; e0.v[HV3] = 0x10000; e0.v[HV4] = rnd() % 16; e0.v[HV1] = 0x10000 + rnd() % 20 - 2; e0.v[HV2] = pick_word();
            e1 = e0; e0.v[HA1] = w0[TI_A1]; e1.v[HA1] = w1[TI_A1];
            int c0 = -1, c1 = -1, n0 = cases_holding(&f0, &e0, &c0), n1 = cases_holding(&f1, &e1, &c1);
            bool fail0 = n0 == 1 && f0.cs[c0].next == HFAIL;
            later++; none += n1 == 0;
            if (n0 != 1 || n1 > 1 || (n1 == 0) != fail0) later_bad++;
        }
    } else later_bad++;
    snprintf(what, sizeof what, "store phase 1 over %d word assignments: at most one case holds, none exactly where phase 0 takes FAIL (%d of them; %d otherwise)", later, none, later_bad);
    HOLDS(later_bad == 0 && none > 0 && none < later, what);
}

/* --registry: the registry as the kernel holds it after a production open, one line per function:
   id, name, kind, nin, nout, contract SHA-256, statement, contract text, and the proved image's SHA-256
   for a native entry or "-" (tab separated) */
static int print_registry(void) {
    prog_add(&P);
    if (!act_open(&A_, &P.prog, 7, 7, 0, NULL, true)) return 2;
    for (int i = 0; i < TFN_COUNT; i++) {
        TcFnInfo fi; char text[1024];
        if (!tc_fn_info(A_.h.fn[i], &fi)) return 2;
        tisa_fn_contract(i, text, sizeof text);
        printf("%d\t%s\t%s\t%u\t%u\t", A_.h.fn[i], fi.name, fi.kind == TC_FN_OP ? "operation" : "guard", (unsigned)fi.nin, (unsigned)fi.nout);
        for (int j = 0; j < 32; j++) printf("%02x", fi.contract_sha256[j]);
        int k = tisa_native_of(i);
        printf("\t%s\t%s\t%s\n", TISA_FNS[i].statement, text, k >= 0 ? TISA_NATIVE[k].image_sha256 : "-");
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc > 1 && !strcmp(argv[1], "--registry")) return print_registry();
    probe_controls();
    route_controls();
    rule_set_controls();
    recipe_controls();
    atomicity_controls();
    init_controls();
    accounting_controls();
    function_controls();
    trust_controls();
    case_controls();
    printf("admission_tisa: %s (%d violated, %d scenes not set up)\n", violations || setups ? "VIOLATED" : "holds", violations, setups);
    return violations ? 1 : setups ? 2 : 0;
}

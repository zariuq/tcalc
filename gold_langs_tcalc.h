#ifndef GOLD_LANGS_TCALC_H
#define GOLD_LANGS_TCALC_H

/*
 * gold_langs_tcalc.h — hand-written C interpreters for the Gold example languages and the
 *                      joined workflow that strings them together
 *
 * What this file is: each language's meaning below is C code; sends, receives and a few
 * commits are recorded as tcalc events (6 rules).  Nothing here is generated from the
 * authored GSLT modules.  The interpreters run in dl_tcalc's self-test (suites 12 and 13) on
 * the example files named below and are compared with constant expected results; the same
 * constants are what test_gold_joined_workflow.sh checks the native tools against.  Beyond
 * those files (checked 2026-11-11): the Erlang interpreter crashes on a run-time type error
 * (`fact(a)`); the OCaml interpreter evaluates `*` wrongly (`double 21` gives 2) and does not
 * type-check its input (the Hindley-Milner checker of part 3 is exercised on types built by
 * hand, not on parsed sources).
 *
 * Contents:
 *   1. Datalog (D0 + D1 Retained Explanations):
 *      - Three distinct completion regimes:
 *        (a) DL_COMPLETION_FACT_CLOSURE (set-deduplicated derived facts),
 *        (b) DL_COMPLETION_ONESTEP_EXPLANATIONS (retained one-step derivation keys
 *            (head, rule_id, prem0_occ, prem1_occ) with set-deduplicated facts),
 *        (c) DL_COMPLETION_UNBOUNDED_UNFOLDING (unfolded derivation trees without
 *            cycle collapse; stays PENDING on cyclic graphs under finite budget).
 *      - Cyclic graphs, multi-path explanation diamonds, points-to analysis,
 *        and nonlinear/multiway joins.
 *   2. First-Order CHR (C1):
 *      - Logical variables, compound terms, occurs-check unification, wakeups
 *        preserving occurrence IDs and propagation history (leq.chr,
 *        finite_terms.pl, resource_scheduler.pl).
 *   3. Erlang (E0 + E1), a parser and interpreter for the subset these two files use:
 *      - Processes, fresh PIDs, closures, separate `send` into per-(sender,receiver)
 *        in-flight FIFO network channels, `deliver` into process mailboxes, and
 *        selective `receive` with guards preserving unmatched mailbox prefixes
 *        and exact cursor resumption (gold_worker_pool.erl, gold_selective_reply.erl).
 *   4. OCaml (O0 + O1), a parser and interpreter for the subset these two files use, and a
 *      separate type checker:
 *      - Hindley-Milner rank-1 let-polymorphism with the value restriction,
 *        type-directed constructor disambiguation, explicit type refusals
 *        (mismatch, occurs-check, monomorphic lambda param, value restriction),
 *        strings, closures, recursive function groups, and first-match order
 *        (task_ranking.ml, tree_list.ml).
 *   5. Maude (M0 + M1), a parser for a subset and a rule-table evaluator:
 *      - Equations modulo ACU (assoc, comm, id), permitted vs. frozen
 *        rewrite contexts (`frozen` attribute), and conditional rules (`crl`)
 *        with multistep rewrite conditions (`=>*`) and resumable query search
 *        (resource_protocol.maude, nested_workflow.maude).
 *   6. Joined 5-Language Gold Workflow:
 *      Datalog evidence -> CHR resources -> Maude protocol checks ->
 *      OCaml ranking -> Erlang workers -> MeTTa results, explanations & receipts.
 */

#include "tcalc.h"
#include "bridge/tc_cetta_bridge.h"
#include "petta_tcalc_eval.h"

#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define GOLD_SPACE_DL_FACTS        2
#define GOLD_SPACE_DL_EXPLANATIONS 3
#define GOLD_SPACE_ER_NETWORK      4
#define GOLD_SPACE_ER_MAILBOX      5
#define GOLD_SPACE_ML_EVAL         6
#define GOLD_SPACE_MAUDE_STATE     7

/* =========================================================================
 * PART 1: Datalog D1 — Retained Explanations & 3 Distinct Completion Regimes
 * ========================================================================= */

typedef enum {
    DL_COMPLETION_FACT_CLOSURE         = 0,
    DL_COMPLETION_ONESTEP_EXPLANATIONS = 1,
    DL_COMPLETION_UNBOUNDED_UNFOLDING  = 2
} GoldDlCompletionMode;

typedef enum {
    DL_STATUS_COMPLETE         = 0,
    DL_STATUS_BUDGET_EXHAUSTED = 1
} GoldDlStatus;

typedef struct {
    char pred[32];
    int64_t a0;
    int64_t a1;
    uint32_t occ_id;
    uint32_t depth;
    uint64_t path_hash;
    Occ tc_occ;
} GoldDlFact;

typedef struct {
    char head_pred[32];
    int64_t a0;
    int64_t a1;
    uint32_t rule_id;
    uint32_t prem0_occ_id;
    uint32_t prem1_occ_id;
    Occ tc_occ;
} GoldDlExplanation;

typedef struct {
    uint32_t rule_id;
    char head_pred[32];
    char body0_pred[32];
    char body1_pred[32]; /* empty if 1-premise rule */
    bool is_nonlinear_self_eq; /* true if body0 requires a0 == a1 */
    bool is_reversed_single;   /* true if head(Y, X) :- body0(X, Y) */
    bool is_sym_join;          /* true if head(X, Y) :- body0(X, Z), body1(Y, Z) */
} GoldDlRule;

typedef struct {
    GoldDlCompletionMode mode;
    GoldDlStatus status;
    uint32_t max_steps;
    uint32_t steps_taken;

    uint32_t nfacts;
    GoldDlFact facts[256];

    uint32_t nexpls;
    GoldDlExplanation expls[512];

    uint32_t nrules;
    GoldDlRule rules[32];

    int sort_val;
    int sort_fact;
    int con_fact;
    int con_expl;
    int rule_derive_fact;
    int rule_record_expl;
    TcAdmissionProfile profile_set;
    TcAdmissionProfile profile_bag;
    uint64_t tc_admitted_facts;
    uint64_t tc_admitted_expls;
    TcAdmittedEvent last_event;
    TcAdmissionReceipt last_receipt;
} GoldDatalogEngine;

static inline void gold_dl_init(GoldDatalogEngine *dl, GoldDlCompletionMode mode, uint32_t max_steps) {
    memset(dl, 0, sizeof(*dl));
    dl->mode = mode;
    dl->max_steps = max_steps;

    tc_init(1u << 19, 1u << 18);
    tc_protect(GOLD_SPACE_DL_FACTS);
    tc_protect(GOLD_SPACE_DL_EXPLANATIONS);

    dl->sort_val = tc_sort(SORT_PURE | SORT_STRICT);
    dl->sort_fact = tc_sort(SORT_STRICT | SORT_PROVABLE);
    Binder b1 = { .sort = (uint16_t)dl->sort_val, .bound = 0, .deps = 0 };
    dl->con_fact = tc_con((uint16_t)dl->sort_fact, 0, 1, &b1);
    dl->con_expl = tc_con((uint16_t)dl->sort_fact, 0, 1, &b1);

    Binder ctx1[1] = { b1 };
    {
        tc_ctx(1, ctx1);
        Term v0 = tc_v(0);
        Rule r;
        memset(&r, 0, sizeof(r));
        r.fresh = -1;
        r.inputs = 0x1;   /* the fact the host derived */
        r.make = (Pat){ .t = tc_app(dl->con_fact, &v0), .space = GOLD_SPACE_DL_FACTS };
        r.nabsent = 1;
        r.absent[0] = (Pat){ .t = tc_app(dl->con_fact, &v0), .space = GOLD_SPACE_DL_FACTS };
        dl->rule_derive_fact = tc_rule(&r);
    }
    {
        tc_ctx(1, ctx1);
        Term v0 = tc_v(0);
        Rule r;
        memset(&r, 0, sizeof(r));
        r.fresh = -1;
        r.inputs = 0x1;   /* the explanation the host recorded */
        r.make = (Pat){ .t = tc_app(dl->con_expl, &v0), .space = GOLD_SPACE_DL_EXPLANATIONS };
        r.nabsent = 1;
        r.absent[0] = (Pat){ .t = tc_app(dl->con_expl, &v0), .space = GOLD_SPACE_DL_EXPLANATIONS };
        dl->rule_record_expl = tc_rule(&r);
    }
    tc_seal();
    dl->profile_set = tc_admission_custom_profile("gold_dl_set", true, true, false, false, NULL, NULL);
    dl->profile_bag = tc_admission_custom_profile("gold_dl_bag", false, true, false, false, NULL, NULL);
}

static inline bool gold_dl_has_fact(const GoldDatalogEngine *dl, const char *pred, int64_t a0, int64_t a1) {
    for (uint32_t i = 0; i < dl->nfacts; i++) {
        if (strcmp(dl->facts[i].pred, pred) == 0 &&
            dl->facts[i].a0 == a0 && dl->facts[i].a1 == a1)
            return true;
    }
    return false;
}

static inline bool gold_dl_has_expl(
    const GoldDatalogEngine *dl,
    const char *pred, int64_t a0, int64_t a1,
    uint32_t rule_id, uint32_t p0, uint32_t p1)
{
    for (uint32_t i = 0; i < dl->nexpls; i++) {
        const GoldDlExplanation *e = &dl->expls[i];
        if (e->rule_id == rule_id && e->prem0_occ_id == p0 && e->prem1_occ_id == p1 &&
            e->a0 == a0 && e->a1 == a1 && strcmp(e->head_pred, pred) == 0)
            return true;
    }
    return false;
}

static inline uint32_t gold_dl_count_expls_for(
    const GoldDatalogEngine *dl,
    const char *pred, int64_t a0, int64_t a1)
{
    uint32_t c = 0;
    for (uint32_t i = 0; i < dl->nexpls; i++) {
        const GoldDlExplanation *e = &dl->expls[i];
        if (e->a0 == a0 && e->a1 == a1 && strcmp(e->head_pred, pred) == 0)
            c++;
    }
    return c;
}

static inline bool gold_dl_emit_tc_fact(GoldDatalogEngine *dl, const char *pred, int64_t a0, int64_t a1, uint32_t depth, uint64_t path_hash) {
    if (dl->nfacts >= 256) return false;
    uint64_t fid = tc_fresh_name();
    while (fid == 0) fid = tc_fresh_name();
    Term inst[TC_VARS];
    memset(inst, 0, sizeof(inst));
    inst[0] = tc_name((uint16_t)dl->sort_val, fid);
    TcPreparedStep cand;
    memset(&cand, 0, sizeof(cand));
    cand.rule = dl->rule_derive_fact;
    cand.inst = inst;
    TcPreparedEffect eff;
    TcAdmissionReceipt rec;
    TcRefusalReason ref = TC_REFUSE_NONE;
    if (tc_bridge_execute_candidate(&cand, &dl->profile_set, &eff, &dl->last_event, &rec, &ref) != TC_BRIDGE_ADMITTED)
        return false;
    dl->last_receipt = rec;
    dl->tc_admitted_facts++;
    GoldDlFact *f = &dl->facts[dl->nfacts];
    snprintf(f->pred, sizeof(f->pred), "%s", pred);
    f->a0 = a0;
    f->a1 = a1;
    f->occ_id = dl->nfacts + 1u;
    f->depth = depth;
    f->path_hash = path_hash;
    f->tc_occ = rec.out;
    dl->nfacts++;
    return true;
}

static inline bool gold_dl_emit_tc_expl(
    GoldDatalogEngine *dl,
    const char *pred, int64_t a0, int64_t a1,
    uint32_t rule_id, uint32_t p0, uint32_t p1)
{
    if (dl->nexpls >= 512) return false;
    uint64_t fid = tc_fresh_name();
    while (fid == 0) fid = tc_fresh_name();
    Term inst[TC_VARS];
    memset(inst, 0, sizeof(inst));
    inst[0] = tc_name((uint16_t)dl->sort_val, fid);
    TcPreparedStep cand;
    memset(&cand, 0, sizeof(cand));
    cand.rule = dl->rule_record_expl;
    cand.inst = inst;
    TcPreparedEffect eff;
    TcAdmissionReceipt rec;
    TcRefusalReason ref = TC_REFUSE_NONE;
    if (tc_bridge_execute_candidate(&cand, &dl->profile_set, &eff, &dl->last_event, &rec, &ref) != TC_BRIDGE_ADMITTED)
        return false;
    dl->last_receipt = rec;
    dl->tc_admitted_expls++;
    GoldDlExplanation *e = &dl->expls[dl->nexpls++];
    snprintf(e->head_pred, sizeof(e->head_pred), "%s", pred);
    e->a0 = a0;
    e->a1 = a1;
    e->rule_id = rule_id;
    e->prem0_occ_id = p0;
    e->prem1_occ_id = p1;
    e->tc_occ = rec.out;
    return true;
}

static inline void gold_dl_add_edb(GoldDatalogEngine *dl, const char *pred, int64_t a0, int64_t a1) {
    if (dl->mode != DL_COMPLETION_UNBOUNDED_UNFOLDING && gold_dl_has_fact(dl, pred, a0, a1))
        return;
    gold_dl_emit_tc_fact(dl, pred, a0, a1, 0, ((uint64_t)a0 << 32) ^ (uint64_t)a1);
}

static inline void gold_dl_add_rule_1(
    GoldDatalogEngine *dl,
    uint32_t rule_id,
    const char *head_pred,
    const char *body0_pred,
    bool is_nonlinear_self_eq,
    bool is_reversed_single)
{
    if (dl->nrules >= 32) return;
    GoldDlRule *r = &dl->rules[dl->nrules++];
    memset(r, 0, sizeof(*r));
    r->rule_id = rule_id;
    snprintf(r->head_pred, sizeof(r->head_pred), "%s", head_pred);
    snprintf(r->body0_pred, sizeof(r->body0_pred), "%s", body0_pred);
    r->is_nonlinear_self_eq = is_nonlinear_self_eq;
    r->is_reversed_single = is_reversed_single;
}

static inline void gold_dl_add_rule_2(
    GoldDatalogEngine *dl,
    uint32_t rule_id,
    const char *head_pred,
    const char *body0_pred,
    const char *body1_pred,
    bool is_sym_join)
{
    if (dl->nrules >= 32) return;
    GoldDlRule *r = &dl->rules[dl->nrules++];
    memset(r, 0, sizeof(*r));
    r->rule_id = rule_id;
    snprintf(r->head_pred, sizeof(r->head_pred), "%s", head_pred);
    snprintf(r->body0_pred, sizeof(r->body0_pred), "%s", body0_pred);
    snprintf(r->body1_pred, sizeof(r->body1_pred), "%s", body1_pred);
    r->is_sym_join = is_sym_join;
}

static inline GoldDlStatus gold_dl_run(GoldDatalogEngine *dl) {
    bool changed = true;
    while (changed) {
        changed = false;
        uint32_t cur_nfacts = dl->nfacts;
        for (uint32_t r_idx = 0; r_idx < dl->nrules; r_idx++) {
            const GoldDlRule *r = &dl->rules[r_idx];
            if (r->body1_pred[0] == '\0') {
                /* 1-premise rule: head(X, Y) :- body0(X, Y) */
                for (uint32_t i = 0; i < cur_nfacts; i++) {
                    if (strcmp(dl->facts[i].pred, r->body0_pred) != 0) continue;
                    if (r->is_nonlinear_self_eq && dl->facts[i].a0 != dl->facts[i].a1) continue;
                    int64_t hx = r->is_reversed_single ? dl->facts[i].a1 : dl->facts[i].a0;
                    int64_t hy = r->is_reversed_single ? dl->facts[i].a0 : dl->facts[i].a1;
                    uint32_t p0_id = dl->facts[i].occ_id;

                    if (dl->mode == DL_COMPLETION_FACT_CLOSURE) {
                        if (!gold_dl_has_fact(dl, r->head_pred, hx, hy)) {
                            if (dl->max_steps > 0 && dl->steps_taken >= dl->max_steps) {
                                dl->status = DL_STATUS_BUDGET_EXHAUSTED;
                                return dl->status;
                            }
                            dl->steps_taken++;
                            gold_dl_emit_tc_fact(dl, r->head_pred, hx, hy, dl->facts[i].depth + 1u, 0);
                            changed = true;
                        }
                    } else if (dl->mode == DL_COMPLETION_ONESTEP_EXPLANATIONS) {
                        if (!gold_dl_has_fact(dl, r->head_pred, hx, hy)) {
                            gold_dl_emit_tc_fact(dl, r->head_pred, hx, hy, dl->facts[i].depth + 1u, 0);
                            changed = true;
                        }
                        if (!gold_dl_has_expl(dl, r->head_pred, hx, hy, r->rule_id, p0_id, 0)) {
                            if (dl->max_steps > 0 && dl->steps_taken >= dl->max_steps) {
                                dl->status = DL_STATUS_BUDGET_EXHAUSTED;
                                return dl->status;
                            }
                            dl->steps_taken++;
                            gold_dl_emit_tc_expl(dl, r->head_pred, hx, hy, r->rule_id, p0_id, 0);
                            changed = true;
                        }
                    } else {
                        /* DL_COMPLETION_UNBOUNDED_UNFOLDING */
                        uint64_t ph = (dl->facts[i].path_hash * 1099511628211ULL) ^ r->rule_id ^ p0_id;
                        bool seen_path = false;
                        for (uint32_t k = 0; k < dl->nfacts; k++) {
                            if (dl->facts[k].path_hash == ph &&
                                strcmp(dl->facts[k].pred, r->head_pred) == 0 &&
                                dl->facts[k].a0 == hx && dl->facts[k].a1 == hy) {
                                seen_path = true;
                                break;
                            }
                        }
                        if (!seen_path) {
                            if (dl->max_steps > 0 && dl->steps_taken >= dl->max_steps) {
                                dl->status = DL_STATUS_BUDGET_EXHAUSTED;
                                return dl->status;
                            }
                            dl->steps_taken++;
                            gold_dl_emit_tc_fact(dl, r->head_pred, hx, hy, dl->facts[i].depth + 1u, ph);
                            gold_dl_emit_tc_expl(dl, r->head_pred, hx, hy, r->rule_id, p0_id, 0);
                            changed = true;
                        }
                    }
                }
            } else {
                /* 2-premise join rule:
                 * Default: head(X, Z) :- body0(X, Y), body1(Y, Z)
                 * Symmetric join (e.g. alias): head(X, Y) :- body0(X, Z), body1(Y, Z) */
                for (uint32_t i = 0; i < cur_nfacts; i++) {
                    if (strcmp(dl->facts[i].pred, r->body0_pred) != 0) continue;
                    for (uint32_t j = 0; j < cur_nfacts; j++) {
                        if (strcmp(dl->facts[j].pred, r->body1_pred) != 0) continue;
                        int64_t hx = 0, hy = 0;
                        if (r->is_sym_join) {
                            if (dl->facts[i].a1 != dl->facts[j].a1) continue;
                            hx = dl->facts[i].a0;
                            hy = dl->facts[j].a0;
                        } else {
                            if (dl->facts[i].a1 != dl->facts[j].a0) continue;
                            hx = dl->facts[i].a0;
                            hy = dl->facts[j].a1;
                        }
                        uint32_t p0_id = dl->facts[i].occ_id;
                        uint32_t p1_id = dl->facts[j].occ_id;
                        uint32_t next_depth = (dl->facts[i].depth > dl->facts[j].depth
                                               ? dl->facts[i].depth : dl->facts[j].depth) + 1u;

                        if (dl->mode == DL_COMPLETION_FACT_CLOSURE) {
                            if (!gold_dl_has_fact(dl, r->head_pred, hx, hy)) {
                                if (dl->max_steps > 0 && dl->steps_taken >= dl->max_steps) {
                                    dl->status = DL_STATUS_BUDGET_EXHAUSTED;
                                    return dl->status;
                                }
                                dl->steps_taken++;
                                gold_dl_emit_tc_fact(dl, r->head_pred, hx, hy, next_depth, 0);
                                changed = true;
                            }
                        } else if (dl->mode == DL_COMPLETION_ONESTEP_EXPLANATIONS) {
                            if (!gold_dl_has_fact(dl, r->head_pred, hx, hy)) {
                                gold_dl_emit_tc_fact(dl, r->head_pred, hx, hy, next_depth, 0);
                                changed = true;
                            }
                            if (!gold_dl_has_expl(dl, r->head_pred, hx, hy, r->rule_id, p0_id, p1_id)) {
                                if (dl->max_steps > 0 && dl->steps_taken >= dl->max_steps) {
                                    dl->status = DL_STATUS_BUDGET_EXHAUSTED;
                                    return dl->status;
                                }
                                dl->steps_taken++;
                                gold_dl_emit_tc_expl(dl, r->head_pred, hx, hy, r->rule_id, p0_id, p1_id);
                                changed = true;
                            }
                        } else {
                            /* DL_COMPLETION_UNBOUNDED_UNFOLDING */
                            uint64_t ph = ((dl->facts[i].path_hash * 1099511628211ULL) ^
                                           (dl->facts[j].path_hash * 1469598103934665603ULL)) ^
                                          ((uint64_t)r->rule_id << 16) ^ ((uint64_t)p0_id << 8) ^ p1_id;
                            bool seen_path = false;
                            for (uint32_t k = 0; k < dl->nfacts; k++) {
                                if (dl->facts[k].path_hash == ph &&
                                    strcmp(dl->facts[k].pred, r->head_pred) == 0 &&
                                    dl->facts[k].a0 == hx && dl->facts[k].a1 == hy) {
                                    seen_path = true;
                                    break;
                                }
                            }
                            if (!seen_path) {
                                if (dl->max_steps > 0 && dl->steps_taken >= dl->max_steps) {
                                    dl->status = DL_STATUS_BUDGET_EXHAUSTED;
                                    return dl->status;
                                }
                                dl->steps_taken++;
                                gold_dl_emit_tc_fact(dl, r->head_pred, hx, hy, next_depth, ph);
                                gold_dl_emit_tc_expl(dl, r->head_pred, hx, hy, r->rule_id, p0_id, p1_id);
                                changed = true;
                            }
                        }
                    }
                }
            }
        }
    }
    dl->status = DL_STATUS_COMPLETE;
    return dl->status;
}

static inline uint32_t gold_dl_count_pred_facts(const GoldDatalogEngine *dl, const char *pred) {
    uint32_t c = 0;
    for (uint32_t i = 0; i < dl->nfacts; i++) {
        if (strcmp(dl->facts[i].pred, pred) == 0) c++;
    }
    return c;
}

/* =========================================================================
 * PART 2: Erlang E0 + E1 — Processes, Per-(Sender,Receiver) FIFO Channels,
 *         Mailboxes, Selective Receive & Resumable Cursor Machine over tcalc
 * ========================================================================= */

typedef struct {
    char tag[32];
    uint32_t sender_pid;
    int64_t req_id;
    int64_t payload;
    PettaAtom *term_payload;
} GoldErMsg;

typedef struct {
    bool alive;
    uint32_t sender_pid;
    uint32_t receiver_pid;
    uint32_t seq_no;
    GoldErMsg msg;
    Term tc_term;
    Occ tc_occ;
} GoldErEnvelope;

typedef struct {
    bool alive;
    GoldErMsg msg;
    Term tc_term;
    Occ tc_occ;
} GoldErMailboxEntry;

typedef enum {
    ER_CURSOR_IDLE    = 0,
    ER_CURSOR_PEEKING = 1,
    ER_CURSOR_DONE    = 2,
    ER_CURSOR_BLOCKED = 3
} GoldErCursorPhase;

typedef struct {
    GoldErCursorPhase phase;
    uint32_t pid;
    uint32_t scan_idx;
    char expected_tag[32];
    int64_t min_req_id; /* guard: msg.req_id >= min_req_id */
    uint32_t steps_executed;
    GoldErMsg matched_msg;
} GoldErReceiveCursor;

typedef struct {
    bool active;
    uint32_t pid;
    char role[32];
    uint32_t mbox_count;
    GoldErMailboxEntry mbox[64];
    int64_t last_result;
    bool is_actor;
    char spawn_fn[32];
    uint32_t spawn_argc;
    PettaAtom *spawn_args[4];
} GoldErProcess;

typedef struct {
    uint32_t next_pid;
    uint32_t nprocs;
    GoldErProcess procs[16];

    uint32_t nenvelopes;
    uint32_t next_seq;
    GoldErEnvelope network[128];

    int sort_val;
    int sort_er;
    int con_env;
    int con_mbox;
    int con_consumed;
    int rule_er_send;
    int rule_er_deliver;
    int rule_er_receive;
    TcAdmissionProfile profile_linear;

    uint64_t sends_admitted;
    uint64_t deliveries_admitted;
    uint64_t receives_admitted;
    TcAdmittedEvent last_event;
    TcAdmissionReceipt last_receipt;
} GoldErlangSystem;

static inline void gold_er_init(GoldErlangSystem *sys) {
    memset(sys, 0, sizeof(*sys));
    sys->next_pid = 1u;
    sys->next_seq = 1u;

    tc_init(1u << 19, 1u << 18);
    tc_protect(GOLD_SPACE_ER_NETWORK);
    tc_protect(GOLD_SPACE_ER_MAILBOX);

    sys->sort_val = tc_sort(SORT_PURE | SORT_STRICT);
    sys->sort_er = tc_sort(SORT_STRICT | SORT_PROVABLE);
    Binder b1 = { .sort = (uint16_t)sys->sort_val, .bound = 0, .deps = 0 };
    sys->con_env = tc_con((uint16_t)sys->sort_er, 0, 1, &b1);
    sys->con_mbox = tc_con((uint16_t)sys->sort_er, 0, 1, &b1);
    sys->con_consumed = tc_con((uint16_t)sys->sort_er, 0, 1, &b1);

    Binder ctx1[1] = { b1 };
    /* Rule 1: send (emit envelope into GOLD_SPACE_ER_NETWORK) */
    {
        tc_ctx(1, ctx1);
        Term v0 = tc_v(0);
        Rule r;
        memset(&r, 0, sizeof(r));
        r.fresh = -1;
        r.inputs = 0x1;   /* the envelope the host sends */
        r.make = (Pat){ .t = tc_app(sys->con_env, &v0), .space = GOLD_SPACE_ER_NETWORK };
        sys->rule_er_send = tc_rule(&r);
    }
    /* Rule 2: deliver (linear take from GOLD_SPACE_ER_NETWORK, make in GOLD_SPACE_ER_MAILBOX) */
    {
        tc_ctx(1, ctx1);
        Term v0 = tc_v(0);
        Rule r;
        memset(&r, 0, sizeof(r));
        r.fresh = -1;
        r.ntake = 1;
        r.take[0] = (Pat){ .t = tc_app(sys->con_env, &v0), .space = GOLD_SPACE_ER_NETWORK };
        r.make = (Pat){ .t = tc_app(sys->con_mbox, &v0), .space = GOLD_SPACE_ER_MAILBOX };
        sys->rule_er_deliver = tc_rule(&r);
    }
    /* Rule 3: selective receive (linear take from GOLD_SPACE_ER_MAILBOX, make consumed receipt) */
    {
        tc_ctx(1, ctx1);
        Term v0 = tc_v(0);
        Rule r;
        memset(&r, 0, sizeof(r));
        r.fresh = -1;
        r.ntake = 1;
        r.take[0] = (Pat){ .t = tc_app(sys->con_mbox, &v0), .space = GOLD_SPACE_ER_MAILBOX };
        r.make = (Pat){ .t = tc_app(sys->con_consumed, &v0), .space = GOLD_SPACE_ER_NETWORK };
        sys->rule_er_receive = tc_rule(&r);
    }
    tc_seal();
    sys->profile_linear = tc_admission_custom_profile("gold_er_linear", false, true, false, false, NULL, NULL);
}

static inline uint32_t gold_er_spawn(GoldErlangSystem *sys, const char *role) {
    if (sys->nprocs >= 16) return 0;
    GoldErProcess *p = &sys->procs[sys->nprocs++];
    memset(p, 0, sizeof(*p));
    p->active = true;
    p->pid = sys->next_pid++;
    snprintf(p->role, sizeof(p->role), "%s", role);
    return p->pid;
}

static inline GoldErProcess *gold_er_find_proc(GoldErlangSystem *sys, uint32_t pid) {
    for (uint32_t i = 0; i < sys->nprocs; i++) {
        if (sys->procs[i].active && sys->procs[i].pid == pid)
            return &sys->procs[i];
    }
    return NULL;
}

/* Separate `send`: places message in in-flight network channel without touching receiver's mailbox */
static inline bool gold_er_send(
    GoldErlangSystem *sys,
    uint32_t sender_pid,
    uint32_t receiver_pid,
    const char *tag,
    int64_t req_id,
    int64_t payload)
{
    if (sys->nenvelopes >= 128) return false;
    uint64_t fid = tc_fresh_name();
    while (fid == 0) fid = tc_fresh_name();
    Term t = tc_name((uint16_t)sys->sort_val, fid);
    Term inst[TC_VARS];
    memset(inst, 0, sizeof(inst));
    inst[0] = t;
    TcPreparedStep cand;
    memset(&cand, 0, sizeof(cand));
    cand.rule = sys->rule_er_send;
    cand.inst = inst;
    TcPreparedEffect eff;
    TcAdmissionReceipt rec;
    TcRefusalReason ref = TC_REFUSE_NONE;
    if (tc_bridge_execute_candidate(&cand, &sys->profile_linear, &eff, &sys->last_event, &rec, &ref) != TC_BRIDGE_ADMITTED)
        return false;
    sys->last_receipt = rec;
    sys->sends_admitted++;
    GoldErEnvelope *env = &sys->network[sys->nenvelopes++];
    env->alive = true;
    env->sender_pid = sender_pid;
    env->receiver_pid = receiver_pid;
    env->seq_no = sys->next_seq++;
    snprintf(env->msg.tag, sizeof(env->msg.tag), "%s", tag);
    env->msg.sender_pid = sender_pid;
    env->msg.req_id = req_id;
    env->msg.payload = payload;
    env->tc_term = t;
    env->tc_occ = rec.out;
    return true;
}

/* Separate `deliver`: delivers oldest in-flight message for (sender_pid, receiver_pid),
 * enforcing per-(sender, receiver) FIFO channel order! */
static inline bool gold_er_deliver_fifo(
    GoldErlangSystem *sys,
    uint32_t sender_pid,
    uint32_t receiver_pid)
{
    GoldErProcess *proc = gold_er_find_proc(sys, receiver_pid);
    if (!proc || proc->mbox_count >= 64) return false;
    for (uint32_t i = 0; i < sys->nenvelopes; i++) {
        GoldErEnvelope *env = &sys->network[i];
        if (!env->alive) continue;
        if ((sender_pid == 0 || env->sender_pid == sender_pid) &&
            env->receiver_pid == receiver_pid) {
            Occ take_occs[1] = { env->tc_occ };
            Term inst[TC_VARS];
            memset(inst, 0, sizeof(inst));
            inst[0] = env->tc_term;
            TcPreparedStep cand;
            memset(&cand, 0, sizeof(cand));
            cand.rule = sys->rule_er_deliver;
            cand.take = take_occs;
            cand.inst = inst;
            TcPreparedEffect eff;
            TcAdmissionReceipt rec;
            TcRefusalReason ref = TC_REFUSE_NONE;
            if (tc_bridge_execute_candidate(&cand, &sys->profile_linear, &eff, &sys->last_event, &rec, &ref) != TC_BRIDGE_ADMITTED)
                return false;
            sys->last_receipt = rec;
            sys->deliveries_admitted++;
            env->alive = false;
            GoldErMailboxEntry *me = &proc->mbox[proc->mbox_count++];
            me->alive = true;
            me->msg = env->msg;
            me->tc_term = env->tc_term;
            me->tc_occ = rec.out;
            return true;
        }
    }
    return false;
}

/* Begin a resumable selective-receive cursor over `pid`'s mailbox */
static inline GoldErReceiveCursor gold_er_receive_begin(
    uint32_t pid,
    const char *expected_tag,
    int64_t min_req_id)
{
    GoldErReceiveCursor cur;
    memset(&cur, 0, sizeof(cur));
    cur.phase = ER_CURSOR_PEEKING;
    cur.pid = pid;
    cur.scan_idx = 0;
    snprintf(cur.expected_tag, sizeof(cur.expected_tag), "%s", expected_tag);
    cur.min_req_id = min_req_id;
    return cur;
}

/* Advance selective-receive cursor by `budget` scan/remove steps.
 * Preserves all unmatched earlier messages in `proc->mbox` in their exact arrival order! */
static inline void gold_er_receive_resume(
    GoldErlangSystem *sys,
    GoldErReceiveCursor *cur,
    uint32_t budget)
{
    GoldErProcess *proc = gold_er_find_proc(sys, cur->pid);
    if (!proc || cur->phase == ER_CURSOR_DONE || cur->phase == ER_CURSOR_BLOCKED)
        return;

    uint32_t steps = 0;
    while (steps < budget && cur->phase == ER_CURSOR_PEEKING) {
        /* Advance scan_idx past already-consumed slots */
        while (cur->scan_idx < proc->mbox_count && !proc->mbox[cur->scan_idx].alive) {
            cur->scan_idx++;
        }
        if (cur->scan_idx >= proc->mbox_count) {
            cur->phase = ER_CURSOR_BLOCKED;
            return;
        }
        steps++;
        cur->steps_executed++;
        GoldErMailboxEntry *me = &proc->mbox[cur->scan_idx];
        if (strcmp(me->msg.tag, cur->expected_tag) == 0 &&
            me->msg.req_id >= cur->min_req_id) {
            /* Match! Linearly consume this mailbox entry on tcalc while leaving
             * all earlier unmatched entries (0 .. scan_idx-1) alive and untouched! */
            Occ take_occs[1] = { me->tc_occ };
            Term inst[TC_VARS];
            memset(inst, 0, sizeof(inst));
            inst[0] = me->tc_term;
            TcPreparedStep cand;
            memset(&cand, 0, sizeof(cand));
            cand.rule = sys->rule_er_receive;
            cand.take = take_occs;
            cand.inst = inst;
            TcPreparedEffect eff;
            TcAdmissionReceipt rec;
            TcRefusalReason ref = TC_REFUSE_NONE;
            if (tc_bridge_execute_candidate(&cand, &sys->profile_linear, &eff, &sys->last_event, &rec, &ref) == TC_BRIDGE_ADMITTED) {
                sys->last_receipt = rec;
                sys->receives_admitted++;
                me->alive = false;
                cur->matched_msg = me->msg;
                cur->phase = ER_CURSOR_DONE;
                proc->last_result = me->msg.payload;
                return;
            }
        }
        /* Did not match pattern+guard: keep message in mailbox and advance cursor */
        cur->scan_idx++;
    }
}

static inline uint32_t gold_er_alive_mbox_count(const GoldErProcess *proc) {
    uint32_t c = 0;
    for (uint32_t i = 0; i < proc->mbox_count; i++) {
        if (proc->mbox[i].alive) c++;
    }
    return c;
}

/* =========================================================================
 * PART 2B: Erlang E1 Source Parser & Multi-Process Evaluator over tcalc
 *          (`gold_worker_pool.erl`, `gold_selective_reply.erl`)
 * ========================================================================= */

typedef struct {
    char fname[32];
    uint32_t arity;
    PettaAtom *params[6];
    char guard_str[64];
    char body_str[512];
} GoldErClause;

typedef struct {
    char mod_name[32];
    uint32_t nclauses;
    GoldErClause clauses[32];
} GoldErModule;

static inline const char *gold_er_skip_ws(const char *p) {
    while (*p) {
        if (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n') { p++; continue; }
        if (*p == '%') { while (*p && *p != '\n') p++; continue; }
        break;
    }
    return p;
}

static inline PettaAtom *gold_er_make_tag(const char *tag, uint32_t n, PettaAtom **args) {
    PettaAtom **all = (PettaAtom **)calloc((size_t)n + 1u, sizeof(PettaAtom *));
    all[0] = petta_atom_sym(tag);
    for (uint32_t i = 0; i < n; i++) all[i + 1u] = args[i];
    PettaAtom *r = petta_atom_expr(n + 1u, all);
    free(all);
    return r;
}

/* Parse an Erlang term/pattern into a PettaAtom:
 *   - Variables (uppercase or `_`) -> PETTA_ATOM_VAR (or `PETTA_ATOM_SYM("_")` for `_`)
 *   - Atoms (lowercase) -> PETTA_ATOM_SYM
 *   - Integers -> PETTA_ATOM_INT
 *   - Tuples `{a, b}` -> `({} a b)`
 *   - Lists `[]` -> `[]`, `[h | t]` -> `(| h t)`, `[a, b]` -> `(| a (| b []))`
 *   - Pattern alias `P = V` -> `(=pat P V)` */
static inline PettaAtom *gold_er_parse_term(const char **pp) {
    const char *p = gold_er_skip_ws(*pp);
    if (!*p) return NULL;
    PettaAtom *lhs = NULL;
    if (*p == '{') {
        p++;
        PettaAtom *items[8];
        uint32_t n = 0;
        p = gold_er_skip_ws(p);
        while (*p && *p != '}' && n < 8u) {
            items[n++] = gold_er_parse_term(&p);
            p = gold_er_skip_ws(p);
            if (*p == ',') p = gold_er_skip_ws(p + 1);
        }
        if (*p == '}') p++;
        lhs = gold_er_make_tag("{}", n, items);
    } else if (*p == '[') {
        p++;
        p = gold_er_skip_ws(p);
        if (*p == ']') {
            p++;
            lhs = petta_atom_sym("[]");
        } else {
            PettaAtom *elems[16];
            uint32_t ne = 0;
            PettaAtom *tail = NULL;
            while (*p && *p != ']' && ne < 16u) {
                elems[ne++] = gold_er_parse_term(&p);
                p = gold_er_skip_ws(p);
                if (*p == ',') {
                    p = gold_er_skip_ws(p + 1);
                } else if (*p == '|') {
                    p = gold_er_skip_ws(p + 1);
                    tail = gold_er_parse_term(&p);
                    p = gold_er_skip_ws(p);
                    break;
                }
            }
            if (*p == ']') p++;
            if (!tail) tail = petta_atom_sym("[]");
            for (int32_t i = (int32_t)ne - 1; i >= 0; i--) {
                PettaAtom *cargs[2] = { elems[i], tail };
                tail = gold_er_make_tag("|", 2, cargs);
            }
            lhs = tail;
        }
    } else if (*p == '<' && strncmp(p, "<0.", 3) == 0) {
        uint32_t pid = (uint32_t)strtoul(p + 3, (char **)&p, 10);
        while (*p && *p != '>') p++;
        if (*p == '>') p++;
        PettaAtom *pa = petta_atom_int((int64_t)pid);
        lhs = gold_er_make_tag("Pid", 1, &pa);
    } else if ((*p == '-' && isdigit((unsigned char)p[1])) || isdigit((unsigned char)*p)) {
        int64_t v = strtoll(p, (char **)&p, 10);
        lhs = petta_atom_int(v);
    } else {
        char id[64] = {0};
        size_t il = 0;
        while (*p && (isalnum((unsigned char)*p) || *p == '_')) {
            if (il + 1 < sizeof(id)) id[il++] = *p;
            p++;
        }
        if (il == 0) return NULL;
        if (strcmp(id, "_") == 0) {
            lhs = petta_atom_sym("_");
        } else if (isupper((unsigned char)id[0]) || id[0] == '_') {
            lhs = petta_atom_var(id);
        } else {
            lhs = petta_atom_sym(id);
        }
    }
    p = gold_er_skip_ws(p);
    if (*p == '=' && p[1] != '=' && p[1] != '<') {
        p = gold_er_skip_ws(p + 1);
        PettaAtom *rhs = gold_er_parse_term(&p);
        PettaAtom *pargs[2] = { lhs, rhs };
        lhs = gold_er_make_tag("=pat", 2, pargs);
    }
    *pp = p;
    return lhs;
}

static inline void gold_er_format_atom(const PettaAtom *a, char *buf, size_t cap) {
    if (!a || cap == 0) return;
    if (a->kind == PETTA_ATOM_INT) {
        snprintf(buf, cap, "%" PRId64, a->ival);
        return;
    }
    if (a->kind == PETTA_ATOM_SYM || a->kind == PETTA_ATOM_VAR) {
        snprintf(buf, cap, "%s", a->text);
        return;
    }
    if (a->kind == PETTA_ATOM_EXPR && a->arity >= 1 && a->args[0]->kind == PETTA_ATOM_SYM) {
        const char *tag = a->args[0]->text;
        if (strcmp(tag, "{}") == 0) {
            size_t pos = (size_t)snprintf(buf, cap, "{");
            for (uint32_t i = 1; i < a->arity; i++) {
                if (i > 1) pos += (size_t)snprintf(buf + pos, cap > pos ? cap - pos : 0, ", ");
                char sub[128] = {0};
                gold_er_format_atom(a->args[i], sub, sizeof(sub));
                pos += (size_t)snprintf(buf + pos, cap > pos ? cap - pos : 0, "%s", sub);
            }
            snprintf(buf + pos, cap > pos ? cap - pos : 0, "}");
            return;
        }
        if (strcmp(tag, "|") == 0 && a->arity == 3) {
            size_t pos = (size_t)snprintf(buf, cap, "[");
            const PettaAtom *cur = a;
            bool first = true;
            while (cur && cur->kind == PETTA_ATOM_EXPR && cur->arity == 3 &&
                   cur->args[0]->kind == PETTA_ATOM_SYM && strcmp(cur->args[0]->text, "|") == 0) {
                if (!first) pos += (size_t)snprintf(buf + pos, cap > pos ? cap - pos : 0, ", ");
                first = false;
                char sub[128] = {0};
                gold_er_format_atom(cur->args[1], sub, sizeof(sub));
                pos += (size_t)snprintf(buf + pos, cap > pos ? cap - pos : 0, "%s", sub);
                cur = cur->args[2];
            }
            if (cur && !(cur->kind == PETTA_ATOM_SYM && strcmp(cur->text, "[]") == 0)) {
                char sub[128] = {0};
                gold_er_format_atom(cur, sub, sizeof(sub));
                pos += (size_t)snprintf(buf + pos, cap > pos ? cap - pos : 0, " | %s", sub);
            }
            snprintf(buf + pos, cap > pos ? cap - pos : 0, "]");
            return;
        }
        if (strcmp(tag, "Pid") == 0 && a->arity == 2 && a->args[1]->kind == PETTA_ATOM_INT) {
            snprintf(buf, cap, "<0.%" PRId64 ".0>", a->args[1]->ival);
            return;
        }
    }
    petta_atom_render(a, buf, cap);
}

static inline bool gold_er_match_pat(
    const PettaAtom *pat,
    const PettaAtom *val,
    const PettaEnv *pin_env,
    PettaEnv *env)
{
    if (!pat || !val) return false;
    if (pat->kind == PETTA_ATOM_SYM && strcmp(pat->text, "_") == 0) return true;
    if (pat->kind == PETTA_ATOM_VAR) {
        const PettaAtom *pinned = pin_env ? petta_env_lookup(pin_env, pat->text) : NULL;
        if (pinned) return petta_atom_eq(pinned, val);
        const PettaAtom *existing = petta_env_lookup(env, pat->text);
        if (existing) return petta_atom_eq(existing, val);
        petta_env_bind(env, pat->text, val);
        return true;
    }
    if (pat->kind == PETTA_ATOM_EXPR && pat->arity == 3 &&
        pat->args[0]->kind == PETTA_ATOM_SYM && strcmp(pat->args[0]->text, "=pat") == 0) {
        return gold_er_match_pat(pat->args[1], val, pin_env, env) &&
               gold_er_match_pat(pat->args[2], val, pin_env, env);
    }
    if (pat->kind != val->kind) return false;
    if (pat->kind == PETTA_ATOM_INT) return pat->ival == val->ival;
    if (pat->kind == PETTA_ATOM_SYM) return strcmp(pat->text, val->text) == 0;
    if (pat->kind == PETTA_ATOM_EXPR) {
        if (pat->arity != val->arity) return false;
        for (uint32_t i = 0; i < pat->arity; i++) {
            if (!gold_er_match_pat(pat->args[i], val->args[i], pin_env, env)) return false;
        }
        return true;
    }
    return false;
}

static inline bool gold_er_eval_guard(const char *guard_str, const PettaEnv *env) {
    const char *p = gold_er_skip_ws(guard_str);
    if (!*p) return true;
    if (strncmp(p, "is_integer(", 11) == 0) {
        p += 11;
        PettaAtom *arg = gold_er_parse_term(&p);
        const PettaAtom *v = (arg && arg->kind == PETTA_ATOM_VAR) ? petta_env_lookup(env, arg->text) : arg;
        bool ok = (v && v->kind == PETTA_ATOM_INT);
        petta_atom_free(arg);
        return ok;
    }
    PettaAtom *la = gold_er_parse_term(&p);
    p = gold_er_skip_ws(p);
    char op[8] = {0};
    size_t ol = 0;
    while (*p && (*p == '>' || *p == '<' || *p == '=')) {
        if (ol + 1 < sizeof(op)) op[ol++] = *p;
        p++;
    }
    PettaAtom *ra = gold_er_parse_term(&p);
    const PettaAtom *lv = (la && la->kind == PETTA_ATOM_VAR) ? petta_env_lookup(env, la->text) : la;
    const PettaAtom *rv = (ra && ra->kind == PETTA_ATOM_VAR) ? petta_env_lookup(env, ra->text) : ra;
    bool res = false;
    if (lv && rv && lv->kind == PETTA_ATOM_INT && rv->kind == PETTA_ATOM_INT) {
        if (strcmp(op, ">") == 0) res = (lv->ival > rv->ival);
        else if (strcmp(op, "<") == 0) res = (lv->ival < rv->ival);
        else if (strcmp(op, ">=") == 0) res = (lv->ival >= rv->ival);
        else if (strcmp(op, "=<") == 0 || strcmp(op, "<=") == 0) res = (lv->ival <= rv->ival);
        else if (strcmp(op, "==") == 0) res = (lv->ival == rv->ival);
    }
    petta_atom_free(la);
    petta_atom_free(ra);
    return res;
}

static inline bool gold_er_parse_source(GoldErModule *mod, const char *src) {
    memset(mod, 0, sizeof(*mod));
    const char *p = src;
    while (*p) {
        p = gold_er_skip_ws(p);
        if (!*p) break;
        if (*p == '-') {
            if (strncmp(p, "-module(", 8) == 0) {
                p += 8;
                size_t ml = 0;
                while (*p && *p != ')' && ml + 1 < sizeof(mod->mod_name)) mod->mod_name[ml++] = *p++;
            }
            while (*p && *p != '.') p++;
            if (*p == '.') p++;
            continue;
        }
        /* Parse function clauses: fname(p1, ...) [when Guard] -> Body (; | .) */
        while (*p && mod->nclauses < 32u) {
            p = gold_er_skip_ws(p);
            if (!*p || *p == '-') break;
            GoldErClause *cl = &mod->clauses[mod->nclauses];
            memset(cl, 0, sizeof(*cl));
            size_t fl = 0;
            while (*p && (isalnum((unsigned char)*p) || *p == '_')) {
                if (fl + 1 < sizeof(cl->fname)) cl->fname[fl++] = *p;
                p++;
            }
            if (fl == 0) { p++; break; }
            p = gold_er_skip_ws(p);
            if (*p == '(') {
                p++;
                p = gold_er_skip_ws(p);
                while (*p && *p != ')' && cl->arity < 6u) {
                    cl->params[cl->arity++] = gold_er_parse_term(&p);
                    p = gold_er_skip_ws(p);
                    if (*p == ',') p = gold_er_skip_ws(p + 1);
                }
                if (*p == ')') p++;
            }
            p = gold_er_skip_ws(p);
            if (strncmp(p, "when", 4) == 0 && (p[4] == ' ' || p[4] == '\t')) {
                p = gold_er_skip_ws(p + 4);
                const char *arrow = strstr(p, "->");
                if (arrow) {
                    size_t gl = (size_t)(arrow - p);
                    while (gl > 0 && (p[gl - 1] == ' ' || p[gl - 1] == '\t')) gl--;
                    if (gl >= sizeof(cl->guard_str)) gl = sizeof(cl->guard_str) - 1u;
                    memcpy(cl->guard_str, p, gl);
                    p = arrow;
                }
            }
            if (strncmp(p, "->", 2) == 0) p += 2;
            p = gold_er_skip_ws(p);
            /* Scan clause body up to top-level `;` or `.` (respecting `receive ... end`, `fun ... end`, `(...)`, `[...]`, `{...}`) */
            size_t bl = 0;
            int depth = 0, end_depth = 0;
            while (*p) {
                if (depth == 0 && end_depth == 0 && (*p == ';' || *p == '.')) break;
                if ((strncmp(p, "receive", 7) == 0 && !isalnum((unsigned char)p[7]) && p[7] != '_') ||
                    (strncmp(p, "fun", 3) == 0 && !isalnum((unsigned char)p[3]) && p[3] != '_')) {
                    end_depth++;
                } else if (strncmp(p, "end", 3) == 0 && !isalnum((unsigned char)p[3]) && p[3] != '_' &&
                           (bl == 0 || (!isalnum((unsigned char)cl->body_str[bl - 1]) && cl->body_str[bl - 1] != '_'))) {
                    if (end_depth > 0) end_depth--;
                }
                if (*p == '(' || *p == '[' || *p == '{') depth++;
                else if ((*p == ')' || *p == ']' || *p == '}') && depth > 0) depth--;
                if (bl + 1 < sizeof(cl->body_str)) cl->body_str[bl++] = *p;
                p++;
            }
            mod->nclauses++;
            if (*p == ';') { p++; continue; }
            if (*p == '.') { p++; break; }
        }
    }
    return mod->nclauses > 0;
}

static inline void gold_er_module_destroy(GoldErModule *mod) {
    if (!mod) return;
    for (uint32_t i = 0; i < mod->nclauses; i++) {
        for (uint32_t k = 0; k < mod->clauses[i].arity; k++) {
            petta_atom_free(mod->clauses[i].params[k]);
        }
    }
    memset(mod, 0, sizeof(*mod));
}

static inline void gold_er_destroy(GoldErlangSystem *sys) {
    if (!sys) return;
    for (uint32_t i = 0; i < sys->nenvelopes; i++) {
        petta_atom_free(sys->network[i].msg.term_payload);
        sys->network[i].msg.term_payload = NULL;
    }
    for (uint32_t p = 0; p < sys->nprocs; p++) {
        for (uint32_t a = 0; a < sys->procs[p].spawn_argc; a++) {
            petta_atom_free(sys->procs[p].spawn_args[a]);
            sys->procs[p].spawn_args[a] = NULL;
        }
    }
}

static PettaAtom *gold_er_eval_expr(
    GoldErlangSystem *sys,
    const GoldErModule *mod,
    uint32_t self_pid,
    const char **pp,
    PettaEnv *env,
    bool *out_blocked);

static PettaAtom *gold_er_call_fn(
    GoldErlangSystem *sys,
    const GoldErModule *mod,
    uint32_t self_pid,
    const char *fname,
    uint32_t argc,
    PettaAtom **args,
    bool *out_blocked);

static inline void gold_er_step_actors(GoldErlangSystem *sys, const GoldErModule *mod) {
    bool progress = true;
    uint32_t guard = 0;
    while (progress && guard++ < 64u) {
        progress = false;
        for (uint32_t i = 0; i < sys->nprocs; i++) {
            GoldErProcess *proc = &sys->procs[i];
            if (!proc->active || !proc->is_actor || gold_er_alive_mbox_count(proc) == 0) continue;
            uint32_t before_rec = (uint32_t)sys->receives_admitted;
            bool blocked = false;
            PettaAtom *res = gold_er_call_fn(sys, mod, proc->pid, proc->spawn_fn, proc->spawn_argc, proc->spawn_args, &blocked);
            petta_atom_free(res);
            if (sys->receives_admitted > before_rec) progress = true;
        }
    }
}

static inline PettaAtom *gold_er_eval_seq(
    GoldErlangSystem *sys,
    const GoldErModule *mod,
    uint32_t self_pid,
    const char *seq_str,
    PettaEnv *env,
    bool *out_blocked)
{
    const char *p = gold_er_skip_ws(seq_str);
    PettaAtom *last = NULL;
    while (*p && !*out_blocked) {
        petta_atom_free(last);
        last = gold_er_eval_expr(sys, mod, self_pid, &p, env, out_blocked);
        p = gold_er_skip_ws(p);
        if (*p == ',') p = gold_er_skip_ws(p + 1);
        else break;
    }
    return last;
}

static inline PettaAtom *gold_er_eval_primary(
    GoldErlangSystem *sys,
    const GoldErModule *mod,
    uint32_t self_pid,
    const char **pp,
    PettaEnv *env,
    bool *out_blocked)
{
    const char *p = gold_er_skip_ws(*pp);
    if (!*p) return petta_atom_sym("ok");

    /* 1. `receive ... end` */
    if (strncmp(p, "receive", 7) == 0 && !isalnum((unsigned char)p[7]) && p[7] != '_') {
        p = gold_er_skip_ws(p + 7);
        const char *clauses_start = p;
        /* Advance `p` past matching `end` */
        int rdepth = 1;
        while (*p && rdepth > 0) {
            if ((strncmp(p, "receive", 7) == 0 && !isalnum((unsigned char)p[7]) && p[7] != '_') ||
                (strncmp(p, "fun", 3) == 0 && !isalnum((unsigned char)p[3]) && p[3] != '_')) {
                rdepth++;
                p += 3;
                continue;
            }
            if (strncmp(p, "end", 3) == 0 && !isalnum((unsigned char)p[3]) && p[3] != '_' &&
                !isalnum((unsigned char)p[-1]) && p[-1] != '_') {
                rdepth--;
                if (rdepth == 0) {
                    size_t clen = (size_t)(p - clauses_start);
                    p += 3;
                    *pp = p;
                    char cbuf[512] = {0};
                    if (clen >= sizeof(cbuf)) clen = sizeof(cbuf) - 1u;
                    memcpy(cbuf, clauses_start, clen);

                    GoldErProcess *proc = gold_er_find_proc(sys, self_pid);
                    if (!proc) return petta_atom_sym("error");
                    if (!proc->is_actor) {
                        gold_er_step_actors(sys, mod);
                    }

                    for (uint32_t m = 0; m < proc->mbox_count; m++) {
                        GoldErMailboxEntry *me = &proc->mbox[m];
                        if (!me->alive || !me->msg.term_payload) continue;
                        /* Try each receive clause against `me->msg.term_payload` */
                        const char *cp = cbuf;
                        while (*cp) {
                            cp = gold_er_skip_ws(cp);
                            if (!*cp) break;
                            PettaAtom *rpat = gold_er_parse_term(&cp);
                            cp = gold_er_skip_ws(cp);
                            char rguard[64] = {0};
                            if (strncmp(cp, "when", 4) == 0 && (cp[4] == ' ' || cp[4] == '\t')) {
                                cp = gold_er_skip_ws(cp + 4);
                                const char *arr = strstr(cp, "->");
                                if (arr) {
                                    size_t gl = (size_t)(arr - cp);
                                    while (gl > 0 && (cp[gl - 1] == ' ' || cp[gl - 1] == '\t')) gl--;
                                    if (gl >= sizeof(rguard)) gl = sizeof(rguard) - 1u;
                                    memcpy(rguard, cp, gl);
                                    cp = arr;
                                }
                            }
                            if (strncmp(cp, "->", 2) == 0) cp += 2;
                            cp = gold_er_skip_ws(cp);
                            char rbody[256] = {0};
                            size_t bl = 0;
                            int bdepth = 0;
                            while (*cp && !(bdepth == 0 && *cp == ';')) {
                                if (*cp == '(' || *cp == '[' || *cp == '{') bdepth++;
                                else if ((*cp == ')' || *cp == ']' || *cp == '}') && bdepth > 0) bdepth--;
                                if (bl + 1 < sizeof(rbody)) rbody[bl++] = *cp;
                                cp++;
                            }
                            if (*cp == ';') cp++;

                            PettaEnv cand_env;
                            petta_env_init(&cand_env);
                            bool matched = gold_er_match_pat(rpat, me->msg.term_payload, env, &cand_env) &&
                                           gold_er_eval_guard(rguard, &cand_env);
                            petta_atom_free(rpat);
                            if (matched) {
                                /* Admit linear receive step on tcalc! */
                                Occ take_occs[1] = { me->tc_occ };
                                Term inst[TC_VARS];
                                memset(inst, 0, sizeof(inst));
                                inst[0] = me->tc_term;
                                TcPreparedStep cand;
                                memset(&cand, 0, sizeof(cand));
                                cand.rule = sys->rule_er_receive;
                                cand.take = take_occs;
                                cand.inst = inst;
                                TcPreparedEffect eff;
                                TcAdmissionReceipt rec;
                                TcRefusalReason ref = TC_REFUSE_NONE;
                                if (tc_bridge_execute_candidate(&cand, &sys->profile_linear, &eff, &sys->last_event, &rec, &ref) == TC_BRIDGE_ADMITTED) {
                                    sys->last_receipt = rec;
                                    sys->receives_admitted++;
                                }
                                me->alive = false;
                                for (uint32_t bi = 0; bi < cand_env.nbinds; bi++) {
                                    petta_env_bind(env, cand_env.binds[bi].var, cand_env.binds[bi].val);
                                }
                                petta_env_free(&cand_env);
                                return gold_er_eval_seq(sys, mod, self_pid, rbody, env, out_blocked);
                            }
                            petta_env_free(&cand_env);
                        }
                    }
                    *out_blocked = true;
                    return petta_atom_sym("blocked");
                }
            }
            p++;
        }
    }

    /* 2. Tuple `{e1, e2, ...}` */
    if (*p == '{') {
        p++;
        PettaAtom *items[8];
        uint32_t n = 0;
        p = gold_er_skip_ws(p);
        while (*p && *p != '}' && n < 8u) {
            items[n++] = gold_er_eval_expr(sys, mod, self_pid, &p, env, out_blocked);
            p = gold_er_skip_ws(p);
            if (*p == ',') p = gold_er_skip_ws(p + 1);
        }
        if (*p == '}') p++;
        *pp = p;
        return gold_er_make_tag("{}", n, items);
    }

    /* 3. List `[]`, `[e1, e2]`, `[e1, e2 | tail]` */
    if (*p == '[') {
        p++;
        p = gold_er_skip_ws(p);
        if (*p == ']') {
            p++;
            *pp = p;
            return petta_atom_sym("[]");
        }
        PettaAtom *elems[16];
        uint32_t ne = 0;
        PettaAtom *tail = NULL;
        while (*p && *p != ']' && ne < 16u) {
            elems[ne++] = gold_er_eval_expr(sys, mod, self_pid, &p, env, out_blocked);
            p = gold_er_skip_ws(p);
            if (*p == ',') {
                p = gold_er_skip_ws(p + 1);
            } else if (*p == '|') {
                p = gold_er_skip_ws(p + 1);
                tail = gold_er_eval_expr(sys, mod, self_pid, &p, env, out_blocked);
                p = gold_er_skip_ws(p);
                break;
            }
        }
        if (*p == ']') p++;
        *pp = p;
        if (!tail) tail = petta_atom_sym("[]");
        for (int32_t i = (int32_t)ne - 1; i >= 0; i--) {
            PettaAtom *cargs[2] = { elems[i], tail };
            tail = gold_er_make_tag("|", 2, cargs);
        }
        return tail;
    }

    /* 4. Integer literal */
    if ((*p == '-' && isdigit((unsigned char)p[1])) || isdigit((unsigned char)*p)) {
        int64_t v = strtoll(p, (char **)&p, 10);
        *pp = p;
        return petta_atom_int(v);
    }

    /* 5. Identifier / Variable / Function call / `self()` / `spawn(fun() -> f(...) end)` */
    char id[64] = {0};
    size_t il = 0;
    while (*p && (isalnum((unsigned char)*p) || *p == '_')) {
        if (il + 1 < sizeof(id)) id[il++] = *p;
        p++;
    }
    p = gold_er_skip_ws(p);
    if (isupper((unsigned char)id[0]) || id[0] == '_') {
        *pp = p;
        const PettaAtom *bound = petta_env_lookup(env, id);
        return bound ? petta_atom_clone(bound) : petta_atom_var(id);
    }
    if (strcmp(id, "self") == 0 && *p == '(') {
        while (*p && *p != ')') p++;
        if (*p == ')') p++;
        *pp = p;
        PettaAtom *pa = petta_atom_int((int64_t)self_pid);
        return gold_er_make_tag("Pid", 1, &pa);
    }
    if (strcmp(id, "spawn") == 0 && *p == '(') {
        p = gold_er_skip_ws(p + 1);
        if (strncmp(p, "fun", 3) == 0) {
            const char *arrow = strstr(p, "->");
            if (arrow) p = gold_er_skip_ws(arrow + 2);
        }
        char sfn[32] = {0};
        size_t sl = 0;
        while (*p && (isalnum((unsigned char)*p) || *p == '_')) {
            if (sl + 1 < sizeof(sfn)) sfn[sl++] = *p;
            p++;
        }
        p = gold_er_skip_ws(p);
        PettaAtom *sargs[4] = {0};
        uint32_t sargc = 0;
        if (*p == '(') {
            p++;
            p = gold_er_skip_ws(p);
            while (*p && *p != ')' && sargc < 4u) {
                sargs[sargc++] = gold_er_eval_expr(sys, mod, self_pid, &p, env, out_blocked);
                p = gold_er_skip_ws(p);
                if (*p == ',') p = gold_er_skip_ws(p + 1);
            }
            if (*p == ')') p++;
        }
        p = gold_er_skip_ws(p);
        if (strncmp(p, "end", 3) == 0) p = gold_er_skip_ws(p + 3);
        if (*p == ')') p++;
        *pp = p;

        uint32_t new_pid = gold_er_spawn(sys, sfn);
        GoldErProcess *np = gold_er_find_proc(sys, new_pid);
        if (np) {
            np->is_actor = true;
            snprintf(np->spawn_fn, sizeof(np->spawn_fn), "%s", sfn);
            np->spawn_argc = sargc;
            for (uint32_t k = 0; k < sargc; k++) np->spawn_args[k] = sargs[k];
        } else {
            for (uint32_t k = 0; k < sargc; k++) petta_atom_free(sargs[k]);
        }
        PettaAtom *pa = petta_atom_int((int64_t)new_pid);
        return gold_er_make_tag("Pid", 1, &pa);
    }
    if (*p == '(') {
        p++;
        p = gold_er_skip_ws(p);
        PettaAtom *fargs[6] = {0};
        uint32_t fargc = 0;
        while (*p && *p != ')' && fargc < 6u) {
            fargs[fargc++] = gold_er_eval_expr(sys, mod, self_pid, &p, env, out_blocked);
            p = gold_er_skip_ws(p);
            if (*p == ',') p = gold_er_skip_ws(p + 1);
        }
        if (*p == ')') p++;
        *pp = p;
        /* Tail-call inside an actor process updates its actor arguments and yields if mailbox is empty */
        GoldErProcess *sproc = gold_er_find_proc(sys, self_pid);
        if (sproc && sproc->is_actor && strcmp(id, sproc->spawn_fn) == 0) {
            for (uint32_t k = 0; k < sproc->spawn_argc; k++) petta_atom_free(sproc->spawn_args[k]);
            sproc->spawn_argc = fargc;
            for (uint32_t k = 0; k < fargc; k++) sproc->spawn_args[k] = fargs[k];
            return petta_atom_sym("actor_continue");
        }
        PettaAtom *ret = gold_er_call_fn(sys, mod, self_pid, id, fargc, fargs, out_blocked);
        for (uint32_t k = 0; k < fargc; k++) petta_atom_free(fargs[k]);
        return ret;
    }
    *pp = p;
    return petta_atom_sym(id);
}

static inline PettaAtom *gold_er_eval_arith(
    GoldErlangSystem *sys,
    const GoldErModule *mod,
    uint32_t self_pid,
    const char **pp,
    PettaEnv *env,
    bool *out_blocked)
{
    PettaAtom *lhs = gold_er_eval_primary(sys, mod, self_pid, pp, env, out_blocked);
    const char *p = gold_er_skip_ws(*pp);
    while (*p == '+' || *p == '-' || *p == '*') {
        if (*p == '-' && p[1] == '>') break;
        char op = *p++;
        *pp = p;
        PettaAtom *rhs = gold_er_eval_primary(sys, mod, self_pid, pp, env, out_blocked);
        if (lhs->kind == PETTA_ATOM_INT && rhs->kind == PETTA_ATOM_INT) {
            int64_t lv = lhs->ival, rv = rhs->ival;
            int64_t res = (op == '+') ? (lv + rv) : (op == '-') ? (lv - rv) : (lv * rv);
            petta_atom_free(lhs);
            petta_atom_free(rhs);
            lhs = petta_atom_int(res);
        } else {
            petta_atom_free(rhs);
        }
        p = gold_er_skip_ws(*pp);
    }
    return lhs;
}

static inline PettaAtom *gold_er_eval_expr(
    GoldErlangSystem *sys,
    const GoldErModule *mod,
    uint32_t self_pid,
    const char **pp,
    PettaEnv *env,
    bool *out_blocked)
{
    const char *p = gold_er_skip_ws(*pp);
    /* Check for `Var = Expr` assignment */
    if (isupper((unsigned char)*p)) {
        const char *scan = p;
        char vname[64] = {0};
        size_t vl = 0;
        while (*scan && (isalnum((unsigned char)*scan) || *scan == '_')) {
            if (vl + 1 < sizeof(vname)) vname[vl++] = *scan;
            scan++;
        }
        scan = gold_er_skip_ws(scan);
        if (*scan == '=' && scan[1] != '=' && scan[1] != '<') {
            *pp = gold_er_skip_ws(scan + 1);
            PettaAtom *rhs = gold_er_eval_expr(sys, mod, self_pid, pp, env, out_blocked);
            petta_env_bind(env, vname, rhs);
            return rhs;
        }
    }
    PettaAtom *lhs = gold_er_eval_arith(sys, mod, self_pid, pp, env, out_blocked);
    p = gold_er_skip_ws(*pp);
    if (*p == '!') {
        *pp = gold_er_skip_ws(p + 1);
        PettaAtom *msg = gold_er_eval_arith(sys, mod, self_pid, pp, env, out_blocked);
        uint32_t dest_pid = 0;
        if (lhs->kind == PETTA_ATOM_EXPR && lhs->arity == 2 &&
            lhs->args[0]->kind == PETTA_ATOM_SYM && strcmp(lhs->args[0]->text, "Pid") == 0 &&
            lhs->args[1]->kind == PETTA_ATOM_INT) {
            dest_pid = (uint32_t)lhs->args[1]->ival;
        } else if (lhs->kind == PETTA_ATOM_INT) {
            dest_pid = (uint32_t)lhs->ival;
        }
        if (dest_pid > 0) {
            const char *tag = (msg->kind == PETTA_ATOM_SYM) ? msg->text : "tuple";
            int64_t pay = (msg->kind == PETTA_ATOM_INT) ? msg->ival : 0;
            if (msg->kind == PETTA_ATOM_EXPR && msg->arity >= 2 &&
                msg->args[0]->kind == PETTA_ATOM_SYM && strcmp(msg->args[0]->text, "{}") == 0 &&
                msg->args[1]->kind == PETTA_ATOM_SYM) {
                tag = msg->args[1]->text;
                if (msg->arity >= 3 && msg->args[msg->arity - 1]->kind == PETTA_ATOM_INT)
                    pay = msg->args[msg->arity - 1]->ival;
            }
            if (gold_er_send(sys, self_pid, dest_pid, tag, 1, pay)) {
                sys->network[sys->nenvelopes - 1u].msg.term_payload = petta_atom_clone(msg);
                gold_er_deliver_fifo(sys, self_pid, dest_pid);
            }
        }
        petta_atom_free(lhs);
        return msg;
    }
    return lhs;
}

static inline PettaAtom *gold_er_call_fn(
    GoldErlangSystem *sys,
    const GoldErModule *mod,
    uint32_t self_pid,
    const char *fname,
    uint32_t argc,
    PettaAtom **args,
    bool *out_blocked)
{
    for (uint32_t c = 0; c < mod->nclauses; c++) {
        const GoldErClause *cl = &mod->clauses[c];
        if (cl->arity != argc || strcmp(cl->fname, fname) != 0) continue;
        PettaEnv cenv;
        petta_env_init(&cenv);
        bool ok = true;
        for (uint32_t i = 0; i < argc; i++) {
            if (!gold_er_match_pat(cl->params[i], args[i], NULL, &cenv)) {
                ok = false;
                break;
            }
        }
        if (ok && !gold_er_eval_guard(cl->guard_str, &cenv)) ok = false;
        if (ok) {
            PettaAtom *res = gold_er_eval_seq(sys, mod, self_pid, cl->body_str, &cenv, out_blocked);
            petta_env_free(&cenv);
            return res;
        }
        petta_env_free(&cenv);
    }
    return petta_atom_sym("no_clause");
}

static inline bool gold_er_eval_call_str(
    GoldErlangSystem *sys,
    const GoldErModule *mod,
    uint32_t caller_pid,
    const char *call_expr,
    char *out_buf,
    size_t out_cap)
{
    if (caller_pid == 0) caller_pid = gold_er_spawn(sys, "caller");
    PettaEnv env;
    petta_env_init(&env);
    bool blocked = false;
    PettaAtom *res = gold_er_eval_seq(sys, mod, caller_pid, call_expr, &env, &blocked);
    gold_er_format_atom(res, out_buf, out_cap);
    petta_atom_free(res);
    petta_env_free(&env);
    return !blocked;
}

/* =========================================================================
 * PART 3: OCaml O0 + O1 — Hindley-Milner Rank-1 Let-Polymorphism,
 *         Type-Directed Constructor Disambiguation, Refusals & Evaluator
 * ========================================================================= */

typedef enum {
    OCAML_TY_VAR     = 0,
    OCAML_TY_INT     = 1,
    OCAML_TY_STRING  = 2,
    OCAML_TY_BOOL    = 3,
    OCAML_TY_ARROW   = 4,
    OCAML_TY_PAIR    = 5,
    OCAML_TY_LIST    = 6,
    OCAML_TY_REF     = 7,
    OCAML_TY_VARIANT = 8
} GoldMlTypeKind;

typedef enum {
    OCAML_OK                      = 0,
    OCAML_REFUSE_TYPE_MISMATCH    = 1,
    OCAML_REFUSE_OCCURS_CHECK     = 2,
    OCAML_REFUSE_MONO_PARAM       = 3,
    OCAML_REFUSE_VALUE_RESTRICTION = 4,
    OCAML_REFUSE_AMBIGUOUS_CTOR   = 5
} GoldMlRefusalKind;

typedef struct GoldMlType {
    GoldMlTypeKind kind;
    uint32_t var_id;
    char variant_name[32];
    struct GoldMlType *left;
    struct GoldMlType *right;
} GoldMlType;

typedef struct {
    uint32_t nquant;
    uint32_t cap_quant;
    uint32_t *quant_vars;
    GoldMlType *body;
} GoldMlScheme;

typedef struct {
    uint32_t next_tvar;
    uint32_t ntypes;
    uint32_t cap_types;
    GoldMlType **pool;
    uint32_t cap_subst;
    GoldMlType **subst;
    GoldMlRefusalKind refusal;
} GoldMlTypeEnv;

static inline void gold_ml_type_env_init(GoldMlTypeEnv *tenv) {
    memset(tenv, 0, sizeof(*tenv));
    tenv->next_tvar = 1u;
    tenv->cap_types = 256u;
    tenv->pool = (GoldMlType **)calloc(tenv->cap_types, sizeof(GoldMlType *));
    tenv->cap_subst = 128u;
    tenv->subst = (GoldMlType **)calloc(tenv->cap_subst, sizeof(GoldMlType *));
}

static inline void gold_ml_type_env_destroy(GoldMlTypeEnv *tenv) {
    if (!tenv) return;
    for (uint32_t i = 0; i < tenv->ntypes; i++) {
        free(tenv->pool[i]);
    }
    free(tenv->pool);
    free(tenv->subst);
    memset(tenv, 0, sizeof(*tenv));
}

static inline void gold_ml_scheme_destroy(GoldMlScheme *sch) {
    if (!sch) return;
    free(sch->quant_vars);
    sch->quant_vars = NULL;
    sch->nquant = 0;
    sch->cap_quant = 0;
}

static inline GoldMlType *gold_ml_alloc_type(GoldMlTypeEnv *tenv, GoldMlTypeKind kind) {
    if (tenv->ntypes >= tenv->cap_types) {
        uint32_t ncap = tenv->cap_types ? tenv->cap_types * 2u : 256u;
        GoldMlType **np = (GoldMlType **)realloc(tenv->pool, (size_t)ncap * sizeof(GoldMlType *));
        if (!np) return NULL;
        tenv->pool = np;
        tenv->cap_types = ncap;
    }
    GoldMlType *t = (GoldMlType *)calloc(1, sizeof(GoldMlType));
    if (!t) return NULL;
    t->kind = kind;
    tenv->pool[tenv->ntypes++] = t;
    return t;
}

static inline GoldMlType *gold_ml_tvar(GoldMlTypeEnv *tenv) {
    GoldMlType *t = gold_ml_alloc_type(tenv, OCAML_TY_VAR);
    uint32_t id = tenv->next_tvar++;
    if (id >= tenv->cap_subst) {
        uint32_t ncap = tenv->cap_subst ? tenv->cap_subst * 2u : 128u;
        while (ncap <= id) ncap *= 2u;
        GoldMlType **ns = (GoldMlType **)realloc(tenv->subst, (size_t)ncap * sizeof(GoldMlType *));
        if (ns) {
            memset(ns + tenv->cap_subst, 0, (size_t)(ncap - tenv->cap_subst) * sizeof(GoldMlType *));
            tenv->subst = ns;
            tenv->cap_subst = ncap;
        }
    }
    t->var_id = id;
    return t;
}

static inline GoldMlType *gold_ml_tarrow(GoldMlTypeEnv *tenv, GoldMlType *dom, GoldMlType *cod) {
    GoldMlType *t = gold_ml_alloc_type(tenv, OCAML_TY_ARROW);
    t->left = dom;
    t->right = cod;
    return t;
}

static inline GoldMlType *gold_ml_tpair(GoldMlTypeEnv *tenv, GoldMlType *fst, GoldMlType *snd) {
    GoldMlType *t = gold_ml_alloc_type(tenv, OCAML_TY_PAIR);
    t->left = fst;
    t->right = snd;
    return t;
}

static inline GoldMlType *gold_ml_tref(GoldMlTypeEnv *tenv, GoldMlType *elem) {
    GoldMlType *t = gold_ml_alloc_type(tenv, OCAML_TY_REF);
    t->left = elem;
    return t;
}

static inline GoldMlType *gold_ml_tvariant(GoldMlTypeEnv *tenv, const char *vname) {
    GoldMlType *t = gold_ml_alloc_type(tenv, OCAML_TY_VARIANT);
    snprintf(t->variant_name, sizeof(t->variant_name), "%s", vname);
    return t;
}

static inline GoldMlType *gold_ml_prune(GoldMlTypeEnv *tenv, GoldMlType *t) {
    if (!t) return NULL;
    while (t->kind == OCAML_TY_VAR && t->var_id < tenv->cap_subst && tenv->subst[t->var_id] != NULL) {
        t = tenv->subst[t->var_id];
    }
    return t;
}

static inline bool gold_ml_occurs_in(GoldMlTypeEnv *tenv, uint32_t var_id, GoldMlType *t) {
    t = gold_ml_prune(tenv, t);
    if (!t) return false;
    if (t->kind == OCAML_TY_VAR) return t->var_id == var_id;
    return gold_ml_occurs_in(tenv, var_id, t->left) ||
           gold_ml_occurs_in(tenv, var_id, t->right);
}

static inline bool gold_ml_unify(GoldMlTypeEnv *tenv, GoldMlType *a, GoldMlType *b) {
    a = gold_ml_prune(tenv, a);
    b = gold_ml_prune(tenv, b);
    if (!a || !b) return false;
    if (a->kind == OCAML_TY_VAR) {
        if (b->kind == OCAML_TY_VAR && a->var_id == b->var_id) return true;
        if (gold_ml_occurs_in(tenv, a->var_id, b)) {
            tenv->refusal = OCAML_REFUSE_OCCURS_CHECK;
            return false;
        }
        tenv->subst[a->var_id] = b;
        return true;
    }
    if (b->kind == OCAML_TY_VAR) {
        return gold_ml_unify(tenv, b, a);
    }
    if (a->kind != b->kind) {
        tenv->refusal = OCAML_REFUSE_TYPE_MISMATCH;
        return false;
    }
    if (a->kind == OCAML_TY_VARIANT && strcmp(a->variant_name, b->variant_name) != 0) {
        tenv->refusal = OCAML_REFUSE_TYPE_MISMATCH;
        return false;
    }
    if (a->left || b->left) {
        if (!gold_ml_unify(tenv, a->left, b->left)) return false;
    }
    if (a->right || b->right) {
        if (!gold_ml_unify(tenv, a->right, b->right)) return false;
    }
    return true;
}

static inline void gold_ml_scheme_push_qvar(GoldMlScheme *sch, uint32_t var_id) {
    if (!sch->quant_vars) {
        sch->cap_quant = 16u;
        sch->quant_vars = (uint32_t *)calloc(sch->cap_quant, sizeof(uint32_t));
    }
    for (uint32_t i = 0; i < sch->nquant; i++) {
        if (sch->quant_vars[i] == var_id) return;
    }
    if (sch->nquant >= sch->cap_quant) {
        uint32_t ncap = sch->cap_quant * 2u;
        uint32_t *nv = (uint32_t *)realloc(sch->quant_vars, (size_t)ncap * sizeof(uint32_t));
        if (!nv) return;
        sch->quant_vars = nv;
        sch->cap_quant = ncap;
    }
    sch->quant_vars[sch->nquant++] = var_id;
}

static inline void gold_ml_collect_tvars(GoldMlTypeEnv *tenv, GoldMlType *t, GoldMlScheme *sch) {
    t = gold_ml_prune(tenv, t);
    if (!t) return;
    if (t->kind == OCAML_TY_VAR) {
        gold_ml_scheme_push_qvar(sch, t->var_id);
        return;
    }
    if (t->left) gold_ml_collect_tvars(tenv, t->left, sch);
    if (t->right) gold_ml_collect_tvars(tenv, t->right, sch);
}

/* Generalize `t` into a rank-1 scheme ONLY if `is_syntactic_value` holds (Value Restriction!) */
static inline GoldMlScheme gold_ml_generalize(GoldMlTypeEnv *tenv, GoldMlType *t, bool is_syntactic_value) {
    GoldMlScheme sch;
    memset(&sch, 0, sizeof(sch));
    t = gold_ml_prune(tenv, t);
    sch.body = t;
    if (!is_syntactic_value) {
        /* Value restriction: expansive expressions (such as `ref None`) remain monomorphic! */
        return sch;
    }
    gold_ml_collect_tvars(tenv, t, &sch);
    return sch;
}

static inline GoldMlType *gold_ml_clone_subst_var(
    GoldMlTypeEnv *tenv,
    GoldMlType *t,
    const uint32_t *qvars,
    GoldMlType **fresh_vars,
    uint32_t nquant)
{
    t = gold_ml_prune(tenv, t);
    if (!t) return NULL;
    if (t->kind == OCAML_TY_VAR) {
        for (uint32_t i = 0; i < nquant; i++) {
            if (qvars[i] == t->var_id) return fresh_vars[i];
        }
        return t;
    }
    if (!t->left && !t->right) return t;
    GoldMlType *c = gold_ml_alloc_type(tenv, t->kind);
    memcpy(c->variant_name, t->variant_name, sizeof(c->variant_name));
    if (t->left) c->left = gold_ml_clone_subst_var(tenv, t->left, qvars, fresh_vars, nquant);
    if (t->right) c->right = gold_ml_clone_subst_var(tenv, t->right, qvars, fresh_vars, nquant);
    return c;
}

static inline GoldMlType *gold_ml_instantiate(GoldMlTypeEnv *tenv, const GoldMlScheme *sch) {
    if (sch->nquant == 0 || !sch->quant_vars) return gold_ml_prune(tenv, sch->body);
    GoldMlType *fbuf[16];
    GoldMlType **fresh_vars = (sch->nquant <= 16u)
        ? fbuf
        : (GoldMlType **)malloc((size_t)sch->nquant * sizeof(GoldMlType *));
    const uint32_t *qvars = sch->quant_vars;
    for (uint32_t i = 0; i < sch->nquant; i++) {
        fresh_vars[i] = gold_ml_tvar(tenv);
    }
    GoldMlType *res = gold_ml_clone_subst_var(tenv, sch->body, qvars, fresh_vars, sch->nquant);
    if (fresh_vars != fbuf) free(fresh_vars);
    return res;
}

/* Type-directed constructor disambiguation across variant declarations sharing a constructor name:
 * e.g. type metric = Score of int | Label of string
 *      type badge  = Score of int | Rank of int
 * Disambiguates `Score 95` when expected type is `Some(badge)` vs `Some(metric)` and refuses
 * if expected type is an unannotated type variable and multiple variants own `Score` without a default! */
typedef struct {
    char ctor_name[32];
    char owner_variant[32];
    GoldMlTypeKind arg_kind;
} GoldMlCtorDecl;

static inline GoldMlType *gold_ml_disambiguate_ctor(
    GoldMlTypeEnv *tenv,
    const GoldMlCtorDecl *decls,
    uint32_t ndecls,
    const char *ctor_name,
    GoldMlType *arg_type,
    GoldMlType *expected_variant_type)
{
    expected_variant_type = gold_ml_prune(tenv, expected_variant_type);
    const GoldMlCtorDecl *matched = NULL;
    uint32_t match_count = 0;
    for (uint32_t i = 0; i < ndecls; i++) {
        if (strcmp(decls[i].ctor_name, ctor_name) != 0) continue;
        if (expected_variant_type && expected_variant_type->kind == OCAML_TY_VARIANT) {
            if (strcmp(decls[i].owner_variant, expected_variant_type->variant_name) != 0)
                continue;
        }
        matched = &decls[i];
        match_count++;
    }
    if (match_count == 0) {
        tenv->refusal = OCAML_REFUSE_TYPE_MISMATCH;
        return NULL;
    }
    if (match_count > 1 && (!expected_variant_type || expected_variant_type->kind != OCAML_TY_VARIANT)) {
        tenv->refusal = OCAML_REFUSE_AMBIGUOUS_CTOR;
        return NULL;
    }
    GoldMlType *expected_arg = gold_ml_alloc_type(tenv, matched->arg_kind);
    if (!gold_ml_unify(tenv, arg_type, expected_arg)) {
        return NULL;
    }
    GoldMlType *res = gold_ml_tvariant(tenv, matched->owner_variant);
    if (expected_variant_type && !gold_ml_unify(tenv, res, expected_variant_type)) {
        return NULL;
    }
    return res;
}

/* Gold OCaml O1 Task Ranking & Tree/List Evaluator over tcalc (`task_ranking.ml`, `tree_list.ml`) */
typedef struct {
    char name[32];
    int64_t base_priority;
    int64_t explanation_bonus;
    bool maude_certified;
    int64_t total_score;
} GoldMlTaskItem;

static inline void gold_ml_rank_tasks(
    GoldMlTaskItem *items,
    uint32_t nitems,
    char *out_summary,
    size_t summary_cap)
{
    for (uint32_t i = 0; i < nitems; i++) {
        items[i].total_score = items[i].base_priority * 10 +
                               items[i].explanation_bonus * 5 +
                               (items[i].maude_certified ? 100 : -1000);
    }
    /* True stable descending insertion sort by total_score (preserving relative order of ties) */
    for (uint32_t i = 1; i < nitems; i++) {
        GoldMlTaskItem key = items[i];
        int32_t j = (int32_t)i - 1;
        while (j >= 0 && items[j].total_score < key.total_score) {
            items[j + 1] = items[j];
            j--;
        }
        items[j + 1] = key;
    }
    size_t pos = 0;
    pos += (size_t)snprintf(out_summary + pos, summary_cap > pos ? summary_cap - pos : 0, "[");
    for (uint32_t i = 0; i < nitems; i++) {
        if (i > 0) pos += (size_t)snprintf(out_summary + pos, summary_cap > pos ? summary_cap - pos : 0, "; ");
        pos += (size_t)snprintf(out_summary + pos, summary_cap > pos ? summary_cap - pos : 0,
                                "(\"%s\", %" PRId64 ")", items[i].name, items[i].total_score);
    }
    snprintf(out_summary + pos, summary_cap > pos ? summary_cap - pos : 0, "]");
}

/* =========================================================================
 * PART 3B: OCaml O1 Source Parser & Evaluator over tcalc
 *          (`task_ranking.ml`, `tree_list.ml`)
 * ========================================================================= */

typedef struct {
    char name[32];
    bool is_rec;
    uint32_t arity;
    char params[4][32];
    char body[512];
} GoldMlFnDecl;

typedef struct {
    uint32_t ntypes;
    char type_decls[8][128];
    uint32_t nfns;
    GoldMlFnDecl fns[16];
    uint64_t eval_steps;
} GoldMlModule;

static inline const char *gold_ml_skip_ws(const char *p) {
    while (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n') p++;
    return p;
}

static inline bool gold_ml_is_kw(const char *s, size_t len, const char *kw) {
    return strlen(kw) == len && strncmp(s, kw, len) == 0;
}

static inline bool gold_ml_at_kw(const char *p, const char *kw) {
    size_t kl = strlen(kw);
    return strncmp(p, kw, kl) == 0 && !isalnum((unsigned char)p[kl]) && p[kl] != '_' && p[kl] != '\'';
}

/* Parse an OCaml pattern (`_, []`, `Task (_, score, _), (Task (_, next_score, _) as next) :: rest`,
 * `Node (left, value, right)`, `Empty`, etc.) into a PettaAtom */
static PettaAtom *gold_ml_parse_pat_tuple(const char **pp);

static inline PettaAtom *gold_ml_parse_pat_prim(const char **pp) {
    const char *p = gold_ml_skip_ws(*pp);
    if (!*p) return NULL;
    if (*p == '(') {
        p = gold_ml_skip_ws(p + 1);
        if (*p == ')') {
            *pp = p + 1;
            return petta_atom_sym("()");
        }
        PettaAtom *inner = gold_ml_parse_pat_tuple(&p);
        p = gold_ml_skip_ws(p);
        if (*p == ')') p++;
        *pp = p;
        return inner;
    }
    if (*p == '[') {
        p = gold_ml_skip_ws(p + 1);
        if (*p == ']') {
            *pp = p + 1;
            return petta_atom_sym("[]");
        }
        PettaAtom *elems[8];
        uint32_t ne = 0;
        while (*p && *p != ']' && ne < 8u) {
            elems[ne++] = gold_ml_parse_pat_tuple(&p);
            p = gold_ml_skip_ws(p);
            if (*p == ';') p = gold_ml_skip_ws(p + 1);
        }
        if (*p == ']') p++;
        *pp = p;
        PettaAtom *res = petta_atom_sym("[]");
        for (int32_t i = (int32_t)ne - 1; i >= 0; i--) {
            PettaAtom *cargs[2] = { elems[i], res };
            res = gold_er_make_tag("::", 2, cargs);
        }
        return res;
    }
    if (*p == '"') {
        char sbuf[64] = {0};
        size_t sl = 0;
        sbuf[sl++] = *p++;
        while (*p && *p != '"') {
            if (sl + 2 < sizeof(sbuf)) sbuf[sl++] = *p;
            p++;
        }
        if (*p == '"') sbuf[sl++] = *p++;
        *pp = p;
        return petta_atom_sym(sbuf);
    }
    if ((*p == '-' && isdigit((unsigned char)p[1])) || isdigit((unsigned char)*p)) {
        int64_t v = strtoll(p, (char **)&p, 10);
        *pp = p;
        return petta_atom_int(v);
    }
    char id[64] = {0};
    size_t il = 0;
    while (*p && (isalnum((unsigned char)*p) || *p == '_')) {
        if (il + 1 < sizeof(id)) id[il++] = *p;
        p++;
    }
    if (il == 0) return NULL;
    p = gold_ml_skip_ws(p);
    if (strcmp(id, "_") == 0) {
        *pp = p;
        return petta_atom_sym("_");
    }
    if (strcmp(id, "true") == 0 || strcmp(id, "false") == 0) {
        *pp = p;
        return petta_atom_sym(id);
    }
    if (isupper((unsigned char)id[0])) {
        /* Capitalized constructor pattern `Empty` or `Task (...)` or `Node (...)` */
        if (*p == '(' || isalnum((unsigned char)*p) || *p == '_') {
            if (!gold_ml_at_kw(p, "as") && !gold_ml_at_kw(p, "with")) {
                *pp = p;
                PettaAtom *arg = gold_ml_parse_pat_prim(pp);
                PettaAtom *cargs[2] = { petta_atom_sym(id), arg };
                return gold_er_make_tag("Ctor", 2, cargs);
            }
        }
        *pp = p;
        PettaAtom *cname = petta_atom_sym(id);
        return gold_er_make_tag("Ctor", 1, &cname);
    }
    *pp = p;
    return petta_atom_var(id);
}

static inline PettaAtom *gold_ml_parse_pat_as(const char **pp) {
    PettaAtom *lhs = gold_ml_parse_pat_prim(pp);
    const char *p = gold_ml_skip_ws(*pp);
    if (gold_ml_at_kw(p, "as")) {
        p = gold_ml_skip_ws(p + 2);
        char alias[32] = {0};
        size_t al = 0;
        while (*p && (isalnum((unsigned char)*p) || *p == '_')) {
            if (al + 1 < sizeof(alias)) alias[al++] = *p;
            p++;
        }
        *pp = p;
        PettaAtom *aargs[2] = { lhs, petta_atom_var(alias) };
        return gold_er_make_tag("As", 2, aargs);
    }
    return lhs;
}

static inline PettaAtom *gold_ml_parse_pat_cons(const char **pp) {
    PettaAtom *lhs = gold_ml_parse_pat_as(pp);
    const char *p = gold_ml_skip_ws(*pp);
    if (p[0] == ':' && p[1] == ':') {
        *pp = gold_ml_skip_ws(p + 2);
        PettaAtom *rhs = gold_ml_parse_pat_cons(pp);
        PettaAtom *cargs[2] = { lhs, rhs };
        return gold_er_make_tag("::", 2, cargs);
    }
    return lhs;
}

static inline PettaAtom *gold_ml_parse_pat_tuple(const char **pp) {
    PettaAtom *items[8];
    items[0] = gold_ml_parse_pat_cons(pp);
    uint32_t n = 1u;
    const char *p = gold_ml_skip_ws(*pp);
    while (*p == ',' && n < 8u) {
        *pp = gold_ml_skip_ws(p + 1);
        items[n++] = gold_ml_parse_pat_cons(pp);
        p = gold_ml_skip_ws(*pp);
    }
    if (n == 1u) return items[0];
    return gold_er_make_tag(",", n, items);
}

static inline bool gold_ml_match_pat(const PettaAtom *pat, const PettaAtom *val, PettaEnv *env) {
    if (!pat || !val) return false;
    if (pat->kind == PETTA_ATOM_SYM && strcmp(pat->text, "_") == 0) return true;
    if (pat->kind == PETTA_ATOM_VAR) {
        petta_env_bind(env, pat->text, val);
        return true;
    }
    if (pat->kind == PETTA_ATOM_EXPR && pat->arity == 3 &&
        pat->args[0]->kind == PETTA_ATOM_SYM && strcmp(pat->args[0]->text, "As") == 0 &&
        pat->args[2]->kind == PETTA_ATOM_VAR) {
        if (!gold_ml_match_pat(pat->args[1], val, env)) return false;
        petta_env_bind(env, pat->args[2]->text, val);
        return true;
    }
    if (pat->kind != val->kind) return false;
    if (pat->kind == PETTA_ATOM_INT) return pat->ival == val->ival;
    if (pat->kind == PETTA_ATOM_SYM) return strcmp(pat->text, val->text) == 0;
    if (pat->kind == PETTA_ATOM_EXPR) {
        if (pat->arity != val->arity) return false;
        for (uint32_t i = 0; i < pat->arity; i++) {
            if (!gold_ml_match_pat(pat->args[i], val->args[i], env)) return false;
        }
        return true;
    }
    return false;
}

static inline void gold_ml_format_atom(const PettaAtom *a, char *buf, size_t cap) {
    if (!a || cap == 0) return;
    if (a->kind == PETTA_ATOM_INT) {
        snprintf(buf, cap, "%" PRId64, a->ival);
        return;
    }
    if (a->kind == PETTA_ATOM_SYM || a->kind == PETTA_ATOM_VAR) {
        snprintf(buf, cap, "%s", a->text);
        return;
    }
    if (a->kind == PETTA_ATOM_EXPR && a->arity >= 1 && a->args[0]->kind == PETTA_ATOM_SYM) {
        const char *tag = a->args[0]->text;
        if (strcmp(tag, "::") == 0 && a->arity == 3) {
            size_t pos = (size_t)snprintf(buf, cap, "[");
            const PettaAtom *cur = a;
            bool first = true;
            while (cur && cur->kind == PETTA_ATOM_EXPR && cur->arity == 3 &&
                   cur->args[0]->kind == PETTA_ATOM_SYM && strcmp(cur->args[0]->text, "::") == 0) {
                if (!first) pos += (size_t)snprintf(buf + pos, cap > pos ? cap - pos : 0, "; ");
                first = false;
                char sub[128] = {0};
                gold_ml_format_atom(cur->args[1], sub, sizeof(sub));
                pos += (size_t)snprintf(buf + pos, cap > pos ? cap - pos : 0, "%s", sub);
                cur = cur->args[2];
            }
            snprintf(buf + pos, cap > pos ? cap - pos : 0, "]");
            return;
        }
        if (strcmp(tag, ",") == 0) {
            size_t pos = (size_t)snprintf(buf, cap, "(");
            for (uint32_t i = 1; i < a->arity; i++) {
                if (i > 1) pos += (size_t)snprintf(buf + pos, cap > pos ? cap - pos : 0, ", ");
                char sub[128] = {0};
                gold_ml_format_atom(a->args[i], sub, sizeof(sub));
                pos += (size_t)snprintf(buf + pos, cap > pos ? cap - pos : 0, "%s", sub);
            }
            snprintf(buf + pos, cap > pos ? cap - pos : 0, ")");
            return;
        }
        if (strcmp(tag, "Ctor") == 0 && a->arity >= 2 && a->args[1]->kind == PETTA_ATOM_SYM) {
            if (a->arity == 2) {
                snprintf(buf, cap, "%s", a->args[1]->text);
            } else {
                char sub[128] = {0};
                gold_ml_format_atom(a->args[2], sub, sizeof(sub));
                snprintf(buf, cap, "%s %s", a->args[1]->text, sub);
            }
            return;
        }
    }
    petta_atom_render(a, buf, cap);
}

static inline bool gold_ml_parse_source(GoldMlModule *mod, GoldMlTypeEnv *tenv, const char *src) {
    memset(mod, 0, sizeof(*mod));
    const char *p = src;
    while (*p) {
        p = gold_ml_skip_ws(p);
        if (!*p) break;
        if (gold_ml_at_kw(p, "type")) {
            const char *line_end = strchr(p, '\n');
            size_t tl = line_end ? (size_t)(line_end - p) : strlen(p);
            if (mod->ntypes < 8u) {
                if (tl >= sizeof(mod->type_decls[0])) tl = sizeof(mod->type_decls[0]) - 1u;
                memcpy(mod->type_decls[mod->ntypes++], p, tl);
            }
            p = line_end ? (line_end + 1) : (p + tl);
            continue;
        }
        if (gold_ml_at_kw(p, "let")) {
            p = gold_ml_skip_ws(p + 3);
            bool is_rec = false;
            if (gold_ml_at_kw(p, "rec")) {
                is_rec = true;
                p = gold_ml_skip_ws(p + 3);
            }
            if (mod->nfns >= 16u) break;
            GoldMlFnDecl *fn = &mod->fns[mod->nfns];
            memset(fn, 0, sizeof(*fn));
            fn->is_rec = is_rec;
            size_t nl = 0;
            while (*p && (isalnum((unsigned char)*p) || *p == '_')) {
                if (nl + 1 < sizeof(fn->name)) fn->name[nl++] = *p;
                p++;
            }
            p = gold_ml_skip_ws(p);
            while (*p && *p != '=' && fn->arity < 4u) {
                if (*p == '(' && p[1] == ')') {
                    snprintf(fn->params[fn->arity++], 32, "()");
                    p = gold_ml_skip_ws(p + 2);
                } else {
                    size_t pl = 0;
                    while (*p && (isalnum((unsigned char)*p) || *p == '_')) {
                        if (pl + 1 < 32) fn->params[fn->arity][pl++] = *p;
                        p++;
                    }
                    if (pl > 0) fn->arity++;
                    p = gold_ml_skip_ws(p);
                }
            }
            if (*p == '=') p++;
            p = gold_ml_skip_ws(p);
            /* Scan body until the next column-0 `let ` or `type ` or EOF */
            size_t bl = 0;
            while (*p) {
                if (*p == '\n') {
                    const char *next_line = p + 1;
                    if (gold_ml_at_kw(next_line, "let") || gold_ml_at_kw(next_line, "type")) {
                        p = next_line;
                        break;
                    }
                }
                if (bl + 1 < sizeof(fn->body)) fn->body[bl++] = *p;
                p++;
            }
            while (bl > 0 && (fn->body[bl - 1] == ' ' || fn->body[bl - 1] == '\n' || fn->body[bl - 1] == '\r')) {
                fn->body[--bl] = '\0';
            }
            if (tenv) {
                /* Generalize syntactic function declaration in Hindley-Milner GoldMlTypeEnv */
                GoldMlType *fty = gold_ml_tvar(tenv);
                for (uint32_t a = 0; a < fn->arity; a++) {
                    fty = gold_ml_tarrow(tenv, gold_ml_tvar(tenv), fty);
                }
                GoldMlScheme sch = gold_ml_generalize(tenv, fty, true);
                gold_ml_scheme_destroy(&sch);
            }
            mod->nfns++;
            continue;
        }
        p++;
    }
    return mod->nfns > 0;
}

static PettaAtom *gold_ml_eval_expr(GoldMlModule *mod, const char **pp, PettaEnv *env);

static inline PettaAtom *gold_ml_apply_val(GoldMlModule *mod, const PettaAtom *fn_val, PettaAtom *arg) {
    mod->eval_steps++;
    if (fn_val && fn_val->kind == PETTA_ATOM_EXPR && fn_val->arity >= 3 &&
        fn_val->args[0]->kind == PETTA_ATOM_SYM && strcmp(fn_val->args[0]->text, "Closure") == 0) {
        const char *param = fn_val->args[1]->text;
        const char *body_str = fn_val->args[2]->text;
        PettaEnv cenv;
        petta_env_init(&cenv);
        for (uint32_t i = 3; i + 1 < fn_val->arity; i += 2) {
            petta_env_bind(&cenv, fn_val->args[i]->text, fn_val->args[i + 1]);
        }
        if (strcmp(param, "()") != 0) {
            petta_env_bind(&cenv, param, arg);
        }
        const char *bp = body_str;
        PettaAtom *res = gold_ml_eval_expr(mod, &bp, &cenv);
        petta_env_free(&cenv);
        return res;
    }
    return petta_atom_clone(arg);
}

static inline PettaAtom *gold_ml_eval_atom(GoldMlModule *mod, const char **pp, PettaEnv *env, bool allow_comma_in_parens) {
    const char *p = gold_ml_skip_ws(*pp);
    if (!*p) return NULL;
    if (*p == '(') {
        p = gold_ml_skip_ws(p + 1);
        if (*p == ')') {
            *pp = p + 1;
            return petta_atom_sym("()");
        }
        PettaAtom *first = gold_ml_eval_expr(mod, &p, env);
        p = gold_ml_skip_ws(p);
        if (allow_comma_in_parens && *p == ',') {
            PettaAtom *items[8];
            items[0] = first;
            uint32_t n = 1u;
            while (*p == ',' && n < 8u) {
                p = gold_ml_skip_ws(p + 1);
                items[n++] = gold_ml_eval_expr(mod, &p, env);
                p = gold_ml_skip_ws(p);
            }
            if (*p == ')') p++;
            *pp = p;
            return gold_er_make_tag(",", n, items);
        }
        if (*p == ')') p++;
        *pp = p;
        return first;
    }
    if (*p == '[') {
        p = gold_ml_skip_ws(p + 1);
        if (*p == ']') {
            *pp = p + 1;
            return petta_atom_sym("[]");
        }
        PettaAtom *elems[16];
        uint32_t ne = 0;
        while (*p && *p != ']' && ne < 16u) {
            elems[ne++] = gold_ml_eval_expr(mod, &p, env);
            p = gold_ml_skip_ws(p);
            if (*p == ';') p = gold_ml_skip_ws(p + 1);
        }
        if (*p == ']') p++;
        *pp = p;
        PettaAtom *res = petta_atom_sym("[]");
        for (int32_t i = (int32_t)ne - 1; i >= 0; i--) {
            PettaAtom *cargs[2] = { elems[i], res };
            res = gold_er_make_tag("::", 2, cargs);
        }
        return res;
    }
    if (*p == '"') {
        char sbuf[64] = {0};
        size_t sl = 0;
        sbuf[sl++] = *p++;
        while (*p && *p != '"') {
            if (sl + 2 < sizeof(sbuf)) sbuf[sl++] = *p;
            p++;
        }
        if (*p == '"') sbuf[sl++] = *p++;
        *pp = p;
        return petta_atom_sym(sbuf);
    }
    if ((*p == '-' && isdigit((unsigned char)p[1])) || isdigit((unsigned char)*p)) {
        int64_t v = strtoll(p, (char **)&p, 10);
        *pp = p;
        return petta_atom_int(v);
    }
    /* Stop if at reserved keyword */
    if (gold_ml_at_kw(p, "with") || gold_ml_at_kw(p, "then") || gold_ml_at_kw(p, "else") ||
        gold_ml_at_kw(p, "in") || *p == '|' || *p == ')' || *p == ']' || *p == ';' || *p == ',') {
        return NULL;
    }
    char id[64] = {0};
    size_t il = 0;
    while (*p && (isalnum((unsigned char)*p) || *p == '_')) {
        if (il + 1 < sizeof(id)) id[il++] = *p;
        p++;
    }
    if (il == 0) return NULL;
    *pp = p;
    if (strcmp(id, "true") == 0 || strcmp(id, "false") == 0) {
        return petta_atom_sym(id);
    }
    if (isupper((unsigned char)id[0])) {
        PettaAtom *cname = petta_atom_sym(id);
        return gold_er_make_tag("Ctor", 1, &cname);
    }
    const PettaAtom *bound = petta_env_lookup(env, id);
    if (bound) return petta_atom_clone(bound);
    return petta_atom_sym(id);
}

static inline bool gold_ml_can_start_arg(const char *p) {
    p = gold_ml_skip_ws(p);
    if (!*p) return false;
    if (*p == '(' || *p == '[' || *p == '"' || isdigit((unsigned char)*p)) return true;
    if (isalpha((unsigned char)*p) || *p == '_') {
        if (gold_ml_at_kw(p, "with") || gold_ml_at_kw(p, "then") || gold_ml_at_kw(p, "else") ||
            gold_ml_at_kw(p, "in") || gold_ml_at_kw(p, "let") || gold_ml_at_kw(p, "match") ||
            gold_ml_at_kw(p, "if") || gold_ml_at_kw(p, "fun"))
            return false;
        return true;
    }
    return false;
}

static inline PettaAtom *gold_ml_eval_app(GoldMlModule *mod, const char **pp, PettaEnv *env) {
    PettaAtom *head = gold_ml_eval_atom(mod, pp, env, true);
    if (!head) return NULL;
    /* Check if `head` is a constructor `Ctor(Name)` applied to an argument */
    if (head->kind == PETTA_ATOM_EXPR && head->arity == 2 &&
        head->args[0]->kind == PETTA_ATOM_SYM && strcmp(head->args[0]->text, "Ctor") == 0 &&
        gold_ml_can_start_arg(*pp)) {
        PettaAtom *arg = gold_ml_eval_atom(mod, pp, env, true);
        PettaAtom *cargs[2] = { petta_atom_clone(head->args[1]), arg };
        petta_atom_free(head);
        return gold_er_make_tag("Ctor", 2, cargs);
    }
    /* Check if `head` is a module function name or closure applied to 1+ arguments */
    if (gold_ml_can_start_arg(*pp)) {
        PettaAtom *args[4] = {0};
        uint32_t argc = 0;
        while (argc < 4u && gold_ml_can_start_arg(*pp)) {
            args[argc++] = gold_ml_eval_atom(mod, pp, env, true);
        }
        if (head->kind == PETTA_ATOM_SYM) {
            for (uint32_t f = 0; f < mod->nfns; f++) {
                const GoldMlFnDecl *fn = &mod->fns[f];
                if (strcmp(fn->name, head->text) == 0) {
                    mod->eval_steps++;
                    PettaEnv fenv;
                    petta_env_init(&fenv);
                    uint32_t bind_n = argc < fn->arity ? argc : fn->arity;
                    for (uint32_t i = 0; i < bind_n; i++) {
                        if (strcmp(fn->params[i], "()") != 0) {
                            petta_env_bind(&fenv, fn->params[i], args[i]);
                        }
                    }
                    const char *bp = fn->body;
                    PettaAtom *res = gold_ml_eval_expr(mod, &bp, &fenv);
                    petta_env_free(&fenv);
                    /* Over-application of a function returning a closure (e.g. `score_above 206 task`) */
                    for (uint32_t i = bind_n; i < argc; i++) {
                        PettaAtom *next_res = gold_ml_apply_val(mod, res, args[i]);
                        petta_atom_free(res);
                        res = next_res;
                    }
                    for (uint32_t i = 0; i < argc; i++) petta_atom_free(args[i]);
                    petta_atom_free(head);
                    return res;
                }
            }
        }
        /* Apply closure value `head` sequentially to `args` */
        PettaAtom *cur = head;
        for (uint32_t i = 0; i < argc; i++) {
            PettaAtom *next = gold_ml_apply_val(mod, cur, args[i]);
            petta_atom_free(cur);
            cur = next;
            petta_atom_free(args[i]);
        }
        return cur;
    }
    return head;
}

static inline PettaAtom *gold_ml_eval_add(GoldMlModule *mod, const char **pp, PettaEnv *env) {
    PettaAtom *lhs = gold_ml_eval_app(mod, pp, env);
    const char *p = gold_ml_skip_ws(*pp);
    while ((*p == '+' || (*p == '-' && p[1] != '>')) && lhs) {
        char op = *p++;
        *pp = p;
        PettaAtom *rhs = gold_ml_eval_app(mod, pp, env);
        if (lhs->kind == PETTA_ATOM_INT && rhs && rhs->kind == PETTA_ATOM_INT) {
            int64_t r = (op == '+') ? (lhs->ival + rhs->ival) : (lhs->ival - rhs->ival);
            petta_atom_free(lhs);
            petta_atom_free(rhs);
            lhs = petta_atom_int(r);
        } else {
            petta_atom_free(rhs);
        }
        p = gold_ml_skip_ws(*pp);
    }
    return lhs;
}

static inline PettaAtom *gold_ml_eval_cmp(GoldMlModule *mod, const char **pp, PettaEnv *env) {
    PettaAtom *lhs = gold_ml_eval_add(mod, pp, env);
    const char *p = gold_ml_skip_ws(*pp);
    if ((*p == '>' || *p == '<' || (*p == '=' && p[1] != '>')) && lhs) {
        char op[4] = {0};
        op[0] = *p++;
        if (*p == '=') op[1] = *p++;
        *pp = p;
        PettaAtom *rhs = gold_ml_eval_add(mod, pp, env);
        bool b = false;
        if (lhs->kind == PETTA_ATOM_INT && rhs && rhs->kind == PETTA_ATOM_INT) {
            if (strcmp(op, ">") == 0) b = (lhs->ival > rhs->ival);
            else if (strcmp(op, ">=") == 0) b = (lhs->ival >= rhs->ival);
            else if (strcmp(op, "<") == 0) b = (lhs->ival < rhs->ival);
            else if (strcmp(op, "<=") == 0) b = (lhs->ival <= rhs->ival);
            else if (strcmp(op, "=") == 0) b = (lhs->ival == rhs->ival);
        } else if (rhs) {
            b = petta_atom_eq(lhs, rhs);
        }
        petta_atom_free(lhs);
        petta_atom_free(rhs);
        return petta_atom_sym(b ? "true" : "false");
    }
    return lhs;
}

static inline PettaAtom *gold_ml_eval_cons(GoldMlModule *mod, const char **pp, PettaEnv *env) {
    PettaAtom *lhs = gold_ml_eval_cmp(mod, pp, env);
    const char *p = gold_ml_skip_ws(*pp);
    if (p[0] == ':' && p[1] == ':') {
        *pp = gold_ml_skip_ws(p + 2);
        PettaAtom *rhs = gold_ml_eval_cons(mod, pp, env);
        PettaAtom *cargs[2] = { lhs, rhs };
        return gold_er_make_tag("::", 2, cargs);
    }
    return lhs;
}

static inline PettaAtom *gold_ml_eval_expr(GoldMlModule *mod, const char **pp, PettaEnv *env) {
    const char *p = gold_ml_skip_ws(*pp);
    if (!*p) return petta_atom_sym("()");

    /* 1. `let <id> [<param>] = <e1> in <e2>` */
    if (gold_ml_at_kw(p, "let")) {
        p = gold_ml_skip_ws(p + 3);
        char vname[32] = {0}, param[32] = {0};
        size_t vl = 0;
        while (*p && (isalnum((unsigned char)*p) || *p == '_')) {
            if (vl + 1 < sizeof(vname)) vname[vl++] = *p;
            p++;
        }
        p = gold_ml_skip_ws(p);
        if (*p != '=') {
            size_t pl = 0;
            while (*p && (isalnum((unsigned char)*p) || *p == '_')) {
                if (pl + 1 < sizeof(param)) param[pl++] = *p;
                p++;
            }
            p = gold_ml_skip_ws(p);
        }
        if (*p == '=') p = gold_ml_skip_ws(p + 1);
        /* Find matching `in` */
        const char *in_pos = p;
        int ldepth = 1;
        while (*in_pos) {
            if (gold_ml_at_kw(in_pos, "let") && (in_pos == p || !isalnum((unsigned char)in_pos[-1]))) {
                ldepth++;
                in_pos += 3;
                continue;
            }
            if (gold_ml_at_kw(in_pos, "in") && !isalnum((unsigned char)in_pos[-1]) && in_pos[-1] != '_') {
                ldepth--;
                if (ldepth == 0) break;
                in_pos += 2;
                continue;
            }
            in_pos++;
        }
        char rhs_buf[256] = {0};
        size_t rl = (size_t)(in_pos - p);
        while (rl > 0 && (p[rl - 1] == ' ' || p[rl - 1] == '\n')) rl--;
        if (rl >= sizeof(rhs_buf)) rl = sizeof(rhs_buf) - 1u;
        memcpy(rhs_buf, p, rl);

        PettaAtom *bval = NULL;
        if (param[0] != '\0') {
            PettaAtom *cargs[2] = { petta_atom_sym(param), petta_atom_sym(rhs_buf) };
            bval = gold_er_make_tag("Closure", 2, cargs);
        } else {
            const char *rp = rhs_buf;
            bval = gold_ml_eval_expr(mod, &rp, env);
        }
        petta_env_bind(env, vname, bval);
        petta_atom_free(bval);
        *pp = gold_ml_skip_ws(*in_pos ? (in_pos + 2) : in_pos);
        return gold_ml_eval_expr(mod, pp, env);
    }

    /* 2. `if <cond> then <e1> else <e2>` */
    if (gold_ml_at_kw(p, "if")) {
        p = gold_ml_skip_ws(p + 2);
        PettaAtom *cval = gold_ml_eval_cons(mod, &p, env);
        bool is_true = (cval && cval->kind == PETTA_ATOM_SYM && strcmp(cval->text, "true") == 0);
        petta_atom_free(cval);
        p = gold_ml_skip_ws(p);
        if (gold_ml_at_kw(p, "then")) p = gold_ml_skip_ws(p + 4);
        /* Locate matching `else` */
        const char *else_pos = p;
        int idepth = 1;
        while (*else_pos) {
            if (gold_ml_at_kw(else_pos, "if") && (else_pos == p || !isalnum((unsigned char)else_pos[-1]))) {
                idepth++;
                else_pos += 2;
                continue;
            }
            if (gold_ml_at_kw(else_pos, "else") && !isalnum((unsigned char)else_pos[-1])) {
                idepth--;
                if (idepth == 0) break;
                else_pos += 4;
                continue;
            }
            else_pos++;
        }
        char tbuf[256] = {0};
        size_t tl = (size_t)(else_pos - p);
        if (tl >= sizeof(tbuf)) tl = sizeof(tbuf) - 1u;
        memcpy(tbuf, p, tl);
        const char *ebuf = *else_pos ? gold_ml_skip_ws(else_pos + 4) : "";
        if (is_true) {
            const char *tp = tbuf;
            *pp = ebuf + strlen(ebuf);
            return gold_ml_eval_expr(mod, &tp, env);
        } else {
            *pp = ebuf;
            return gold_ml_eval_expr(mod, pp, env);
        }
    }

    /* 3. `fun <param> -> <body>` */
    if (gold_ml_at_kw(p, "fun")) {
        p = gold_ml_skip_ws(p + 3);
        char param[32] = {0};
        size_t pl = 0;
        while (*p && (isalnum((unsigned char)*p) || *p == '_')) {
            if (pl + 1 < sizeof(param)) param[pl++] = *p;
            p++;
        }
        p = gold_ml_skip_ws(p);
        if (strncmp(p, "->", 2) == 0) p = gold_ml_skip_ws(p + 2);
        /* Capture body up to closing `)` if inside parens, or end of string */
        char body_buf[256] = {0};
        size_t bl = 0;
        int bdepth = 0;
        while (*p) {
            if (*p == '(') bdepth++;
            else if (*p == ')') {
                if (bdepth == 0) break;
                bdepth--;
            }
            if (bl + 1 < sizeof(body_buf)) body_buf[bl++] = *p;
            p++;
        }
        *pp = p;
        PettaAtom *cargs[10];
        uint32_t nc = 0;
        cargs[nc++] = petta_atom_sym(param);
        cargs[nc++] = petta_atom_sym(body_buf);
        for (uint32_t i = 0; i < env->nbinds && nc + 2 <= 10u; i++) {
            cargs[nc++] = petta_atom_sym(env->binds[i].var);
            cargs[nc++] = petta_atom_clone(env->binds[i].val);
        }
        return gold_er_make_tag("Closure", nc, cargs);
    }

    /* 4. `match <scrut> with | <pat1> -> <rhs1> | <pat2> -> <rhs2> ...` */
    if (gold_ml_at_kw(p, "match")) {
        p = gold_ml_skip_ws(p + 5);
        PettaAtom *sitems[4];
        sitems[0] = gold_ml_eval_cons(mod, &p, env);
        uint32_t ns = 1u;
        p = gold_ml_skip_ws(p);
        while (*p == ',' && ns < 4u) {
            p = gold_ml_skip_ws(p + 1);
            sitems[ns++] = gold_ml_eval_cons(mod, &p, env);
            p = gold_ml_skip_ws(p);
        }
        PettaAtom *scrut = (ns == 1u) ? sitems[0] : gold_er_make_tag(",", ns, sitems);
        p = gold_ml_skip_ws(p);
        if (gold_ml_at_kw(p, "with")) p = gold_ml_skip_ws(p + 4);
        if (*p == '|') p = gold_ml_skip_ws(p + 1);

        while (*p) {
            PettaAtom *pat = gold_ml_parse_pat_tuple(&p);
            p = gold_ml_skip_ws(p);
            if (strncmp(p, "->", 2) == 0) p = gold_ml_skip_ws(p + 2);
            /* Scan branch RHS up to next top-level `|` */
            char br_buf[384] = {0};
            size_t bl = 0;
            int mdepth = 0, pdepth = 0;
            while (*p) {
                if (pdepth == 0 && mdepth == 0 && *p == '|') break;
                if (*p == '(' || *p == '[') pdepth++;
                else if ((*p == ')' || *p == ']') && pdepth > 0) pdepth--;
                if (gold_ml_at_kw(p, "match") && (bl == 0 || !isalnum((unsigned char)br_buf[bl - 1]))) {
                    mdepth++;
                }
                if (bl + 1 < sizeof(br_buf)) br_buf[bl++] = *p;
                p++;
            }
            if (*p == '|') p = gold_ml_skip_ws(p + 1);

            PettaEnv benv;
            petta_env_init(&benv);
            for (uint32_t i = 0; i < env->nbinds; i++) {
                petta_env_bind(&benv, env->binds[i].var, env->binds[i].val);
            }
            bool matched = gold_ml_match_pat(pat, scrut, &benv);
            petta_atom_free(pat);
            if (matched) {
                petta_atom_free(scrut);
                *pp = p + strlen(p);
                const char *bp = br_buf;
                PettaAtom *res = gold_ml_eval_expr(mod, &bp, &benv);
                petta_env_free(&benv);
                return res;
            }
            petta_env_free(&benv);
        }
        petta_atom_free(scrut);
        *pp = p;
        return petta_atom_sym("match_failure");
    }

    *pp = p;
    return gold_ml_eval_cons(mod, pp, env);
}

static inline bool gold_ml_eval_str(
    GoldMlModule *mod,
    const char *expr_str,
    char *out_buf,
    size_t out_cap)
{
    PettaEnv env;
    petta_env_init(&env);
    const char *p = expr_str;
    PettaAtom *res = gold_ml_eval_expr(mod, &p, &env);
    gold_ml_format_atom(res, out_buf, out_cap);
    petta_atom_free(res);
    petta_env_free(&env);
    return out_buf[0] != '\0' && strcmp(out_buf, "match_failure") != 0;
}

/* =========================================================================
 * PART 4: Maude M0 + M1 — Frozen Contexts, Certified ACU Equations &
 *         Conditional Rules with Multistep Rewrite Conditions (`=>*`) over tcalc
 * ========================================================================= */

typedef enum {
    MAUDE_OK                    = 0,
    MAUDE_REFUSE_FROZEN_CONTEXT = 1,
    MAUDE_REFUSE_CONDITION_FAIL = 2
} GoldMaudeRefusalKind;

typedef struct {
    char state_label[32];
    uint32_t ntokens;
    char tokens[32][64]; /* ACU multiset of soup tokens (canonical sorted order, identity removed) */
    bool inner_subterm_ready;
} GoldMaudeConfig;

typedef struct {
    char name[32];
    uint32_t arity;
    bool is_assoc;
    bool is_comm;
    char id_token[32];
    uint32_t frozen_mask; /* bit i = 1 if 0-based arg i is frozen */
} GoldMaudeOpDecl;

typedef struct {
    uint32_t nlhs;
    char lhs[4][64];
    char rhs[64];
} GoldMaudeEqDecl;

typedef struct {
    char label[32];
    uint32_t nlhs;
    char lhs[4][64];
    uint32_t nrhs;
    char rhs[4][64];
    uint32_t nreq;
    char req[4][64];
    bool is_conditional;
    bool cond_is_rew; /* true for `if L => R`, false for `if L = R` */
    char cond_lhs[64];
    char cond_rhs[64];
} GoldMaudeRlDecl;

typedef struct {
    int sort_val;
    int sort_state;
    int con_state;
    int rule_maude_step;
    TcAdmissionProfile profile_linear;
    uint64_t eq_normalizations;
    uint64_t rl_rewrites_admitted;
    uint64_t crl_subsearches_completed;
    GoldMaudeRefusalKind last_refusal;
    TcAdmittedEvent last_event;
    TcAdmissionReceipt last_receipt;

    /* Parsed / registered module declarations (no hardcoded rules!) */
    uint32_t nvars;
    char vars[32][32];
    uint32_t nops;
    GoldMaudeOpDecl ops[64];
    uint32_t neqs;
    GoldMaudeEqDecl eqs[64];
    uint32_t nrules;
    GoldMaudeRlDecl rules[64];
} GoldMaudeEngine;

static inline void gold_maude_register_id_token(GoldMaudeEngine *me, const char *op_name, const char *id_tok) {
    if (me->nops >= 64) return;
    GoldMaudeOpDecl *op = &me->ops[me->nops++];
    memset(op, 0, sizeof(*op));
    snprintf(op->name, sizeof(op->name), "%s", op_name);
    op->arity = 2;
    op->is_assoc = true;
    op->is_comm = true;
    snprintf(op->id_token, sizeof(op->id_token), "%s", id_tok);
}

static inline void gold_maude_register_op_frozen(GoldMaudeEngine *me, const char *op_name, uint32_t arity, uint32_t frozen_mask) {
    for (uint32_t i = 0; i < me->nops; i++) {
        if (strcmp(me->ops[i].name, op_name) == 0) {
            me->ops[i].arity = arity;
            me->ops[i].frozen_mask = frozen_mask;
            return;
        }
    }
    if (me->nops >= 64) return;
    GoldMaudeOpDecl *op = &me->ops[me->nops++];
    memset(op, 0, sizeof(*op));
    snprintf(op->name, sizeof(op->name), "%s", op_name);
    op->arity = arity;
    op->frozen_mask = frozen_mask;
}

static inline void gold_maude_register_eq2(GoldMaudeEngine *me, const char *lhs0, const char *lhs1, const char *rhs) {
    if (me->neqs >= 64) return;
    GoldMaudeEqDecl *eq = &me->eqs[me->neqs++];
    memset(eq, 0, sizeof(*eq));
    eq->nlhs = (lhs1 && lhs1[0]) ? 2u : 1u;
    snprintf(eq->lhs[0], sizeof(eq->lhs[0]), "%s", lhs0);
    if (eq->nlhs == 2u) snprintf(eq->lhs[1], sizeof(eq->lhs[1]), "%s", lhs1);
    snprintf(eq->rhs, sizeof(eq->rhs), "%s", rhs);
}

static inline void gold_maude_register_rl1(
    GoldMaudeEngine *me,
    const char *label,
    const char *lhs0,
    const char *req0,
    const char *rhs0)
{
    if (me->nrules >= 64) return;
    GoldMaudeRlDecl *r = &me->rules[me->nrules++];
    memset(r, 0, sizeof(*r));
    snprintf(r->label, sizeof(r->label), "%s", label);
    r->nlhs = 1u;
    snprintf(r->lhs[0], sizeof(r->lhs[0]), "%s", lhs0);
    if (req0 && req0[0]) {
        r->nreq = 1u;
        snprintf(r->req[0], sizeof(r->req[0]), "%s", req0);
    }
    r->nrhs = 1u;
    snprintf(r->rhs[0], sizeof(r->rhs[0]), "%s", rhs0);
}

static inline void gold_maude_register_crl(
    GoldMaudeEngine *me,
    const char *label,
    const char *lhs0,
    const char *lhs1,
    const char *rhs0,
    bool cond_is_rew,
    const char *cond_lhs,
    const char *cond_rhs)
{
    if (me->nrules >= 64) return;
    GoldMaudeRlDecl *r = &me->rules[me->nrules++];
    memset(r, 0, sizeof(*r));
    snprintf(r->label, sizeof(r->label), "%s", label);
    r->nlhs = (lhs1 && lhs1[0]) ? 2u : 1u;
    snprintf(r->lhs[0], sizeof(r->lhs[0]), "%s", lhs0);
    if (r->nlhs == 2u) snprintf(r->lhs[1], sizeof(r->lhs[1]), "%s", lhs1);
    r->nrhs = 1u;
    snprintf(r->rhs[0], sizeof(r->rhs[0]), "%s", rhs0);
    r->is_conditional = true;
    r->cond_is_rew = cond_is_rew;
    snprintf(r->cond_lhs, sizeof(r->cond_lhs), "%s", cond_lhs);
    snprintf(r->cond_rhs, sizeof(r->cond_rhs), "%s", cond_rhs);
}

static inline void gold_maude_init(GoldMaudeEngine *me) {
    memset(me, 0, sizeof(*me));
    tc_init(1u << 19, 1u << 18);
    tc_protect(GOLD_SPACE_MAUDE_STATE);

    me->sort_val = tc_sort(SORT_PURE | SORT_STRICT);
    me->sort_state = tc_sort(SORT_STRICT | SORT_PROVABLE);
    Binder b1 = { .sort = (uint16_t)me->sort_val, .bound = 0, .deps = 0 };
    me->con_state = tc_con((uint16_t)me->sort_state, 0, 1, &b1);

    Binder ctx1[1] = { b1 };
    {
        tc_ctx(1, ctx1);
        Term v0 = tc_v(0);
        Rule r;
        memset(&r, 0, sizeof(r));
        r.fresh = -1;
        r.inputs = 0x1;   /* the state the host rewrote to */
        r.make = (Pat){ .t = tc_app(me->con_state, &v0), .space = GOLD_SPACE_MAUDE_STATE };
        me->rule_maude_step = tc_rule(&r);
    }
    tc_seal();
    me->profile_linear = tc_admission_custom_profile("gold_maude_linear", false, true, false, false, NULL, NULL);

    /* Register default protocol module declarations in `me` table (used when no external `.maude` file is parsed) */
    gold_maude_register_id_token(me, "__", "none");
    gold_maude_register_id_token(me, "__", "empty");
    gold_maude_register_eq2(me, "half_grant", "half_grant", "grant_ready");
    gold_maude_register_rl1(me, "step1", "probe_start", "quota_ok", "stage1_checked");
    gold_maude_register_rl1(me, "step2", "stage1_checked", "policy_ok", "stage2_verified");
    gold_maude_register_rl1(me, "step3", "stage2_verified", "", "audit_passed");
    gold_maude_register_crl(me, "commit-protocol", "req_slot", "grant_ready", "SafeGrant",
                            true, "probe_start", "audit_passed");
}

static inline bool gold_maude_is_id_token(const GoldMaudeEngine *me, const char *tok) {
    if (!tok || tok[0] == '\0') return true;
    for (uint32_t i = 0; i < me->nops; i++) {
        if (me->ops[i].id_token[0] != '\0' && strcmp(me->ops[i].id_token, tok) == 0) {
            return true;
        }
    }
    return false;
}

static inline uint32_t gold_maude_lookup_frozen_mask(const GoldMaudeEngine *me, const char *op_name) {
    for (uint32_t i = 0; i < me->nops; i++) {
        if (strcmp(me->ops[i].name, op_name) == 0) return me->ops[i].frozen_mask;
    }
    return 0u;
}

/* Normalize a single term/token under unary wrapper equations (e.g. `eq group(empty) = empty`,
 * `eq group(group(W)) = group(W)`) even beneath frozen operators like `sealed(...)`! */
static inline void gold_maude_normalize_term_str(GoldMaudeEngine *me, char *tok, size_t cap) {
    bool changed = true;
    while (changed) {
        changed = false;
        /* If `tok` is `op(inner)`, recursively normalize `inner` first */
        char *lp = strchr(tok, '(');
        size_t len = strlen(tok);
        if (lp && len > 0 && tok[len - 1] == ')' && strchr(lp + 1, ',') == NULL) {
            size_t op_len = (size_t)(lp - tok);
            char op_name[32] = {0};
            if (op_len < sizeof(op_name)) {
                memcpy(op_name, tok, op_len);
                char inner[64] = {0};
                size_t in_len = len - op_len - 2u;
                if (in_len < sizeof(inner)) {
                    memcpy(inner, lp + 1, in_len);
                    char prev_inner[64];
                    snprintf(prev_inner, sizeof(prev_inner), "%s", inner);
                    gold_maude_normalize_term_str(me, inner, sizeof(inner));
                    if (strcmp(inner, prev_inner) != 0) {
                        snprintf(tok, cap, "%s(%s)", op_name, inner);
                        changed = true;
                    }
                }
            }
        }
        /* Check unary equations in `me->eqs`:
         *   - exact match `eq->lhs[0] == tok` -> `eq->rhs`
         *   - schematic wrapper match `op(op($W)) -> op($W)` */
        for (uint32_t e = 0; e < me->neqs; e++) {
            const GoldMaudeEqDecl *eq = &me->eqs[e];
            if (eq->nlhs != 1u) continue;
            if (strcmp(eq->lhs[0], tok) == 0) {
                snprintf(tok, cap, "%s", eq->rhs);
                me->eq_normalizations++;
                changed = true;
                break;
            }
            /* Parametric idempotence `op(op($W)) = op($W)` */
            const char *pat = eq->lhs[0];
            const char * dlr = strchr(pat, '$');
            if (dlr && dlr > pat) {
                size_t prefix_len = (size_t)(dlr - pat);
                if (strncmp(tok, pat, prefix_len) == 0) {
                    /* Count trailing ')' in pat after $var */
                    const char *pat_end = pat + strlen(pat);
                    size_t close_cnt = 0;
                    while (pat_end > dlr && *(pat_end - 1) == ')') { close_cnt++; pat_end--; }
                    size_t tlen = strlen(tok);
                    if (tlen > prefix_len + close_cnt) {
                        bool closes_ok = true;
                        for (size_t c = 0; c < close_cnt; c++) {
                            if (tok[tlen - 1u - c] != ')') { closes_ok = false; break; }
                        }
                        if (closes_ok) {
                            char bound_w[64] = {0};
                            size_t wlen = tlen - prefix_len - close_cnt;
                            if (wlen < sizeof(bound_w)) {
                                memcpy(bound_w, tok + prefix_len, wlen);
                                const char *rhs_dlr = strchr(eq->rhs, '$');
                                if (rhs_dlr) {
                                    size_t rpre = (size_t)(rhs_dlr - eq->rhs);
                                    const char *rpost = rhs_dlr + 1;
                                    while (*rpost && ((*rpost >= 'A' && *rpost <= 'Z') || (*rpost >= 'a' && *rpost <= 'z') || (*rpost >= '0' && *rpost <= '9') || *rpost == '_')) rpost++;
                                    char rebuilt[256];
                                    snprintf(rebuilt, sizeof(rebuilt), "%.*s%s%s", (int)rpre, eq->rhs, bound_w, rpost);
                                    snprintf(tok, cap, "%.*s", (int)(cap > 0 ? cap - 1 : 0), rebuilt);
                                    me->eq_normalizations++;
                                    changed = true;
                                    break;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/* Certified ACU Equation Normalization driven by `me->ops` and `me->eqs`:
 *   1. Normalizes each subterm under unary equations (even inside frozen operators),
 *   2. Eliminates declared ACU identity tokens (`id: none`, `id: empty`),
 *   3. Canonically sorts the ACU soup multiset,
 *   4. Applies binary ACU coalescing equations (`eq A B = C`) from `me->eqs`! */
static inline void gold_maude_normalize_acu(GoldMaudeEngine *me, GoldMaudeConfig *cfg) {
    me->eq_normalizations++;
    /* 1. Normalize individual tokens and eliminate declared ACU identities */
    uint32_t w = 0;
    for (uint32_t i = 0; i < cfg->ntokens; i++) {
        gold_maude_normalize_term_str(me, cfg->tokens[i], sizeof(cfg->tokens[i]));
        if (gold_maude_is_id_token(me, cfg->tokens[i])) continue;
        if (w != i) memcpy(cfg->tokens[w], cfg->tokens[i], sizeof(cfg->tokens[w]));
        w++;
    }
    cfg->ntokens = w;

    /* 2. Sort tokens lexicographically (AC commutativity + associativity) */
    for (uint32_t i = 0; i < cfg->ntokens; i++) {
        for (uint32_t j = i + 1; j < cfg->ntokens; j++) {
            if (strcmp(cfg->tokens[j], cfg->tokens[i]) < 0) {
                char tmp[64];
                memcpy(tmp, cfg->tokens[i], sizeof(tmp));
                memcpy(cfg->tokens[i], cfg->tokens[j], sizeof(cfg->tokens[i]));
                memcpy(cfg->tokens[j], tmp, sizeof(cfg->tokens[j]));
            }
        }
    }

    /* 3. Apply binary ACU equations (`eq lhs0 lhs1 = rhs`) from `me->eqs` */
    for (uint32_t e = 0; e < me->neqs; e++) {
        const GoldMaudeEqDecl *eq = &me->eqs[e];
        if (eq->nlhs != 2u) continue;
        for (uint32_t i = 0; i < cfg->ntokens; i++) {
            if (strcmp(cfg->tokens[i], eq->lhs[0]) != 0) continue;
            for (uint32_t j = i + 1; j < cfg->ntokens; j++) {
                if (strcmp(cfg->tokens[j], eq->lhs[1]) == 0) {
                    snprintf(cfg->tokens[i], sizeof(cfg->tokens[i]), "%s", eq->rhs);
                    for (uint32_t k = j; k + 1 < cfg->ntokens; k++) {
                        memcpy(cfg->tokens[k], cfg->tokens[k + 1], sizeof(cfg->tokens[k]));
                    }
                    cfg->ntokens--;
                    gold_maude_normalize_acu(me, cfg);
                    return;
                }
            }
        }
    }
}

static inline bool gold_maude_has_token(const GoldMaudeConfig *cfg, const char *tok) {
    for (uint32_t i = 0; i < cfg->ntokens; i++) {
        if (strcmp(cfg->tokens[i], tok) == 0) return true;
    }
    return false;
}

static inline bool gold_maude_consume_token(GoldMaudeConfig *cfg, const char *tok) {
    for (uint32_t i = 0; i < cfg->ntokens; i++) {
        if (strcmp(cfg->tokens[i], tok) == 0) {
            for (uint32_t k = i; k + 1 < cfg->ntokens; k++)
                memcpy(cfg->tokens[k], cfg->tokens[k + 1], sizeof(cfg->tokens[k]));
            cfg->ntokens--;
            return true;
        }
    }
    return false;
}

static inline void gold_maude_add_token(GoldMaudeConfig *cfg, const char *tok) {
    if (cfg->ntokens < 32) {
        snprintf(cfg->tokens[cfg->ntokens++], sizeof(cfg->tokens[0]), "%s", tok);
    }
}

static inline void gold_maude_commit_tc_step(GoldMaudeEngine *me) {
    uint64_t fid = tc_fresh_name();
    while (fid == 0) fid = tc_fresh_name();
    Term inst[TC_VARS];
    memset(inst, 0, sizeof(inst));
    inst[0] = tc_name((uint16_t)me->sort_val, fid);
    TcPreparedStep cand;
    memset(&cand, 0, sizeof(cand));
    cand.rule = me->rule_maude_step;
    cand.inst = inst;
    TcPreparedEffect eff;
    TcAdmissionReceipt rec;
    TcRefusalReason ref = TC_REFUSE_NONE;
    if (tc_bridge_execute_candidate(&cand, &me->profile_linear, &eff, &me->last_event, &rec, &ref) == TC_BRIDGE_ADMITTED) {
        me->last_receipt = rec;
        me->rl_rewrites_admitted++;
    }
}

/* Attempt a rewrite inside argument position `arg_pos` under operator `frozen_mask`.
 * If `(frozen_mask & (1u << arg_pos)) != 0`, rewriting is REFUSED (`MAUDE_REFUSE_FROZEN_CONTEXT`),
 * whereas equational normalization is always permitted! */
static inline bool gold_maude_try_context_rewrite(
    GoldMaudeEngine *me,
    GoldMaudeConfig *cfg,
    uint32_t arg_pos,
    uint32_t frozen_mask)
{
    /* Equations normalize even inside frozen contexts */
    gold_maude_normalize_acu(me, cfg);
    if ((frozen_mask & (1u << arg_pos)) != 0u) {
        me->last_refusal = MAUDE_REFUSE_FROZEN_CONTEXT;
        return false;
    }
    me->last_refusal = MAUDE_OK;
    cfg->inner_subterm_ready = true;
    gold_maude_commit_tc_step(me);
    return true;
}

/* Execute one unconditional rule step (`!r->is_conditional`) from `me->rules` on `sub` */
static inline bool gold_maude_step_unconditional(GoldMaudeEngine *me, GoldMaudeConfig *sub) {
    gold_maude_normalize_acu(me, sub);
    for (uint32_t r_idx = 0; r_idx < me->nrules; r_idx++) {
        const GoldMaudeRlDecl *r = &me->rules[r_idx];
        if (r->is_conditional) continue;
        /* Check required context tokens */
        bool req_ok = true;
        for (uint32_t q = 0; q < r->nreq; q++) {
            if (!gold_maude_has_token(sub, r->req[q])) { req_ok = false; break; }
        }
        if (!req_ok) continue;
        /* Check LHS tokens on a copy */
        GoldMaudeConfig next = *sub;
        bool lhs_ok = true;
        for (uint32_t l = 0; l < r->nlhs; l++) {
            if (!gold_maude_consume_token(&next, r->lhs[l])) { lhs_ok = false; break; }
        }
        if (!lhs_ok) continue;
        for (uint32_t k = 0; k < r->nrhs; k++) {
            gold_maude_add_token(&next, r->rhs[k]);
        }
        gold_maude_normalize_acu(me, &next);
        *sub = next;
        return true;
    }
    return false;
}

/* Execute a conditional rule (`crl`) from `me->rules` by running a multistep rewrite sub-search (`=>*`)
 * using `me->rules` on a cloned configuration! */
static inline bool gold_maude_apply_crl_multistep(
    GoldMaudeEngine *me,
    GoldMaudeConfig *cfg,
    uint32_t max_cond_steps)
{
    gold_maude_normalize_acu(me, cfg);
    for (uint32_t r_idx = 0; r_idx < me->nrules; r_idx++) {
        const GoldMaudeRlDecl *r = &me->rules[r_idx];
        if (!r->is_conditional) continue;

        GoldMaudeConfig after_lhs = *cfg;
        bool lhs_ok = true;
        for (uint32_t l = 0; l < r->nlhs; l++) {
            if (!gold_maude_consume_token(&after_lhs, r->lhs[l])) { lhs_ok = false; break; }
        }
        if (!lhs_ok) continue;

        if (!r->cond_is_rew) {
            if (strcmp(r->cond_lhs, r->cond_rhs) != 0) continue;
        } else {
            GoldMaudeConfig sub = *cfg;
            gold_maude_add_token(&sub, r->cond_lhs);
            uint32_t steps = 0;
            while (steps < max_cond_steps) {
                gold_maude_normalize_acu(me, &sub);
                if (gold_maude_has_token(&sub, r->cond_rhs)) break;
                steps++;
                if (!gold_maude_step_unconditional(me, &sub)) break;
            }
            if (!gold_maude_has_token(&sub, r->cond_rhs)) {
                continue;
            }
            me->crl_subsearches_completed++;
        }

        for (uint32_t k = 0; k < r->nrhs; k++) {
            gold_maude_add_token(&after_lhs, r->rhs[k]);
        }
        snprintf(after_lhs.state_label, sizeof(after_lhs.state_label), "Committed");
        gold_maude_normalize_acu(me, &after_lhs);
        *cfg = after_lhs;
        gold_maude_commit_tc_step(me);
        me->last_refusal = MAUDE_OK;
        return true;
    }
    me->last_refusal = MAUDE_REFUSE_CONDITION_FAIL;
    return false;
}

/* Parse a `.maude` module source file (`resource_protocol.maude`, `nested_workflow.maude`, etc.)
 * into `GoldMaudeEngine`'s operator, equation, and rewrite-rule tables! */
static inline bool gold_maude_is_decl_var(const GoldMaudeEngine *me, const char *tok) {
    for (uint32_t i = 0; i < me->nvars; i++) {
        if (strcmp(me->vars[i], tok) == 0) return true;
    }
    return false;
}

static inline void gold_maude_varify_term(const GoldMaudeEngine *me, const char *in, char *out, size_t cap) {
    size_t pos = 0;
    const char *p = in;
    while (*p && pos + 1 < cap) {
        if ((*p >= 'A' && *p <= 'Z') || (*p >= 'a' && *p <= 'z') || (*p >= '0' && *p <= '9') || *p == '_') {
            char id[32] = {0};
            size_t ilen = 0;
            while ((*p >= 'A' && *p <= 'Z') || (*p >= 'a' && *p <= 'z') || (*p >= '0' && *p <= '9') || *p == '_') {
                if (ilen + 1 < sizeof(id)) id[ilen++] = *p;
                p++;
            }
            if (gold_maude_is_decl_var(me, id)) {
                pos += (size_t)snprintf(out + pos, cap - pos, "$%s", id);
            } else {
                pos += (size_t)snprintf(out + pos, cap - pos, "%s", id);
            }
        } else if (*p == ' ' && pos > 0 && out[pos - 1] == ',') {
            p++; /* normalize `f(a, b)` -> `f(a,b)` */
        } else {
            out[pos++] = *p++;
        }
    }
    out[pos] = '\0';
}

/* Split a whitespace-separated soup of top-level Maude terms (keeping balanced `(...)` together) */
static inline uint32_t gold_maude_split_soup_terms(
    const GoldMaudeEngine *me,
    const char *s,
    char out_terms[][64],
    uint32_t max_terms)
{
    uint32_t count = 0;
    const char *p = s;
    while (*p && count < max_terms) {
        while (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n') p++;
        if (*p == '\0' || (*p == '.' && (p[1] == '\0' || p[1] == ' ' || p[1] == '\n'))) break;
        char raw[64] = {0};
        size_t rlen = 0;
        int depth = 0;
        while (*p) {
            if (depth == 0 && (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n')) break;
            if (depth == 0 && *p == '.' && (p[1] == '\0' || p[1] == ' ' || p[1] == '\n')) break;
            if (*p == '(') depth++;
            else if (*p == ')' && depth > 0) depth--;
            if (rlen + 1 < sizeof(raw)) raw[rlen++] = *p;
            p++;
        }
        raw[rlen] = '\0';
        if (rlen > 0) {
            if (me) gold_maude_varify_term(me, raw, out_terms[count], 64);
            else snprintf(out_terms[count], 64, "%s", raw);
            count++;
        }
    }
    return count;
}

static inline bool gold_maude_parse_source(GoldMaudeEngine *me, const char *src) {
    if (!me || !src) return false;
    me->nvars = 0;
    me->nops = 0;
    me->neqs = 0;
    me->nrules = 0;

    char line_buf[512];
    const char *cur = src;
    while (*cur) {
        while (*cur == ' ' || *cur == '\t' || *cur == '\r' || *cur == '\n') cur++;
        if (!*cur) break;
        /* Read statement up to terminating ` .` or newline-for-load */
        if (strncmp(cur, "load ", 5) == 0 || strncmp(cur, "mod ", 4) == 0 ||
            strncmp(cur, "fmod ", 5) == 0 || strncmp(cur, "endm", 4) == 0 ||
            strncmp(cur, "endfm", 5) == 0) {
            while (*cur && *cur != '\n') cur++;
            continue;
        }
        size_t lpos = 0;
        while (*cur && lpos + 1 < sizeof(line_buf)) {
            if (*cur == '.' && (cur[1] == '\0' || cur[1] == ' ' || cur[1] == '\t' || cur[1] == '\r' || cur[1] == '\n')) {
                cur++;
                break;
            }
            line_buf[lpos++] = (*cur == '\n' || *cur == '\r') ? ' ' : *cur;
            cur++;
        }
        line_buf[lpos] = '\0';
        char *s = line_buf;
        while (*s == ' ') s++;

        /* 1. `var` / `vars` declaration */
        if (strncmp(s, "var ", 4) == 0 || strncmp(s, "vars ", 5) == 0) {
            char *p = s + (s[3] == 's' ? 5 : 4);
            char *colon = strchr(p, ':');
            if (colon) *colon = '\0';
            while (*p) {
                while (*p == ' ') p++;
                if (!*p) break;
                char vname[32] = {0};
                size_t vl = 0;
                while (*p && *p != ' ') {
                    if (vl + 1 < sizeof(vname)) vname[vl++] = *p;
                    p++;
                }
                if (vl > 0 && me->nvars < 32) {
                    snprintf(me->vars[me->nvars++], 32, "%s", vname);
                }
            }
            continue;
        }

        /* 2. `op` / `ops` declaration with attributes `[...]` */
        if (strncmp(s, "op ", 3) == 0 || strncmp(s, "ops ", 4) == 0) {
            char *lb = strchr(s, '[');
            char *rb = lb ? strchr(lb, ']') : NULL;
            char *colon = strchr(s, ':');
            char *arrow = colon ? strstr(colon, "->") : NULL;
            if (!colon || !arrow) continue;
            /* Count domain sorts between `:` and `->` for arity */
            uint32_t arity = 0;
            {
                const char *dp = colon + 1;
                while (dp < arrow) {
                    while (dp < arrow && *dp == ' ') dp++;
                    if (dp >= arrow) break;
                    arity++;
                    while (dp < arrow && *dp != ' ') dp++;
                }
            }
            uint32_t frozen_mask = 0u;
            char id_tok[32] = {0};
            if (lb && rb && rb > lb) {
                char attr[128] = {0};
                size_t alen = (size_t)(rb - lb - 1);
                if (alen >= sizeof(attr)) alen = sizeof(attr) - 1u;
                memcpy(attr, lb + 1, alen);
                const char *id_p = strstr(attr, "id:");
                if (id_p) {
                    id_p += 3;
                    while (*id_p == ' ') id_p++;
                    size_t il = 0;
                    while (*id_p && *id_p != ' ' && *id_p != ']') {
                        if (il + 1 < sizeof(id_tok)) id_tok[il++] = *id_p;
                        id_p++;
                    }
                }
                const char *fr_p = strstr(attr, "frozen");
                if (fr_p) {
                    const char *lp2 = strchr(fr_p, '(');
                    if (lp2) {
                        uint32_t pos1 = (uint32_t)strtoul(lp2 + 1, NULL, 10);
                        if (pos1 >= 1u && pos1 <= 32u) frozen_mask |= (1u << (pos1 - 1u));
                    } else {
                        frozen_mask = (arity > 0 && arity < 32u) ? ((1u << arity) - 1u) : 0xFFFFFFFFu;
                    }
                }
            }
            /* Register each operator name before `:` */
            char *op_p = s + (s[2] == 's' ? 4 : 3);
            while (op_p < colon) {
                while (op_p < colon && *op_p == ' ') op_p++;
                if (op_p >= colon) break;
                char oname[32] = {0};
                size_t ol = 0;
                while (op_p < colon && *op_p != ' ') {
                    if (ol + 1 < sizeof(oname)) oname[ol++] = *op_p;
                    op_p++;
                }
                if (ol > 0) {
                    if (id_tok[0]) gold_maude_register_id_token(me, oname, id_tok);
                    if (frozen_mask != 0u) gold_maude_register_op_frozen(me, oname, arity, frozen_mask);
                }
            }
            continue;
        }

        /* 3. `eq <lhs> = <rhs>` */
        if (strncmp(s, "eq ", 3) == 0) {
            char *eq_sign = strstr(s + 3, " = ");
            if (!eq_sign) continue;
            *eq_sign = '\0';
            char lhs_terms[4][64] = {{0}};
            uint32_t nl = gold_maude_split_soup_terms(me, s + 3, lhs_terms, 4);
            char rhs_term[64] = {0};
            gold_maude_varify_term(me, eq_sign + 3, rhs_term, sizeof(rhs_term));
            /* Trim leading/trailing spaces on rhs_term */
            char *rp = rhs_term;
            while (*rp == ' ') rp++;
            size_t rlen = strlen(rp);
            while (rlen > 0 && rp[rlen - 1] == ' ') rp[--rlen] = '\0';
            if (nl >= 1u && me->neqs < 64) {
                GoldMaudeEqDecl *eq = &me->eqs[me->neqs++];
                memset(eq, 0, sizeof(*eq));
                eq->nlhs = nl;
                for (uint32_t i = 0; i < nl; i++) snprintf(eq->lhs[i], 64, "%s", lhs_terms[i]);
                snprintf(eq->rhs, 64, "%s", rp);
            }
            continue;
        }

        /* 4. `rl [<label>] : <lhs> => <rhs>` or `crl [<label>] : <lhs> => <rhs> if <cond>` */
        bool is_crl = (strncmp(s, "crl ", 4) == 0);
        if (strncmp(s, "rl ", 3) == 0 || is_crl) {
            char label[32] = "rule";
            char *lb = strchr(s, '[');
            char *rb = lb ? strchr(lb, ']') : NULL;
            char *colon = rb ? strchr(rb, ':') : strchr(s, ':');
            if (lb && rb && rb > lb) {
                size_t ll = (size_t)(rb - lb - 1);
                if (ll >= sizeof(label)) ll = sizeof(label) - 1u;
                memcpy(label, lb + 1, ll);
                label[ll] = '\0';
            }
            char *body = colon ? (colon + 1) : (s + (is_crl ? 4 : 3));
            char *if_kw = is_crl ? strstr(body, " if ") : NULL;
            if (if_kw) *if_kw = '\0';
            char *arrow = strstr(body, "=>");
            if (!arrow || me->nrules >= 64) continue;
            *arrow = '\0';
            GoldMaudeRlDecl *r = &me->rules[me->nrules++];
            memset(r, 0, sizeof(*r));
            snprintf(r->label, sizeof(r->label), "%s", label);
            r->nlhs = gold_maude_split_soup_terms(me, body, r->lhs, 4);
            r->nrhs = gold_maude_split_soup_terms(me, arrow + 2, r->rhs, 4);
            if (is_crl && if_kw) {
                r->is_conditional = true;
                char *cond = if_kw + 4;
                char *c_rew = strstr(cond, "=>");
                char *c_eq  = strstr(cond, " = ");
                if (c_rew) {
                    r->cond_is_rew = true;
                    *c_rew = '\0';
                    char cl[1][64] = {{0}}, cr[1][64] = {{0}};
                    if (gold_maude_split_soup_terms(me, cond, cl, 1) > 0)
                        snprintf(r->cond_lhs, 64, "%s", cl[0]);
                    if (gold_maude_split_soup_terms(me, c_rew + 2, cr, 1) > 0)
                        snprintf(r->cond_rhs, 64, "%s", cr[0]);
                } else if (c_eq) {
                    r->cond_is_rew = false;
                    *c_eq = '\0';
                    char cl[1][64] = {{0}}, cr[1][64] = {{0}};
                    if (gold_maude_split_soup_terms(me, cond, cl, 1) > 0)
                        snprintf(r->cond_lhs, 64, "%s", cl[0]);
                    if (gold_maude_split_soup_terms(me, c_eq + 3, cr, 1) > 0)
                        snprintf(r->cond_rhs, 64, "%s", cr[0]);
                }
            }
            continue;
        }
    }
    return (me->nops + me->neqs + me->nrules) > 0;
}

/* Match a pattern token (such as `permission($J,$G)` or `request($J)` or `token`)
 * against a ground token (such as `permission(alpha,open)`), updating variable bindings! */
typedef struct {
    uint32_t nvars;
    char names[8][32];
    char vals[8][64];
} GoldMaudeSubst;

static inline bool gold_maude_bind_var(GoldMaudeSubst *sub, const char *vname, const char *val) {
    for (uint32_t i = 0; i < sub->nvars; i++) {
        if (strcmp(sub->names[i], vname) == 0) {
            return strcmp(sub->vals[i], val) == 0;
        }
    }
    if (sub->nvars >= 8) return false;
    snprintf(sub->names[sub->nvars], 32, "%s", vname);
    snprintf(sub->vals[sub->nvars], 64, "%s", val);
    sub->nvars++;
    return true;
}

static inline void gold_maude_apply_subst(const GoldMaudeSubst *sub, const char *pat, char *out, size_t cap) {
    size_t pos = 0;
    const char *p = pat;
    while (*p && pos + 1 < cap) {
        if (*p == '$') {
            p++;
            char vname[32] = {0};
            size_t vl = 0;
            while ((*p >= 'A' && *p <= 'Z') || (*p >= 'a' && *p <= 'z') || (*p >= '0' && *p <= '9') || *p == '_') {
                if (vl + 1 < sizeof(vname)) vname[vl++] = *p;
                p++;
            }
            const char *bound = vname;
            for (uint32_t i = 0; i < sub->nvars; i++) {
                if (strcmp(sub->names[i], vname) == 0) { bound = sub->vals[i]; break; }
            }
            pos += (size_t)snprintf(out + pos, cap - pos, "%s", bound);
        } else {
            out[pos++] = *p++;
        }
    }
    out[pos] = '\0';
}

static inline bool gold_maude_match_pat_tok(const char *pat, const char *ground, GoldMaudeSubst *sub) {
    if (strchr(pat, '$') == NULL) {
        return strcmp(pat, ground) == 0;
    }
    if (pat[0] == '$' && strchr(pat + 1, '(') == NULL && strchr(pat + 1, ',') == NULL) {
        return gold_maude_bind_var(sub, pat + 1, ground);
    }
    /* Compound pattern `op(a1,a2)` vs `op(g1,g2)` */
    const char *plp = strchr(pat, '(');
    const char *glp = strchr(ground, '(');
    if (!plp || !glp) return false;
    size_t pop_len = (size_t)(plp - pat);
    size_t gop_len = (size_t)(glp - ground);
    if (pop_len != gop_len || strncmp(pat, ground, pop_len) != 0) return false;
    size_t plen = strlen(pat), glen = strlen(ground);
    if (pat[plen - 1] != ')' || ground[glen - 1] != ')') return false;
    char pinner[64] = {0}, ginner[64] = {0};
    memcpy(pinner, plp + 1, plen - pop_len - 2u);
    memcpy(ginner, glp + 1, glen - gop_len - 2u);
    char *pcomma = strchr(pinner, ',');
    char *gcomma = strchr(ginner, ',');
    if ((pcomma != NULL) != (gcomma != NULL)) return false;
    if (!pcomma) {
        return gold_maude_match_pat_tok(pinner, ginner, sub);
    }
    *pcomma = '\0';
    *gcomma = '\0';
    return gold_maude_match_pat_tok(pinner, ginner, sub) &&
           gold_maude_match_pat_tok(pcomma + 1, gcomma + 1, sub);
}

static inline bool gold_maude_match_lhs_recursive(
    const GoldMaudeRlDecl *r,
    uint32_t lhs_idx,
    const GoldMaudeConfig *cfg,
    uint32_t used_mask,
    GoldMaudeSubst *sub,
    uint32_t *out_used_mask)
{
    if (lhs_idx >= r->nlhs || lhs_idx >= 4u) {
        *out_used_mask = used_mask;
        return lhs_idx >= r->nlhs;
    }
    for (uint32_t i = 0; i < cfg->ntokens; i++) {
        if ((used_mask & (1u << i)) != 0u) continue;
        GoldMaudeSubst next_sub = *sub;
        if (gold_maude_match_pat_tok(r->lhs[lhs_idx], cfg->tokens[i], &next_sub)) {
            if (gold_maude_match_lhs_recursive(r, lhs_idx + 1u, cfg, used_mask | (1u << i), &next_sub, out_used_mask)) {
                *sub = next_sub;
                return true;
            }
        }
    }
    return false;
}

/* Rewrite a parsed Maude term string (`rew <term> .`) to normal form over `tcalc`,
 * respecting `[frozen]` / `[frozen (k)]`, ACU equations, and multistep `crl` conditions! */
static inline uint32_t gold_maude_eval_rew_str(
    GoldMaudeEngine *me,
    const char *term_str,
    uint32_t max_steps,
    uint32_t max_cond_steps,
    char *out_buf,
    size_t out_cap)
{
    me->last_refusal = MAUDE_OK;
    /* Check if the entire term is wrapped in a unary operator `op(inner)` (e.g. `sealed(...)` or `group(...)`) */
    char norm_top[128] = {0};
    gold_maude_varify_term(me, term_str, norm_top, sizeof(norm_top));
    gold_maude_normalize_term_str(me, norm_top, sizeof(norm_top));

    const char *lp = strchr(norm_top, '(');
    size_t nlen = strlen(norm_top);
    if (lp && nlen > 0 && norm_top[nlen - 1] == ')') {
        /* Check if '(' matches the final ')' at top level */
        int depth = 0;
        bool single_outer = true;
        for (const char *p = lp; p < norm_top + nlen - 1; p++) {
            if (*p == '(') depth++;
            else if (*p == ')') {
                depth--;
                if (depth == 0) { single_outer = false; break; }
            }
        }
        if (single_outer) {
            char outer_op[32] = {0};
            size_t olen = (size_t)(lp - norm_top);
            if (olen < sizeof(outer_op)) {
                memcpy(outer_op, norm_top, olen);
                uint32_t fmask = gold_maude_lookup_frozen_mask(me, outer_op);
                if ((fmask & 1u) != 0u) {
                    /* Top-level operator is frozen on argument 1: equations normalized, rule rewrites refused! */
                    me->last_refusal = MAUDE_REFUSE_FROZEN_CONTEXT;
                    snprintf(out_buf, out_cap, "%s", norm_top);
                    return 0;
                }
            }
        }
    }

    GoldMaudeConfig cfg;
    memset(&cfg, 0, sizeof(cfg));
    cfg.ntokens = gold_maude_split_soup_terms(NULL, norm_top, cfg.tokens, 32);
    gold_maude_normalize_acu(me, &cfg);

    uint32_t steps = 0;
    while (steps < max_steps) {
        bool fired = false;
        for (uint32_t r_idx = 0; r_idx < me->nrules; r_idx++) {
            const GoldMaudeRlDecl *r = &me->rules[r_idx];
            GoldMaudeSubst sub;
            memset(&sub, 0, sizeof(sub));
            uint32_t used_mask = 0u;
            if (!gold_maude_match_lhs_recursive(r, 0, &cfg, 0u, &sub, &used_mask)) continue;

            if (r->is_conditional) {
                char clhs[64] = {0}, crhs[64] = {0};
                gold_maude_apply_subst(&sub, r->cond_lhs, clhs, sizeof(clhs));
                gold_maude_apply_subst(&sub, r->cond_rhs, crhs, sizeof(crhs));
                if (!r->cond_is_rew) {
                    if (strcmp(clhs, crhs) != 0) continue;
                } else {
                    /* Multistep condition sub-search `clhs =>* crhs` */
                    GoldMaudeConfig sub_cfg;
                    memset(&sub_cfg, 0, sizeof(sub_cfg));
                    gold_maude_add_token(&sub_cfg, clhs);
                    uint32_t csteps = 0;
                    while (csteps < max_cond_steps) {
                        gold_maude_normalize_acu(me, &sub_cfg);
                        if (gold_maude_has_token(&sub_cfg, crhs)) break;
                        csteps++;
                        if (!gold_maude_step_unconditional(me, &sub_cfg)) break;
                    }
                    if (!gold_maude_has_token(&sub_cfg, crhs)) continue;
                    me->crl_subsearches_completed++;
                }
            }

            /* Commit rewrite: remove `used_mask` tokens, add instantiated `r->rhs` tokens */
            GoldMaudeConfig next_cfg;
            memset(&next_cfg, 0, sizeof(next_cfg));
            for (uint32_t i = 0; i < cfg.ntokens; i++) {
                if ((used_mask & (1u << i)) == 0u) {
                    gold_maude_add_token(&next_cfg, cfg.tokens[i]);
                }
            }
            for (uint32_t k = 0; k < r->nrhs; k++) {
                char rinst[64] = {0};
                gold_maude_apply_subst(&sub, r->rhs[k], rinst, sizeof(rinst));
                gold_maude_add_token(&next_cfg, rinst);
            }
            gold_maude_normalize_acu(me, &next_cfg);
            cfg = next_cfg;
            gold_maude_commit_tc_step(me);
            steps++;
            fired = true;
            break;
        }
        if (!fired) break;
    }

    size_t pos = 0;
    if (cfg.ntokens == 0) {
        snprintf(out_buf, out_cap, "empty");
    } else {
        for (uint32_t i = 0; i < cfg.ntokens; i++) {
            if (i > 0) pos += (size_t)snprintf(out_buf + pos, out_cap > pos ? out_cap - pos : 0, " ");
            pos += (size_t)snprintf(out_buf + pos, out_cap > pos ? out_cap - pos : 0, "%s", cfg.tokens[i]);
        }
    }
    return steps;
}

/* =========================================================================
 * PART 5: Joined 5-Language Gold Workflow (Stage 6)
 *   Datalog evidence -> CHR resources -> Maude protocol checks ->
 *   OCaml ranking -> Erlang workers -> MeTTa results, explanations & receipts
 * ========================================================================= */

typedef struct {
    bool all_stages_ok;
    uint32_t dl_demanded_tasks;
    uint32_t dl_explanation_count;
    uint32_t chr_allocated_resources;
    bool maude_protocol_certified;
    char ocaml_ranking_summary[256];
    int64_t erlang_worker_reply_sum;
    char metta_final_report[512];
    uint64_t total_tc_events_admitted;
} GoldJoinedWorkflowReport;

#endif /* GOLD_LANGS_TCALC_H */

#ifndef PETTA_TCALC_EVAL_H
#define PETTA_TCALC_EVAL_H

/*
 * petta_tcalc_eval.h — Route A: Stage-3 Core PeTTa / GSLT Evaluator &
 *                      MeTTa Prime Sub-Calculi Syntactic Sugar Substrate
 *
 * Executes the Stage-3 core of PeTTa programs and GSLT runner/explorer
 * continuations (gslt_runner.metta) over the tcalc kernel and tc_cetta_bridge,
 * covering the core special forms, rewrite dispatch, and 5 sub-calculi:
 *   1. Pattern matching & unification with repeated variables and occurs-check,
 *   2. Lexical binding (let, let*, case, match) with capture-avoiding substitution,
 *   3. Non-deterministic alternatives & exact answer multiplicity (superpose, collapse,
 *      multi-clause rewrite rules),
 *   4. Protected tcalc atomspace effects (add-atom, remove-atom, get-atoms, match)
 *      producing verified TcAdmittedEvent and TcAdmissionReceipt records,
 *   5. Evaluation order, arithmetic/boolean/comparison builtins, and explicit fault propagation,
 *   6. Exact continuation resumption across interrupted/resumed runner & explorer quanta,
 *   7. MeTTa Prime syntactic sugar for 5 restricted tcalc sub-calculi:
 *      - ReadOnlyQuery:     (match &self <pat> <tmpl>)
 *      - MonotoneDatalog:   (infer-atoms! &self (from (<p1> ...)) (where (<g1> ...)) (emit <head>))
 *      - LinearConsumption: (take-atom! &self <pat> <tmpl>) & (replace-atom! &self <old> <new>)
 *      - RefinedCHR:        (simpagate! &self <keep_pat> <rem_pat> <guard> <body>)
 *      - ChannelComm:       (send-chan! &self <ch> <msg>) & (comm! &self <ch> <pat> <body>)
 */

#include "tcalc.h"
#include "bridge/tc_cetta_bridge.h"

#include <ctype.h>
#include <inttypes.h>
#include <math.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define PETTA_SPACE_ATOMS   6
#define PETTA_SPACE_HISTORY 7

typedef enum {
    PETTA_ATOM_SYM  = 0,
    PETTA_ATOM_VAR  = 1,
    PETTA_ATOM_INT  = 2,
    PETTA_ATOM_STR  = 3,
    PETTA_ATOM_EXPR = 4
} PettaAtomKind;

typedef struct PettaAtom {
    PettaAtomKind kind;
    bool has_vars;
    uint32_t refcnt;
    uint32_t nf_epoch;
    uint64_t var_mask;
    char *text;
    int64_t ival;
    uint32_t arity;
    struct PettaAtom **args;
} PettaAtom;

typedef enum {
    PETTA_STATUS_OK               = 0,
    PETTA_STATUS_FAULT            = 1,
    PETTA_STATUS_BUDGET_EXHAUSTED = 2
} PettaStatusKind;

typedef enum {
    PETTA_FAULT_NONE     = 0,
    PETTA_FAULT_DIV_ZERO = 1,
    PETTA_FAULT_TYPE     = 2,
    PETTA_FAULT_UNBOUND  = 3
} PettaFaultKind;

typedef struct {
    char *var;
    PettaAtom *val;
} PettaBind;

typedef struct {
    uint32_t nbinds;
    uint32_t cap_binds;
    PettaBind *binds;
} PettaEnv;

typedef struct {
    uint32_t count;
    uint32_t cap;
    PettaAtom **items;
} PettaValList;

typedef struct {
    bool removed;
    PettaAtom *lhs;
    PettaAtom *rhs;
    uint32_t arity;
    uint32_t head_hash;
    uint32_t next_in_bucket;
} PettaEqRule;

typedef struct {
    bool alive;
    uint32_t id;
    char space[32];
    PettaAtom *atom;
    Term tc_term;
    Occ tc_occ;
} PettaStoreEntry;

typedef struct {
    char rule_name[64];
    uint32_t nkept;
    uint32_t kept_ids[8];
} PettaSimpHist;

typedef struct {
    /* Equation rules (= <lhs> <rhs>) in declaration order (dynamic capacity) */
    uint32_t nrules;
    uint32_t cap_rules;
    PettaEqRule *rules;
    uint64_t rule_head_bloom[4];
    uint32_t rule_bucket_head[256];
    uint32_t rule_bucket_tail[256];
    bool has_sym_rules;
    bool has_var_head_rules;

    /* tcalc-backed Atomspace (&self, dynamic capacity) */
    uint32_t nstore;
    uint32_t cap_store;
    uint32_t next_occ_id;
    PettaStoreEntry *store;

    /* Propagation history for simpagate! sub-calculus (dynamic capacity) */
    uint32_t nhist;
    uint32_t cap_hist;
    PettaSimpHist *hist;

    /* Interned atom table for tc_fresh_name() IDs (dynamic capacity) */
    uint32_t ninterned;
    uint32_t cap_interned;
    PettaAtom **interned_atoms;
    uint64_t *interned_name_ids;

    /* tcalc constructor & rule IDs for store transitions */
    int sort_val;
    int sort_atom;
    int con_atom_box;
    int con_void_sink;
    int rule_add_atom;
    int rule_remove_atom;
    int rule_replace_atom;
    int rule_infer_atom;
    int rule_simpagate_consume;
    int rule_comm_sync;

    TcAdmissionProfile profile_linear;
    TcAdmissionProfile profile_set;

    /* Execution & receipt accounting */
    uint64_t steps_executed;
    uint64_t max_steps;
    uint32_t depth;
    uint32_t max_depth;
    uint64_t tc_events_admitted;
    uint64_t subcalc_queries_run;
    uint64_t subcalc_datalog_inferred;
    uint64_t subcalc_linear_taken;
    uint64_t subcalc_simpagate_fired;
    uint64_t subcalc_comm_synced;

    PettaStatusKind status;
    PettaFaultKind fault;
    TcAdmittedEvent last_event;
    TcAdmissionReceipt last_receipt;

    struct {
        char head[64];
        uint32_t param_count;
        char param_types[8][32];
    } sigs[64];
    uint32_t nsigs;

    bool has_binds;
    bool cut_fired;
    uint32_t var_freshen_seq;
    char cur_dir[512];
    char cur_space[64];
    struct {
        char space[64];
        char path[512];
    } imported_files[64];
    uint32_t nimported_files;
    char translator_rules[16][64];
    uint32_t ntranslator_rules;
} PettaTcalcEngine;

/* =========================================================================
 * 1. PettaAtom Allocation, Cloning, Equality, Hashing & Rendering
 * ========================================================================= */

static inline char *petta_strdup(const char *s) {
    if (!s) s = "";
    size_t n = strlen(s);
    char *p = (char *)malloc(n + 1);
    memcpy(p, s, n + 1);
    return p;
}

static inline uint32_t petta_str_fnv1a(const char *s) {
    uint32_t h = 2166136261u;
    if (s) {
        for (const char *p = s; *p; p++)
            h = (h ^ (uint8_t)*p) * 16777619u;
    }
    return h ? h : 1u;
}

static inline PettaAtom *petta_atom_sym(const char *s) {
    PettaAtom *a = (PettaAtom *)calloc(1, sizeof(PettaAtom));
    a->kind = PETTA_ATOM_SYM;
    a->refcnt = 1u;
    a->text = petta_strdup(s);
    return a;
}

static inline PettaAtom *petta_atom_var(const char *v) {
    PettaAtom *a = (PettaAtom *)calloc(1, sizeof(PettaAtom));
    a->kind = PETTA_ATOM_VAR;
    a->has_vars = true;
    a->refcnt = 1u;
    a->var_mask = 1ULL << (petta_str_fnv1a(v) & 63u);
    a->text = petta_strdup(v);
    return a;
}

static inline PettaAtom *petta_atom_int(int64_t iv) {
    PettaAtom *a = (PettaAtom *)calloc(1, sizeof(PettaAtom));
    a->kind = PETTA_ATOM_INT;
    a->refcnt = 1u;
    a->ival = iv;
    char ibuf[32];
    snprintf(ibuf, sizeof(ibuf), "%" PRId64, iv);
    a->text = petta_strdup(ibuf);
    return a;
}

static inline PettaAtom *petta_atom_str(const char *s) {
    PettaAtom *a = (PettaAtom *)calloc(1, sizeof(PettaAtom));
    a->kind = PETTA_ATOM_STR;
    a->refcnt = 1u;
    a->text = petta_strdup(s);
    return a;
}

static inline PettaAtom *petta_atom_expr(uint32_t arity, PettaAtom **args) {
    PettaAtom *a = (PettaAtom *)calloc(1, sizeof(PettaAtom));
    a->kind = PETTA_ATOM_EXPR;
    a->refcnt = 1u;
    a->text = petta_strdup("");
    a->arity = arity;
    uint64_t vm = 0ULL;
    if (arity > 0) {
        a->args = (PettaAtom **)calloc(arity, sizeof(PettaAtom *));
        for (uint32_t i = 0; i < arity; i++) {
            a->args[i] = args[i];
            if (args[i]) vm |= args[i]->var_mask;
        }
    }
    a->var_mask = vm;
    a->has_vars = (vm != 0ULL);
    return a;
}

static inline void petta_atom_free(PettaAtom *a) {
    if (!a) return;
    if (a->refcnt > 1u) {
        a->refcnt--;
        return;
    }
    if (a->kind == PETTA_ATOM_EXPR) {
        for (uint32_t i = 0; i < a->arity; i++)
            petta_atom_free(a->args[i]);
        free(a->args);
    }
    free(a->text);
    free(a);
}

static inline PettaAtom *petta_atom_clone(const PettaAtom *a) {
    if (!a) return NULL;
    PettaAtom *mut_a = (PettaAtom *)a;
    mut_a->refcnt++;
    return mut_a;
}

static inline void petta_atom_mark_nf(PettaAtom *a, uint32_t epoch) {
    if (!a || a->nf_epoch == epoch) return;
    a->nf_epoch = epoch;
    if (a->kind == PETTA_ATOM_EXPR) {
        if (a->arity >= 1 && a->args[0]->kind == PETTA_ATOM_SYM &&
            (strcmp(a->args[0]->text, "|->") == 0 || strcmp(a->args[0]->text, "quote") == 0))
            return;
        for (uint32_t i = 0; i < a->arity; i++)
            petta_atom_mark_nf(a->args[i], epoch);
    }
}

static inline bool petta_sym_eq(const char *a, const char *b) {
    if (strcmp(a, b) == 0) return true;
    if ((strcmp(a, "True") == 0 || strcmp(a, "true") == 0 || strcmp(a, "Unit") == 0) &&
        (strcmp(b, "True") == 0 || strcmp(b, "true") == 0 || strcmp(b, "Unit") == 0)) return true;
    if ((strcmp(a, "False") == 0 || strcmp(a, "false") == 0) &&
        (strcmp(b, "False") == 0 || strcmp(b, "false") == 0)) return true;
    return false;
}

static inline bool petta_atom_eq(const PettaAtom *a, const PettaAtom *b) {
    if (a == b) return true;
    if (!a || !b || a->kind != b->kind) return false;
    switch (a->kind) {
        case PETTA_ATOM_SYM:
            return petta_sym_eq(a->text, b->text);
        case PETTA_ATOM_VAR:
        case PETTA_ATOM_STR:
            return strcmp(a->text, b->text) == 0;
        case PETTA_ATOM_INT:
            return a->ival == b->ival;
        case PETTA_ATOM_EXPR:
            if (a->arity != b->arity) return false;
            for (uint32_t i = 0; i < a->arity; i++) {
                if (!petta_atom_eq(a->args[i], b->args[i])) return false;
            }
            return true;
    }
    return false;
}

static inline uint32_t petta_atom_hash(const PettaAtom *a) {
    if (!a) return 0u;
    uint32_t h = 2166136261u ^ (uint32_t)a->kind;
    if (a->kind == PETTA_ATOM_INT) {
        uint64_t u = (uint64_t)a->ival;
        h = (h ^ (uint32_t)u) * 16777619u;
        h = (h ^ (uint32_t)(u >> 32)) * 16777619u;
    } else if (a->kind == PETTA_ATOM_EXPR) {
        for (uint32_t i = 0; i < a->arity; i++) {
            h = (h ^ petta_atom_hash(a->args[i])) * 16777619u;
        }
    } else {
        for (const char *p = a->text; *p; p++) {
            h = (h ^ (uint8_t)*p) * 16777619u;
        }
    }
    return h;
}

static inline void petta_atom_render_inner(const PettaAtom *a, char *buf, size_t cap, size_t *pos) {
    if (!a) return;
    if (a->kind == PETTA_ATOM_SYM) {
        *pos += (size_t)snprintf(buf + *pos, cap > *pos ? cap - *pos : 0, "%s", a->text);
    } else if (a->kind == PETTA_ATOM_VAR) {
        *pos += (size_t)snprintf(buf + *pos, cap > *pos ? cap - *pos : 0, "$%s", a->text);
    } else if (a->kind == PETTA_ATOM_INT) {
        *pos += (size_t)snprintf(buf + *pos, cap > *pos ? cap - *pos : 0, "%" PRId64, a->ival);
    } else if (a->kind == PETTA_ATOM_STR) {
        if (*pos + 1 < cap) buf[(*pos)++] = '"';
        for (const char *c = a->text; *c; c++) {
            if (*c == '\\' || *c == '"') {
                if (*pos + 1 < cap) buf[(*pos)++] = '\\';
                if (*pos + 1 < cap) buf[(*pos)++] = *c;
            } else if (*c == '\n') {
                if (*pos + 1 < cap) buf[(*pos)++] = '\\';
                if (*pos + 1 < cap) buf[(*pos)++] = 'n';
            } else if (*c == '\r') {
                if (*pos + 1 < cap) buf[(*pos)++] = '\\';
                if (*pos + 1 < cap) buf[(*pos)++] = 'r';
            } else if (*c == '\t') {
                if (*pos + 1 < cap) buf[(*pos)++] = '\\';
                if (*pos + 1 < cap) buf[(*pos)++] = 't';
            } else {
                if (*pos + 1 < cap) buf[(*pos)++] = *c;
            }
        }
        if (*pos + 1 < cap) buf[(*pos)++] = '"';
        if (*pos < cap) buf[*pos] = '\0';
    } else if (a->kind == PETTA_ATOM_EXPR) {
        *pos += (size_t)snprintf(buf + *pos, cap > *pos ? cap - *pos : 0, "(");
        for (uint32_t i = 0; i < a->arity; i++) {
            if (i > 0) *pos += (size_t)snprintf(buf + *pos, cap > *pos ? cap - *pos : 0, " ");
            petta_atom_render_inner(a->args[i], buf, cap, pos);
        }
        *pos += (size_t)snprintf(buf + *pos, cap > *pos ? cap - *pos : 0, ")");
    }
}

static inline void petta_atom_render(const PettaAtom *a, char *buf, size_t cap) {
    size_t pos = 0;
    if (cap > 0) buf[0] = '\0';
    petta_atom_render_inner(a, buf, cap, &pos);
}

/* =========================================================================
 * 2. S-Expression Parser for PeTTa Programs & Expressions
 * ========================================================================= */

static inline const char *petta_skip_ws(const char *p) {
    while (*p) {
        while (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n') p++;
        if (*p == ';') {
            while (*p && *p != '\n') p++;
            continue;
        }
        break;
    }
    return p;
}

static inline PettaAtom *petta_parse_expr(const char **p) {
    const char *s = petta_skip_ws(*p);
    if (!*s) {
        *p = s;
        return NULL;
    }
    if (*s == '(') {
        s++;
        uint32_t cap = 8u;
        uint32_t arity = 0;
        PettaAtom **args = (PettaAtom **)calloc(cap, sizeof(PettaAtom *));
        bool closed = false;
        while (true) {
            s = petta_skip_ws(s);
            if (!*s) break;
            if (*s == ')') {
                s++;
                closed = true;
                break;
            }
            PettaAtom *child = petta_parse_expr(&s);
            if (!child) break;
            if (arity >= cap) {
                cap *= 2u;
                args = (PettaAtom **)realloc(args, (size_t)cap * sizeof(PettaAtom *));
            }
            args[arity++] = child;
        }
        *p = s;
        if (!closed) {
            for (uint32_t i = 0; i < arity; i++) petta_atom_free(args[i]);
            free(args);
            return NULL;
        }
        PettaAtom *res = petta_atom_expr(arity, args);
        free(args);
        return res;
    }
    if (*s == '"') {
        s++;
        size_t cap = 64, i = 0;
        char *buf = (char *)malloc(cap);
        while (*s && *s != '"') {
            char ch = *s;
            if (ch == '\\' && s[1]) {
                s++;
                if (*s == 'n') ch = '\n';
                else if (*s == 'r') ch = '\r';
                else if (*s == 't') ch = '\t';
                else ch = *s;
            }
            if (i + 1 >= cap) {
                cap *= 2;
                buf = (char *)realloc(buf, cap);
            }
            buf[i++] = ch;
            s++;
        }
        buf[i] = '\0';
        if (*s == '"') s++;
        *p = s;
        PettaAtom *res = petta_atom_str(buf);
        free(buf);
        return res;
    }
    size_t tcap = 64, i = 0;
    char *tok = (char *)malloc(tcap);
    while (*s && *s != ' ' && *s != '\t' && *s != '\r' && *s != '\n' &&
           *s != '(' && *s != ')' && *s != ';') {
        if (i + 1 >= tcap) {
            tcap *= 2;
            tok = (char *)realloc(tok, tcap);
        }
        tok[i++] = *s;
        s++;
    }
    tok[i] = '\0';
    *p = s;
    if (i == 0) {
        free(tok);
        return NULL;
    }
    if (tok[0] == '$' && tok[1] != '\0') {
        PettaAtom *res = petta_atom_var(tok + 1);
        free(tok);
        return res;
    }
    char *endptr = NULL;
    if ((tok[0] >= '0' && tok[0] <= '9') || (tok[0] == '-' && tok[1] >= '0' && tok[1] <= '9')) {
        long long v = strtoll(tok, &endptr, 10);
        if (endptr && *endptr == '\0') {
            free(tok);
            return petta_atom_int((int64_t)v);
        }
    }
    PettaAtom *res = petta_atom_sym(tok);
    free(tok);
    return res;
}

/* =========================================================================
 * 3. Lexical Environment, Pattern Matching, Unification & Capture Avoidance
 * ========================================================================= */

static inline void petta_env_init(PettaEnv *env) {
    memset(env, 0, sizeof(*env));
}

static inline void petta_env_free(PettaEnv *env) {
    if (!env) return;
    for (uint32_t i = 0; i < env->nbinds; i++) {
        free(env->binds[i].var);
        petta_atom_free(env->binds[i].val);
        env->binds[i].var = NULL;
        env->binds[i].val = NULL;
    }
    free(env->binds);
    env->binds = NULL;
    env->nbinds = 0;
    env->cap_binds = 0;
}

static inline PettaEnv petta_env_clone(const PettaEnv *src) {
    PettaEnv dst;
    memset(&dst, 0, sizeof(dst));
    if (src->nbinds > 0) {
        dst.cap_binds = src->nbinds;
        dst.nbinds = src->nbinds;
        dst.binds = (PettaBind *)calloc(src->nbinds, sizeof(PettaBind));
        for (uint32_t i = 0; i < src->nbinds; i++) {
            dst.binds[i].var = petta_strdup(src->binds[i].var);
            dst.binds[i].val = petta_atom_clone(src->binds[i].val);
        }
    }
    return dst;
}

static inline const PettaAtom *petta_env_lookup(const PettaEnv *env, const char *var) {
    /* Search newest binding first to respect lexical shadowing */
    for (int32_t i = (int32_t)env->nbinds - 1; i >= 0; i--) {
        if (strcmp(env->binds[i].var, var) == 0)
            return env->binds[i].val;
    }
    return NULL;
}

static inline void petta_env_bind(PettaEnv *env, const char *var, const PettaAtom *val) {
    if (env->nbinds >= env->cap_binds) {
        uint32_t ncap = env->cap_binds ? env->cap_binds * 2u : 8u;
        env->binds = (PettaBind *)realloc(env->binds, (size_t)ncap * sizeof(PettaBind));
        env->cap_binds = ncap;
    }
    env->binds[env->nbinds].var = petta_strdup(var);
    env->binds[env->nbinds].val = petta_atom_clone(val);
    env->nbinds++;
}

static inline bool petta_var_occurs_in(const char *var, const PettaAtom *term, const PettaEnv *env) {
    if (!term) return false;
    if (term->kind == PETTA_ATOM_VAR) {
        if (strcmp(term->text, var) == 0) return true;
        const PettaAtom *bound = petta_env_lookup(env, term->text);
        if (bound) return petta_var_occurs_in(var, bound, env);
        return false;
    }
    if (term->kind == PETTA_ATOM_EXPR) {
        for (uint32_t i = 0; i < term->arity; i++) {
            if (petta_var_occurs_in(var, term->args[i], env)) return true;
        }
    }
    return false;
}

typedef struct {
    uint32_t count;
    char vars[64][64];
} PettaShadowSet;

static inline void petta_collect_pat_vars(
    const PettaAtom *pat,
    PettaShadowSet *sh)
{
    if (!pat) return;
    if (pat->kind == PETTA_ATOM_VAR) {
        if (strcmp(pat->text, "_") == 0) return;
        for (uint32_t i = 0; i < sh->count; i++) {
            if (strcmp(sh->vars[i], pat->text) == 0) return;
        }
        if (sh->count < 64) {
            snprintf(sh->vars[sh->count++], 64, "%s", pat->text);
        }
        return;
    }
    if (pat->kind == PETTA_ATOM_EXPR) {
        for (uint32_t i = 0; i < pat->arity; i++)
            petta_collect_pat_vars(pat->args[i], sh);
    }
}

/*
 * Pattern match `pat` against `target` within `match_env`.
 * Note: Within a single pattern (such as `(= (same $x $x) True)` or `(case $v ((($a $a) ...)))`),
 * repeated occurrences of `$x` must match equal subterms!
 */
static inline bool petta_match_pattern_inner(
    const PettaAtom *pat,
    const PettaAtom *target,
    PettaEnv *pat_env)
{
    if (!pat || !target) return false;
    if (pat->kind == PETTA_ATOM_VAR) {
        if (strcmp(pat->text, "_") == 0) return true;
        const PettaAtom *existing = petta_env_lookup(pat_env, pat->text);
        if (existing) {
            return petta_atom_eq(existing, target);
        }
        petta_env_bind(pat_env, pat->text, target);
        return true;
    }
    if (pat->kind == PETTA_ATOM_EXPR && pat->arity == 3 &&
        pat->args[0]->kind == PETTA_ATOM_SYM && strcmp(pat->args[0]->text, "@") == 0) {
        return petta_match_pattern_inner(pat->args[1], target, pat_env) &&
               petta_match_pattern_inner(pat->args[2], target, pat_env);
    }
    if (pat->kind == PETTA_ATOM_EXPR && pat->arity == 3 &&
        pat->args[0]->kind == PETTA_ATOM_SYM && target->kind == PETTA_ATOM_INT) {
        const char *pop = pat->args[0]->text;
        if (strcmp(pop, "+") == 0 || strcmp(pop, "#+") == 0) {
            if (pat->args[2]->kind == PETTA_ATOM_INT) {
                PettaAtom *diff = petta_atom_int(target->ival - pat->args[2]->ival);
                bool ok = petta_match_pattern_inner(pat->args[1], diff, pat_env);
                petta_atom_free(diff);
                return ok;
            }
            if (pat->args[1]->kind == PETTA_ATOM_INT) {
                PettaAtom *diff = petta_atom_int(target->ival - pat->args[1]->ival);
                bool ok = petta_match_pattern_inner(pat->args[2], diff, pat_env);
                petta_atom_free(diff);
                return ok;
            }
        } else if (strcmp(pop, "-") == 0 || strcmp(pop, "#-") == 0) {
            if (pat->args[2]->kind == PETTA_ATOM_INT) {
                PettaAtom *sum = petta_atom_int(target->ival + pat->args[2]->ival);
                bool ok = petta_match_pattern_inner(pat->args[1], sum, pat_env);
                petta_atom_free(sum);
                return ok;
            }
            if (pat->args[1]->kind == PETTA_ATOM_INT) {
                PettaAtom *diff = petta_atom_int(pat->args[1]->ival - target->ival);
                bool ok = petta_match_pattern_inner(pat->args[2], diff, pat_env);
                petta_atom_free(diff);
                return ok;
            }
        }
    }
    if (target->kind == PETTA_ATOM_VAR && !pat->has_vars) {
        if (strcmp(target->text, "_") == 0) return true;
        const PettaAtom *existing = petta_env_lookup(pat_env, target->text);
        if (existing) {
            return petta_atom_eq(existing, pat);
        }
        petta_env_bind(pat_env, target->text, pat);
        return true;
    }
    if (pat->kind != target->kind) return false;
    switch (pat->kind) {
        case PETTA_ATOM_SYM:
            return petta_sym_eq(pat->text, target->text);
        case PETTA_ATOM_STR:
            return strcmp(pat->text, target->text) == 0;
        case PETTA_ATOM_INT:
            return pat->ival == target->ival;
        case PETTA_ATOM_EXPR:
            if (pat->arity == 3 && pat->args[0]->kind == PETTA_ATOM_SYM &&
                strcmp(pat->args[0]->text, "cons") == 0 &&
                !(target->arity == 3 && target->args[0]->kind == PETTA_ATOM_SYM &&
                  strcmp(target->args[0]->text, "cons") == 0)) {
                if (target->arity == 0) return false;
                if (!petta_match_pattern_inner(pat->args[1], target->args[0], pat_env))
                    return false;
                uint32_t tail_len = target->arity - 1u;
                PettaAtom **targs = tail_len ? (PettaAtom **)calloc(tail_len, sizeof(PettaAtom *)) : NULL;
                for (uint32_t k = 0; k < tail_len; k++)
                    targs[k] = petta_atom_clone(target->args[k + 1u]);
                PettaAtom *tail_atom = petta_atom_expr(tail_len, targs);
                free(targs);
                bool ok_t = petta_match_pattern_inner(pat->args[2], tail_atom, pat_env);
                petta_atom_free(tail_atom);
                return ok_t;
            }
            if (pat->arity == 3 && pat->args[0]->kind == PETTA_ATOM_SYM &&
                (strcmp(pat->args[0]->text, "append") == 0 || strcmp(pat->args[0]->text, "union-atom") == 0) &&
                !(target->arity == 3 && target->args[0]->kind == PETTA_ATOM_SYM &&
                  (strcmp(target->args[0]->text, "append") == 0 || strcmp(target->args[0]->text, "union-atom") == 0))) {
                if (pat->args[1]->kind == PETTA_ATOM_EXPR && pat->args[1]->arity <= target->arity) {
                    uint32_t plen = pat->args[1]->arity;
                    for (uint32_t k = 0; k < plen; k++) {
                        if (!petta_match_pattern_inner(pat->args[1]->args[k], target->args[k], pat_env))
                            return false;
                    }
                    uint32_t slen = target->arity - plen;
                    PettaAtom **sargs = slen ? (PettaAtom **)calloc(slen, sizeof(PettaAtom *)) : NULL;
                    for (uint32_t k = 0; k < slen; k++)
                        sargs[k] = petta_atom_clone(target->args[plen + k]);
                    PettaAtom *suf = petta_atom_expr(slen, sargs);
                    free(sargs);
                    bool ok_s = petta_match_pattern_inner(pat->args[2], suf, pat_env);
                    petta_atom_free(suf);
                    return ok_s;
                }
                if (pat->args[2]->kind == PETTA_ATOM_EXPR && pat->args[2]->arity <= target->arity) {
                    uint32_t slen = pat->args[2]->arity;
                    uint32_t plen = target->arity - slen;
                    for (uint32_t k = 0; k < slen; k++) {
                        if (!petta_match_pattern_inner(pat->args[2]->args[k], target->args[plen + k], pat_env))
                            return false;
                    }
                    PettaAtom **pargs = plen ? (PettaAtom **)calloc(plen, sizeof(PettaAtom *)) : NULL;
                    for (uint32_t k = 0; k < plen; k++)
                        pargs[k] = petta_atom_clone(target->args[k]);
                    PettaAtom *pre = petta_atom_expr(plen, pargs);
                    free(pargs);
                    bool ok_p = petta_match_pattern_inner(pat->args[1], pre, pat_env);
                    petta_atom_free(pre);
                    return ok_p;
                }
                return false;
            }
            if (pat->arity != target->arity) return false;
            /* Fast fail on concrete symbol/kind heads before cloning large variable bindings */
            for (uint32_t i = 0; i < pat->arity; i++) {
                if (pat->args[i]->kind != PETTA_ATOM_VAR) {
                    if (target->args[i]->kind == PETTA_ATOM_VAR && !pat->args[i]->has_vars)
                        continue;
                    if (pat->args[i]->kind == PETTA_ATOM_EXPR && pat->args[i]->arity == 3 &&
                        pat->args[i]->args[0]->kind == PETTA_ATOM_SYM &&
                        (strcmp(pat->args[i]->args[0]->text, "@") == 0 ||
                         strcmp(pat->args[i]->args[0]->text, "cons") == 0 ||
                         strcmp(pat->args[i]->args[0]->text, "append") == 0 ||
                         strcmp(pat->args[i]->args[0]->text, "union-atom") == 0 ||
                         strcmp(pat->args[i]->args[0]->text, "+") == 0 ||
                         strcmp(pat->args[i]->args[0]->text, "#+") == 0 ||
                         strcmp(pat->args[i]->args[0]->text, "-") == 0 ||
                         strcmp(pat->args[i]->args[0]->text, "#-") == 0))
                        continue;
                    if (pat->args[i]->kind != target->args[i]->kind) return false;
                    if (pat->args[i]->kind == PETTA_ATOM_SYM &&
                        !petta_sym_eq(pat->args[i]->text, target->args[i]->text))
                        return false;
                }
            }
            for (uint32_t i = 0; i < pat->arity; i++) {
                if (pat->args[i]->kind != PETTA_ATOM_VAR) {
                    if (!petta_match_pattern_inner(pat->args[i], target->args[i], pat_env))
                        return false;
                }
            }
            for (uint32_t i = 0; i < pat->arity; i++) {
                if (pat->args[i]->kind == PETTA_ATOM_VAR) {
                    if (!petta_match_pattern_inner(pat->args[i], target->args[i], pat_env))
                        return false;
                }
            }
            return true;
        default:
            return false;
    }
}

static inline bool petta_match_pattern(
    const PettaAtom *pat,
    const PettaAtom *target,
    PettaEnv *out_pat_env)
{
    PettaEnv tmp;
    petta_env_init(&tmp);
    if (!petta_match_pattern_inner(pat, target, &tmp)) {
        petta_env_free(&tmp);
        return false;
    }
    *out_pat_env = tmp;
    return true;
}

static inline bool petta_atom_alpha_eq_inner(
    const PettaAtom *a,
    const PettaAtom *b,
    PettaEnv *a2b,
    PettaEnv *b2a)
{
    if (a == b) return true;
    if (!a || !b || a->kind != b->kind) return false;
    switch (a->kind) {
        case PETTA_ATOM_SYM:
            return petta_sym_eq(a->text, b->text);
        case PETTA_ATOM_STR:
            return strcmp(a->text, b->text) == 0;
        case PETTA_ATOM_INT:
            return a->ival == b->ival;
        case PETTA_ATOM_VAR: {
            const PettaAtom *ma = petta_env_lookup(a2b, a->text);
            const PettaAtom *mb = petta_env_lookup(b2a, b->text);
            if (ma && mb) {
                return strcmp(ma->text, b->text) == 0 && strcmp(mb->text, a->text) == 0;
            }
            if (!ma && !mb) {
                petta_env_bind(a2b, a->text, b);
                petta_env_bind(b2a, b->text, a);
                return true;
            }
            return false;
        }
        case PETTA_ATOM_EXPR:
            if (a->arity != b->arity) return false;
            for (uint32_t i = 0; i < a->arity; i++) {
                if (!petta_atom_alpha_eq_inner(a->args[i], b->args[i], a2b, b2a))
                    return false;
            }
            return true;
    }
    return false;
}

static inline bool petta_atom_alpha_eq(const PettaAtom *a, const PettaAtom *b) {
    if (a == b) return true;
    if (!a || !b) return false;
    if (!a->has_vars && !b->has_vars) return petta_atom_eq(a, b);
    PettaEnv a2b, b2a;
    petta_env_init(&a2b);
    petta_env_init(&b2a);
    bool ok = petta_atom_alpha_eq_inner(a, b, &a2b, &b2a);
    petta_env_free(&a2b);
    petta_env_free(&b2a);
    return ok;
}

/* Two-way first-order unification with occurs-check */
static inline bool petta_unify_atoms(
    const PettaAtom *a,
    const PettaAtom *b,
    PettaEnv *env)
{
    if (!a || !b) return false;
    if (a->kind == PETTA_ATOM_VAR && strcmp(a->text, "_") != 0) {
        const PettaAtom *ab = petta_env_lookup(env, a->text);
        if (ab) return petta_unify_atoms(ab, b, env);
    }
    if (b->kind == PETTA_ATOM_VAR && strcmp(b->text, "_") != 0) {
        const PettaAtom *bb = petta_env_lookup(env, b->text);
        if (bb) return petta_unify_atoms(a, bb, env);
    }
    if (a->kind == PETTA_ATOM_VAR) {
        if (strcmp(a->text, "_") == 0) return true;
        if (b->kind == PETTA_ATOM_VAR && strcmp(a->text, b->text) == 0) return true;
        if (petta_var_occurs_in(a->text, b, env)) return false;
        petta_env_bind(env, a->text, b);
        return true;
    }
    if (b->kind == PETTA_ATOM_VAR) {
        if (strcmp(b->text, "_") == 0) return true;
        if (petta_var_occurs_in(b->text, a, env)) return false;
        petta_env_bind(env, b->text, a);
        return true;
    }
    if (a->kind != b->kind) return false;
    if (a->kind == PETTA_ATOM_INT) return a->ival == b->ival;
    if (a->kind == PETTA_ATOM_SYM) return petta_sym_eq(a->text, b->text);
    if (a->kind == PETTA_ATOM_STR) return strcmp(a->text, b->text) == 0;
    if (a->kind == PETTA_ATOM_EXPR) {
        const PettaAtom *cons_side = NULL, *list_side = NULL;
        if (a->arity == 3 && a->args[0]->kind == PETTA_ATOM_SYM && strcmp(a->args[0]->text, "cons") == 0 &&
            !(b->arity == 3 && b->args[0]->kind == PETTA_ATOM_SYM && strcmp(b->args[0]->text, "cons") == 0)) {
            cons_side = a; list_side = b;
        } else if (b->arity == 3 && b->args[0]->kind == PETTA_ATOM_SYM && strcmp(b->args[0]->text, "cons") == 0 &&
                   !(a->arity == 3 && a->args[0]->kind == PETTA_ATOM_SYM && strcmp(a->args[0]->text, "cons") == 0)) {
            cons_side = b; list_side = a;
        }
        if (cons_side) {
            if (list_side->arity == 0) return false;
            if (!petta_unify_atoms(cons_side->args[1], list_side->args[0], env)) return false;
            uint32_t tlen = list_side->arity - 1u;
            PettaAtom **targs = tlen ? (PettaAtom **)calloc(tlen, sizeof(PettaAtom *)) : NULL;
            for (uint32_t k = 0; k < tlen; k++) targs[k] = petta_atom_clone(list_side->args[k + 1u]);
            PettaAtom *tail_a = petta_atom_expr(tlen, targs);
            free(targs);
            bool ok = petta_unify_atoms(cons_side->args[2], tail_a, env);
            petta_atom_free(tail_a);
            return ok;
        }
        const PettaAtom *app_side = NULL, *tup_side = NULL;
        if (a->arity == 3 && a->args[0]->kind == PETTA_ATOM_SYM &&
            (strcmp(a->args[0]->text, "append") == 0 || strcmp(a->args[0]->text, "union-atom") == 0) &&
            !(b->arity == 3 && b->args[0]->kind == PETTA_ATOM_SYM &&
              (strcmp(b->args[0]->text, "append") == 0 || strcmp(b->args[0]->text, "union-atom") == 0))) {
            app_side = a; tup_side = b;
        } else if (b->arity == 3 && b->args[0]->kind == PETTA_ATOM_SYM &&
                   (strcmp(b->args[0]->text, "append") == 0 || strcmp(b->args[0]->text, "union-atom") == 0) &&
                   !(a->arity == 3 && a->args[0]->kind == PETTA_ATOM_SYM &&
                     (strcmp(a->args[0]->text, "append") == 0 || strcmp(a->args[0]->text, "union-atom") == 0))) {
            app_side = b; tup_side = a;
        }
        if (app_side) {
            if (app_side->args[1]->kind == PETTA_ATOM_EXPR && app_side->args[1]->arity <= tup_side->arity) {
                uint32_t plen = app_side->args[1]->arity;
                for (uint32_t k = 0; k < plen; k++) {
                    if (!petta_unify_atoms(app_side->args[1]->args[k], tup_side->args[k], env)) return false;
                }
                uint32_t slen = tup_side->arity - plen;
                PettaAtom **sargs = slen ? (PettaAtom **)calloc(slen, sizeof(PettaAtom *)) : NULL;
                for (uint32_t k = 0; k < slen; k++) sargs[k] = petta_atom_clone(tup_side->args[plen + k]);
                PettaAtom *suf = petta_atom_expr(slen, sargs);
                free(sargs);
                bool ok = petta_unify_atoms(app_side->args[2], suf, env);
                petta_atom_free(suf);
                return ok;
            }
            if (app_side->args[2]->kind == PETTA_ATOM_EXPR && app_side->args[2]->arity <= tup_side->arity) {
                uint32_t slen = app_side->args[2]->arity;
                uint32_t plen = tup_side->arity - slen;
                for (uint32_t k = 0; k < slen; k++) {
                    if (!petta_unify_atoms(app_side->args[2]->args[k], tup_side->args[plen + k], env)) return false;
                }
                PettaAtom **pargs = plen ? (PettaAtom **)calloc(plen, sizeof(PettaAtom *)) : NULL;
                for (uint32_t k = 0; k < plen; k++) pargs[k] = petta_atom_clone(tup_side->args[k]);
                PettaAtom *pre = petta_atom_expr(plen, pargs);
                free(pargs);
                bool ok = petta_unify_atoms(app_side->args[1], pre, env);
                petta_atom_free(pre);
                return ok;
            }
            return false;
        }
        if (a->arity != b->arity) return false;
        for (uint32_t i = 0; i < a->arity; i++) {
            if (!petta_unify_atoms(a->args[i], b->args[i], env))
                return false;
        }
        return true;
    }
    return false;
}

static inline bool petta_unify_pattern(
    const PettaAtom *a,
    const PettaAtom *b,
    PettaEnv *out_env)
{
    PettaEnv tmp;
    petta_env_init(&tmp);
    if (!petta_unify_atoms(a, b, &tmp)) {
        petta_env_free(&tmp);
        return false;
    }
    *out_env = tmp;
    return true;
}

static inline PettaAtom *petta_freshen_vars(const PettaAtom *a, uint32_t seq) {
    if (!a || !a->has_vars) return petta_atom_clone(a);
    if (a->kind == PETTA_ATOM_VAR) {
        if (strcmp(a->text, "_") == 0) return petta_atom_clone(a);
        char vbuf[128];
        snprintf(vbuf, sizeof(vbuf), "%s__%u", a->text, seq);
        return petta_atom_var(vbuf);
    }
    if (a->kind == PETTA_ATOM_EXPR) {
        PettaAtom **nargs = a->arity ? (PettaAtom **)calloc(a->arity, sizeof(PettaAtom *)) : NULL;
        for (uint32_t i = 0; i < a->arity; i++)
            nargs[i] = petta_freshen_vars(a->args[i], seq);
        PettaAtom *res = petta_atom_expr(a->arity, nargs);
        free(nargs);
        return res;
    }
    return petta_atom_clone(a);
}

static inline void petta_collect_pat_vars_unshadowed(
    const PettaAtom *pat,
    const PettaEnv *env,
    PettaShadowSet *sh)
{
    if (!pat) return;
    if (pat->kind == PETTA_ATOM_VAR) {
        if (strcmp(pat->text, "_") == 0) return;
        if (petta_env_lookup(env, pat->text) != NULL) return;
        for (uint32_t i = 0; i < sh->count; i++) {
            if (strcmp(sh->vars[i], pat->text) == 0) return;
        }
        if (sh->count < 64) {
            snprintf(sh->vars[sh->count++], 64, "%s", pat->text);
        }
        return;
    }
    if (pat->kind == PETTA_ATOM_EXPR) {
        for (uint32_t i = 0; i < pat->arity; i++)
            petta_collect_pat_vars_unshadowed(pat->args[i], env, sh);
    }
}

/*
 * Capture-avoiding substitution of `env` into `expr`, respecting lexical shadowing
 * in `(let $pat $val $body)`, `(let* ((...)) $body)`, and `(case $scrut ((($pat $body) ...)))`.
 */
static inline PettaAtom *petta_subst_env_shadowed(
    const PettaAtom *expr,
    const PettaEnv *env,
    uint64_t env_mask,
    PettaShadowSet *sh)
{
    if (!expr) return NULL;
    if ((expr->var_mask & env_mask) == 0ULL) return petta_atom_clone(expr);
    if (expr->kind == PETTA_ATOM_VAR) {
        for (uint32_t s = 0; s < sh->count; s++) {
            if (strcmp(sh->vars[s], expr->text) == 0)
                return petta_atom_clone(expr);
        }
        const PettaAtom *bound = petta_env_lookup(env, expr->text);
        if (bound) {
            return petta_atom_clone(bound);
        }
        return petta_atom_clone(expr);
    }
    if (expr->kind != PETTA_ATOM_EXPR) {
        return petta_atom_clone(expr);
    }
    /* Handle lexical binding forms to prevent variable capture / shadowing leaks */
    if (expr->arity == 4 && expr->args[0]->kind == PETTA_ATOM_SYM &&
        (strcmp(expr->args[0]->text, "let") == 0 || strcmp(expr->args[0]->text, "chain") == 0)) {
        bool is_chain_order = (strcmp(expr->args[0]->text, "chain") == 0 &&
                               expr->args[2]->kind == PETTA_ATOM_VAR &&
                               expr->args[1]->kind != PETTA_ATOM_VAR);
        uint32_t pat_idx = is_chain_order ? 2u : 1u;
        uint32_t val_idx = is_chain_order ? 1u : 2u;
        PettaAtom *new_args[4];
        new_args[0] = petta_atom_clone(expr->args[0]);
        new_args[val_idx] = petta_subst_env_shadowed(expr->args[val_idx], env, env_mask, sh);
        uint32_t saved_count = sh->count;
        const PettaAtom *pat_a = expr->args[pat_idx];
        if (pat_a->kind == PETTA_ATOM_VAR) {
            const PettaAtom *pb = petta_env_lookup(env, pat_a->text);
            if (pb && pb->has_vars) {
                new_args[pat_idx] = petta_atom_clone(pb);
                petta_collect_pat_vars_unshadowed(pb, env, sh);
            } else {
                new_args[pat_idx] = petta_atom_clone(pat_a);
                petta_collect_pat_vars(pat_a, sh);
            }
        } else {
            new_args[pat_idx] = petta_subst_env_shadowed(pat_a, env, env_mask, sh);
            petta_collect_pat_vars_unshadowed(pat_a, env, sh);
        }
        new_args[3] = petta_subst_env_shadowed(expr->args[3], env, env_mask, sh);
        sh->count = saved_count;
        return petta_atom_expr(4, new_args);
    }
    if (expr->arity == 6 && expr->args[0]->kind == PETTA_ATOM_SYM &&
        strcmp(expr->args[0]->text, "foldl-atom") == 0) {
        PettaAtom *new_args[6];
        new_args[0] = petta_atom_clone(expr->args[0]);
        new_args[1] = petta_subst_env_shadowed(expr->args[1], env, env_mask, sh);
        new_args[2] = petta_subst_env_shadowed(expr->args[2], env, env_mask, sh);
        new_args[3] = petta_atom_clone(expr->args[3]);
        new_args[4] = petta_atom_clone(expr->args[4]);
        uint32_t saved_count = sh->count;
        petta_collect_pat_vars(expr->args[3], sh);
        petta_collect_pat_vars(expr->args[4], sh);
        new_args[5] = petta_subst_env_shadowed(expr->args[5], env, env_mask, sh);
        sh->count = saved_count;
        return petta_atom_expr(6, new_args);
    }
    if (expr->arity == 4 && expr->args[0]->kind == PETTA_ATOM_SYM &&
        (strcmp(expr->args[0]->text, "map-atom") == 0 ||
         strcmp(expr->args[0]->text, "filter-atom") == 0)) {
        PettaAtom *new_args[4];
        new_args[0] = petta_atom_clone(expr->args[0]);
        new_args[1] = petta_subst_env_shadowed(expr->args[1], env, env_mask, sh);
        new_args[2] = petta_atom_clone(expr->args[2]);
        uint32_t saved_count = sh->count;
        petta_collect_pat_vars(expr->args[2], sh);
        new_args[3] = petta_subst_env_shadowed(expr->args[3], env, env_mask, sh);
        sh->count = saved_count;
        return petta_atom_expr(4, new_args);
    }
    if (expr->arity == 3 && expr->args[0]->kind == PETTA_ATOM_SYM &&
        strcmp(expr->args[0]->text, "|->") == 0 &&
        expr->args[1]->kind == PETTA_ATOM_EXPR) {
        PettaAtom *new_args[3];
        new_args[0] = petta_atom_clone(expr->args[0]);
        new_args[1] = petta_atom_clone(expr->args[1]);
        uint32_t saved_count = sh->count;
        petta_collect_pat_vars(expr->args[1], sh);
        new_args[2] = petta_subst_env_shadowed(expr->args[2], env, env_mask, sh);
        sh->count = saved_count;
        return petta_atom_expr(3, new_args);
    }
    if (expr->arity == 3 && expr->args[0]->kind == PETTA_ATOM_SYM &&
        strcmp(expr->args[0]->text, "let*") == 0 &&
        expr->args[1]->kind == PETTA_ATOM_EXPR) {
        PettaAtom *new_args[3];
        new_args[0] = petta_atom_clone(expr->args[0]);
        uint32_t saved_count = sh->count;
        PettaAtom *bind_list = expr->args[1];
        PettaAtom **new_binds = bind_list->arity ? (PettaAtom **)calloc(bind_list->arity, sizeof(PettaAtom *)) : NULL;
        for (uint32_t b = 0; b < bind_list->arity; b++) {
            PettaAtom *pair = bind_list->args[b];
            if (pair->kind == PETTA_ATOM_EXPR && pair->arity == 2) {
                PettaAtom *np[2];
                np[1] = petta_subst_env_shadowed(pair->args[1], env, env_mask, sh);
                if (pair->args[0]->kind == PETTA_ATOM_VAR) {
                    const PettaAtom *pb = petta_env_lookup(env, pair->args[0]->text);
                    if (pb && pb->has_vars) {
                        np[0] = petta_atom_clone(pb);
                        petta_collect_pat_vars_unshadowed(pb, env, sh);
                    } else {
                        np[0] = petta_atom_clone(pair->args[0]);
                        petta_collect_pat_vars(pair->args[0], sh);
                    }
                } else {
                    np[0] = petta_subst_env_shadowed(pair->args[0], env, env_mask, sh);
                    petta_collect_pat_vars_unshadowed(pair->args[0], env, sh);
                }
                new_binds[b] = petta_atom_expr(2, np);
            } else {
                new_binds[b] = petta_subst_env_shadowed(pair, env, env_mask, sh);
            }
        }
        new_args[1] = petta_atom_expr(bind_list->arity, new_binds);
        free(new_binds);
        new_args[2] = petta_subst_env_shadowed(expr->args[2], env, env_mask, sh);
        sh->count = saved_count;
        return petta_atom_expr(3, new_args);
    }
    if (expr->arity == 3 && expr->args[0]->kind == PETTA_ATOM_SYM &&
        strcmp(expr->args[0]->text, "case") == 0 &&
        expr->args[2]->kind == PETTA_ATOM_EXPR) {
        PettaAtom *new_args[3];
        new_args[0] = petta_atom_clone(expr->args[0]);
        new_args[1] = petta_subst_env_shadowed(expr->args[1], env, env_mask, sh);
        PettaAtom *branches = expr->args[2];
        PettaAtom **new_br = branches->arity ? (PettaAtom **)calloc(branches->arity, sizeof(PettaAtom *)) : NULL;
        for (uint32_t b = 0; b < branches->arity; b++) {
            PettaAtom *br = branches->args[b];
            if (br->kind == PETTA_ATOM_EXPR && br->arity == 2) {
                uint32_t saved_count = sh->count;
                PettaAtom *nb[2];
                if (br->args[0]->kind == PETTA_ATOM_VAR) {
                    const PettaAtom *pb = petta_env_lookup(env, br->args[0]->text);
                    if (pb) {
                        nb[0] = petta_atom_clone(pb);
                    } else {
                        nb[0] = petta_atom_clone(br->args[0]);
                        petta_collect_pat_vars(br->args[0], sh);
                    }
                } else {
                    nb[0] = petta_subst_env_shadowed(br->args[0], env, env_mask, sh);
                    petta_collect_pat_vars_unshadowed(br->args[0], env, sh);
                }
                nb[1] = petta_subst_env_shadowed(br->args[1], env, env_mask, sh);
                sh->count = saved_count;
                new_br[b] = petta_atom_expr(2, nb);
            } else {
                new_br[b] = petta_subst_env_shadowed(br, env, env_mask, sh);
            }
        }
        new_args[2] = petta_atom_expr(branches->arity, new_br);
        free(new_br);
        return petta_atom_expr(3, new_args);
    }

    PettaAtom *local_args[16];
    PettaAtom **new_args = (expr->arity <= 16u)
        ? local_args
        : (PettaAtom **)calloc(expr->arity, sizeof(PettaAtom *));
    bool changed = false;
    for (uint32_t i = 0; i < expr->arity; i++) {
        new_args[i] = petta_subst_env_shadowed(expr->args[i], env, env_mask, sh);
        if (new_args[i] != expr->args[i]) changed = true;
    }
    if (!changed) {
        for (uint32_t i = 0; i < expr->arity; i++)
            petta_atom_free(new_args[i]);
        if (expr->arity > 16u) free(new_args);
        return petta_atom_clone(expr);
    }
    PettaAtom *res = petta_atom_expr(expr->arity, new_args);
    if (expr->arity > 16u) free(new_args);
    return res;
}

static __attribute__((noinline)) PettaAtom *petta_subst_env(const PettaAtom *expr, const PettaEnv *env) {
    if (!expr) return NULL;
    if (!expr->has_vars || !env || env->nbinds == 0) return petta_atom_clone(expr);
    uint64_t env_mask = 0ULL;
    for (uint32_t i = 0; i < env->nbinds; i++) {
        env_mask |= (1ULL << (petta_str_fnv1a(env->binds[i].var) & 63u));
    }
    if ((expr->var_mask & env_mask) == 0ULL) return petta_atom_clone(expr);
    PettaShadowSet sh;
    sh.count = 0;
    return petta_subst_env_shadowed(expr, env, env_mask, &sh);
}

static inline PettaAtom *petta_subst_env_trans(const PettaAtom *expr, const PettaEnv *env) {
    PettaAtom *cur = petta_subst_env(expr, env);
    for (uint32_t step = 0; step < 8u && cur && cur->has_vars; step++) {
        PettaAtom *next = petta_subst_env(cur, env);
        bool same = petta_atom_eq(cur, next);
        petta_atom_free(cur);
        cur = next;
        if (same) break;
    }
    return cur;
}

/* =========================================================================
 * 4. tcalc Kernel Initialization & Protected Atomspace Operations
 * ========================================================================= */

static inline void petta_tcalc_engine_init(PettaTcalcEngine *eng, uint64_t max_steps) {
    memset(eng, 0, sizeof(*eng));
    eng->max_steps = max_steps;
    eng->max_depth = 512u;
    eng->next_occ_id = 1u;

    tc_init(1u << 19, 1u << 18);
    tc_protect(PETTA_SPACE_ATOMS);
    tc_protect(PETTA_SPACE_HISTORY);

    eng->sort_val = tc_sort(SORT_PURE | SORT_STRICT);
    eng->sort_atom = tc_sort(SORT_STRICT | SORT_PROVABLE);
    Binder b1 = { .sort = (uint16_t)eng->sort_val, .bound = 0, .deps = 0 };
    eng->con_atom_box = tc_con((uint16_t)eng->sort_atom, 0, 1, &b1);
    eng->con_void_sink = tc_con((uint16_t)eng->sort_atom, 0, 0, NULL);

    Binder ctx1[1] = { b1 };
    Binder ctx2[2] = { b1, b1 };
    Binder ctx3[3] = { b1, b1, b1 };

    /* Rule 1: add-atom (make 1 occurrence in PETTA_SPACE_ATOMS) */
    {
        tc_ctx(1, ctx1);
        Term v0 = tc_v(0);
        Rule r;
        memset(&r, 0, sizeof(r));
        r.fresh = -1;
        r.inputs = 0x1;   /* the atom the host adds */
        r.make = (Pat){ .t = tc_app(eng->con_atom_box, &v0), .space = PETTA_SPACE_ATOMS };
        eng->rule_add_atom = tc_rule(&r);
    }
    /* Rule 2: remove-atom (linear take 1 occurrence in PETTA_SPACE_ATOMS, make sink in HISTORY) */
    {
        tc_ctx(1, ctx1);
        Term v0 = tc_v(0);
        Rule r;
        memset(&r, 0, sizeof(r));
        r.fresh = -1;
        r.ntake = 1;
        r.take[0] = (Pat){ .t = tc_app(eng->con_atom_box, &v0), .space = PETTA_SPACE_ATOMS };
        r.make = (Pat){ .t = tc_app(eng->con_void_sink, NULL), .space = PETTA_SPACE_HISTORY };
        eng->rule_remove_atom = tc_rule(&r);
    }
    /* Rule 3: replace-atom! (linear take 1 old, make 1 new in PETTA_SPACE_ATOMS) */
    {
        tc_ctx(2, ctx2);
        Term v0 = tc_v(0);
        Term v1 = tc_v(1);
        Rule r;
        memset(&r, 0, sizeof(r));
        r.fresh = -1;
        r.inputs = 0x2;   /* the replacing atom */
        r.ntake = 1;
        r.take[0] = (Pat){ .t = tc_app(eng->con_atom_box, &v0), .space = PETTA_SPACE_ATOMS };
        r.make = (Pat){ .t = tc_app(eng->con_atom_box, &v1), .space = PETTA_SPACE_ATOMS };
        eng->rule_replace_atom = tc_rule(&r);
    }
    /* Rule 4: infer-atoms! (keep 1 premise, make 1 derived atom with absent guard) */
    {
        tc_ctx(2, ctx2);
        Term v0 = tc_v(0);
        Term v1 = tc_v(1);
        Rule r;
        memset(&r, 0, sizeof(r));
        r.fresh = -1;
        r.inputs = 0x2;   /* the inferred atom */
        r.nkeep = 1;
        r.keep[0] = (Pat){ .t = tc_app(eng->con_atom_box, &v0), .space = PETTA_SPACE_ATOMS };
        r.make = (Pat){ .t = tc_app(eng->con_atom_box, &v1), .space = PETTA_SPACE_ATOMS };
        r.nabsent = 1;
        r.absent[0] = (Pat){ .t = tc_app(eng->con_atom_box, &v1), .space = PETTA_SPACE_ATOMS };
        eng->rule_infer_atom = tc_rule(&r);
    }
    /* Rule 5: simpagate! (keep 1, take 1, make 1 in PETTA_SPACE_ATOMS) */
    {
        tc_ctx(3, ctx3);
        Term v0 = tc_v(0);
        Term v1 = tc_v(1);
        Term v2 = tc_v(2);
        Rule r;
        memset(&r, 0, sizeof(r));
        r.fresh = -1;
        r.inputs = 0x4;   /* the atom made */
        r.nkeep = 1;
        r.keep[0] = (Pat){ .t = tc_app(eng->con_atom_box, &v0), .space = PETTA_SPACE_ATOMS };
        r.ntake = 1;
        r.take[0] = (Pat){ .t = tc_app(eng->con_atom_box, &v1), .space = PETTA_SPACE_ATOMS };
        r.make = (Pat){ .t = tc_app(eng->con_atom_box, &v2), .space = PETTA_SPACE_ATOMS };
        eng->rule_simpagate_consume = tc_rule(&r);
    }
    /* Rule 6: comm! (paired linear take of sender msg + receiver cont, make result) */
    {
        tc_ctx(3, ctx3);
        Term v0 = tc_v(0);
        Term v1 = tc_v(1);
        Term v2 = tc_v(2);
        Rule r;
        memset(&r, 0, sizeof(r));
        r.fresh = -1;
        r.inputs = 0x4;   /* the result the host computed */
        r.ntake = 2;
        r.take[0] = (Pat){ .t = tc_app(eng->con_atom_box, &v0), .space = PETTA_SPACE_ATOMS };
        r.take[1] = (Pat){ .t = tc_app(eng->con_atom_box, &v1), .space = PETTA_SPACE_ATOMS };
        r.make = (Pat){ .t = tc_app(eng->con_atom_box, &v2), .space = PETTA_SPACE_ATOMS };
        eng->rule_comm_sync = tc_rule(&r);
    }

    tc_seal();
    eng->profile_linear = tc_admission_custom_profile(
        "petta_linear", false, true, false, false, NULL, NULL);
    eng->profile_set = tc_admission_custom_profile(
        "petta_set_saturation", true, true, false, false, NULL, NULL);
}

static inline void petta_ensure_rules_cap(PettaTcalcEngine *eng, uint32_t needed) {
    if (needed <= eng->cap_rules) return;
    uint32_t old_cap = eng->cap_rules;
    uint32_t new_cap = old_cap ? old_cap * 2u : 64u;
    while (new_cap < needed) new_cap *= 2u;
    eng->rules = (PettaEqRule *)realloc(eng->rules, (size_t)new_cap * sizeof(PettaEqRule));
    memset(eng->rules + old_cap, 0, (size_t)(new_cap - old_cap) * sizeof(PettaEqRule));
    eng->cap_rules = new_cap;
}

static inline void petta_ensure_store_cap(PettaTcalcEngine *eng, uint32_t needed) {
    if (needed <= eng->cap_store) return;
    uint32_t old_cap = eng->cap_store;
    uint32_t new_cap = old_cap ? old_cap * 2u : 64u;
    while (new_cap < needed) new_cap *= 2u;
    eng->store = (PettaStoreEntry *)realloc(eng->store, (size_t)new_cap * sizeof(PettaStoreEntry));
    memset(eng->store + old_cap, 0, (size_t)(new_cap - old_cap) * sizeof(PettaStoreEntry));
    eng->cap_store = new_cap;
}

static inline void petta_ensure_interned_cap(PettaTcalcEngine *eng, uint32_t needed) {
    if (needed <= eng->cap_interned) return;
    uint32_t new_cap = eng->cap_interned ? eng->cap_interned * 2u : 64u;
    while (new_cap < needed) new_cap *= 2u;
    eng->interned_atoms = (PettaAtom **)realloc(eng->interned_atoms, (size_t)new_cap * sizeof(PettaAtom *));
    eng->interned_name_ids = (uint64_t *)realloc(eng->interned_name_ids, (size_t)new_cap * sizeof(uint64_t));
    eng->cap_interned = new_cap;
}

static inline void petta_tcalc_engine_destroy(PettaTcalcEngine *eng) {
    if (!eng) return;
    for (uint32_t i = 0; i < eng->nrules; i++) {
        petta_atom_free(eng->rules[i].lhs);
        petta_atom_free(eng->rules[i].rhs);
    }
    for (uint32_t i = 0; i < eng->nstore; i++) {
        petta_atom_free(eng->store[i].atom);
    }
    for (uint32_t i = 0; i < eng->ninterned; i++) {
        petta_atom_free(eng->interned_atoms[i]);
    }
    free(eng->rules);
    free(eng->store);
    free(eng->hist);
    free(eng->interned_atoms);
    free(eng->interned_name_ids);
    memset(eng, 0, sizeof(*eng));
}

static inline Term petta_encode_tc_term(PettaTcalcEngine *eng, const PettaAtom *a) {
    for (uint32_t i = 0; i < eng->ninterned; i++) {
        if (petta_atom_eq(eng->interned_atoms[i], a)) {
            return tc_name((uint16_t)eng->sort_val, eng->interned_name_ids[i]);
        }
    }
    uint64_t fid = tc_fresh_name();
    while (fid == 0) fid = tc_fresh_name();
    petta_ensure_interned_cap(eng, eng->ninterned + 1u);
    uint32_t idx = eng->ninterned++;
    eng->interned_atoms[idx] = petta_atom_clone(a);
    eng->interned_name_ids[idx] = fid;
    return tc_name((uint16_t)eng->sort_val, fid);
}

static inline void petta_register_rule(PettaTcalcEngine *eng, const PettaAtom *lhs_in, const PettaAtom *rhs_in) {
    petta_ensure_rules_cap(eng, eng->nrules + 1u);
    PettaAtom *lhs = petta_atom_clone(lhs_in);
    PettaAtom *rhs = petta_atom_clone(rhs_in);
    uint32_t r_arity = (lhs->kind == PETTA_ATOM_EXPR) ? lhs->arity : 0u;
    uint32_t r_hash = 0u;
    if (lhs->kind == PETTA_ATOM_EXPR && lhs->arity > 0) {
        if (lhs->args[0]->kind == PETTA_ATOM_SYM) {
            r_hash = petta_str_fnv1a(lhs->args[0]->text);
            uint32_t b1 = r_hash & 255u;
            uint32_t b2 = (r_hash >> 8) & 255u;
            eng->rule_head_bloom[b1 >> 6] |= (1ULL << (b1 & 63u));
            eng->rule_head_bloom[b2 >> 6] |= (1ULL << (b2 & 63u));
        } else {
            eng->has_var_head_rules = true;
        }
    } else {
        eng->has_sym_rules = true;
        if (lhs->kind == PETTA_ATOM_VAR) {
            eng->has_var_head_rules = true;
        }
    }
    eng->rules[eng->nrules].removed = false;
    eng->rules[eng->nrules].lhs = lhs;
    eng->rules[eng->nrules].rhs = rhs;
    eng->rules[eng->nrules].arity = r_arity;
    eng->rules[eng->nrules].head_hash = r_hash;
    eng->rules[eng->nrules].next_in_bucket = 0u;
    if (r_hash != 0u) {
        uint32_t b = r_hash & 255u;
        if (eng->rule_bucket_head[b] == 0u) {
            eng->rule_bucket_head[b] = eng->nrules + 1u;
        } else {
            eng->rules[eng->rule_bucket_tail[b] - 1u].next_in_bucket = eng->nrules + 1u;
        }
        eng->rule_bucket_tail[b] = eng->nrules + 1u;
    }
    eng->nrules++;
}

static __attribute__((noinline)) bool petta_store_add_atom_space(
    PettaTcalcEngine *eng,
    const char *space_name,
    const PettaAtom *a)
{
    if (!space_name || !space_name[0]) space_name = "&self";
    if (strcmp(space_name, "&self") == 0 &&
        a->kind == PETTA_ATOM_EXPR && a->arity == 3 &&
        a->args[0]->kind == PETTA_ATOM_SYM && strcmp(a->args[0]->text, "=") == 0 &&
        (a->args[1]->kind == PETTA_ATOM_SYM ||
         (a->args[1]->kind == PETTA_ATOM_EXPR && a->args[1]->arity > 0 &&
          (a->args[1]->args[0]->kind == PETTA_ATOM_SYM || a->args[1]->args[0]->kind == PETTA_ATOM_EXPR)))) {
        petta_register_rule(eng, a->args[1], a->args[2]);
    }
    eng->steps_executed += 16u + (eng->nstore >> 3);
    if (eng->max_steps > 0 && eng->steps_executed >= eng->max_steps) {
        eng->status = PETTA_STATUS_BUDGET_EXHAUSTED;
        return false;
    }
    petta_ensure_store_cap(eng, eng->nstore + 1u);
    Term inner = petta_encode_tc_term(eng, a);
    Term inst[TC_VARS];
    memset(inst, 0, sizeof(inst));
    inst[0] = inner;
    TcPreparedStep cand;
    memset(&cand, 0, sizeof(cand));
    cand.rule = eng->rule_add_atom;
    cand.inst = inst;
    TcPreparedEffect eff;
    TcAdmissionReceipt rec;
    TcRefusalReason ref = TC_REFUSE_NONE;
    if (tc_bridge_execute_candidate(
            &cand, &eng->profile_linear, &eff, &eng->last_event, &rec, &ref) != TC_BRIDGE_ADMITTED) {
        return false;
    }
    eng->last_receipt = rec;
    eng->tc_events_admitted++;
    PettaStoreEntry *se = &eng->store[eng->nstore++];
    se->alive = true;
    se->id = eng->next_occ_id++;
    snprintf(se->space, sizeof(se->space), "%s", space_name);
    se->atom = petta_atom_clone(a);
    se->tc_term = inner;
    se->tc_occ = rec.out;
    return true;
}

static inline bool petta_store_add_atom(PettaTcalcEngine *eng, const PettaAtom *a) {
    return petta_store_add_atom_space(eng, "&self", a);
}

static __attribute__((noinline)) bool petta_store_remove_atom_space(
    PettaTcalcEngine *eng,
    const char *space_name,
    const PettaAtom *a)
{
    if (!space_name || !space_name[0]) space_name = "&self";
    bool any_removed = false;
    if (strcmp(space_name, "&self") == 0 &&
        a->kind == PETTA_ATOM_EXPR && a->arity == 3 &&
        a->args[0]->kind == PETTA_ATOM_SYM && strcmp(a->args[0]->text, "=") == 0) {
        for (uint32_t r = 0; r < eng->nrules; r++) {
            if (!eng->rules[r].removed &&
                petta_atom_alpha_eq(eng->rules[r].lhs, a->args[1]) &&
                petta_atom_alpha_eq(eng->rules[r].rhs, a->args[2])) {
                eng->rules[r].removed = true;
                eng->tc_events_admitted++;
                any_removed = true;
            }
        }
    }
    for (uint32_t i = 0; i < eng->nstore; i++) {
        if (!eng->store[i].alive) continue;
        const char *es = eng->store[i].space[0] ? eng->store[i].space : "&self";
        if (strcmp(es, space_name) != 0) continue;
        PettaEnv uenv;
        petta_env_init(&uenv);
        bool matches = (a->has_vars || eng->store[i].atom->has_vars)
            ? petta_unify_atoms(a, eng->store[i].atom, &uenv)
            : petta_atom_eq(eng->store[i].atom, a);
        petta_env_free(&uenv);
        if (matches) {
            Occ take_occs[1] = { eng->store[i].tc_occ };
            Term inst[TC_VARS];
            memset(inst, 0, sizeof(inst));
            inst[0] = eng->store[i].tc_term;
            TcPreparedStep cand;
            memset(&cand, 0, sizeof(cand));
            cand.rule = eng->rule_remove_atom;
            cand.take = take_occs;
            cand.inst = inst;
            TcPreparedEffect eff;
            TcAdmissionReceipt rec;
            TcRefusalReason ref = TC_REFUSE_NONE;
            if (tc_bridge_execute_candidate(
                    &cand, &eng->profile_linear, &eff, &eng->last_event, &rec, &ref) == TC_BRIDGE_ADMITTED) {
                eng->last_receipt = rec;
                eng->tc_events_admitted++;
                eng->store[i].alive = false;
                any_removed = true;
            }
        }
    }
    return any_removed;
}

static inline bool petta_store_remove_atom(PettaTcalcEngine *eng, const PettaAtom *a) {
    return petta_store_remove_atom_space(eng, "&self", a);
}

static inline bool petta_space_matches(const PettaStoreEntry *se, const char *space_name) {
    const char *es = se->space[0] ? se->space : "&self";
    const char *qs = (space_name && space_name[0]) ? space_name : "&self";
    return strcmp(es, qs) == 0;
}

/* =========================================================================
 * 5. Core PeTTa Evaluator + 5 MeTTa Prime Sub-Calculi Syntactic Sugar Forms
 * ========================================================================= */

static inline void petta_vallist_init(PettaValList *vl) {
    memset(vl, 0, sizeof(*vl));
}

static inline void petta_vallist_free(PettaValList *vl) {
    if (!vl) return;
    for (uint32_t i = 0; i < vl->count; i++) {
        petta_atom_free(vl->items[i]);
    }
    free(vl->items);
    vl->items = NULL;
    vl->count = 0;
    vl->cap = 0;
}

static inline void petta_vallist_push_take(PettaValList *vl, PettaAtom *a) {
    if (!a) return;
    if (vl->count >= vl->cap) {
        uint32_t ncap = vl->cap ? vl->cap * 2u : 4u;
        vl->items = (PettaAtom **)realloc(vl->items, (size_t)ncap * sizeof(PettaAtom *));
        vl->cap = ncap;
    }
    vl->items[vl->count++] = a;
}

static inline void petta_vallist_push_clone(PettaValList *vl, const PettaAtom *a) {
    if (!a) return;
    petta_vallist_push_take(vl, petta_atom_clone(a));
}

static inline bool petta_atom_is_truthy(const PettaAtom *a) {
    if (!a) return false;
    if (a->kind == PETTA_ATOM_SYM) {
        return strcmp(a->text, "True") == 0 || strcmp(a->text, "true") == 0 || strcmp(a->text, "Unit") == 0;
    }
    if (a->kind == PETTA_ATOM_INT) {
        return a->ival != 0;
    }
    return false;
}

static inline bool petta_atom_is_falsy(const PettaAtom *a) {
    if (!a) return false;
    if (a->kind == PETTA_ATOM_SYM) {
        return strcmp(a->text, "False") == 0 || strcmp(a->text, "false") == 0;
    }
    if (a->kind == PETTA_ATOM_INT) {
        return a->ival == 0;
    }
    return false;
}

static inline void petta_eval_expr(
    PettaTcalcEngine *eng,
    const PettaAtom *expr,
    PettaValList *out_vals);

/* Evaluate a single expression and return its first value (or clone of expr if empty) */
static inline PettaAtom *petta_eval_one(PettaTcalcEngine *eng, const PettaAtom *expr) {
    PettaValList vl;
    petta_vallist_init(&vl);
    petta_eval_expr(eng, expr, &vl);
    if (vl.count == 0) {
        petta_vallist_free(&vl);
        return petta_atom_sym("Empty");
    }
    PettaAtom *res = petta_atom_clone(vl.items[0]);
    petta_vallist_free(&vl);
    return res;
}

/* Helper for the 4 Mutating MeTTa Prime Sub-Calculi Syntactic Sugar Forms (extracted to keep
 * petta_eval_expr's and match's stack frames tiny under AddressSanitizer). */
static __attribute__((noinline)) bool petta_eval_mutating_subcalc(
    PettaTcalcEngine *eng,
    const char *op,
    const PettaAtom *expr,
    PettaValList *out_vals)
{
    /* Sub-Calculus 2 (MonotoneDatalog):
     * (infer-atoms! &self (from ($p1 ...)) (where ($g1 ...)) (emit $head)) */
    if (strcmp(op, "infer-atoms!") == 0 && expr->arity == 5) {
        const PettaAtom *from_clause = expr->args[2];
        const PettaAtom *where_clause = expr->args[3];
        const PettaAtom *emit_clause = expr->args[4];
        if (from_clause->kind == PETTA_ATOM_EXPR && from_clause->arity == 2 &&
            from_clause->args[1]->kind == PETTA_ATOM_EXPR &&
            where_clause->kind == PETTA_ATOM_EXPR && where_clause->arity == 2 &&
            where_clause->args[1]->kind == PETTA_ATOM_EXPR &&
            emit_clause->kind == PETTA_ATOM_EXPR && emit_clause->arity == 2) {
            const PettaAtom *pats = from_clause->args[1];
            const PettaAtom *guards = where_clause->args[1];
            const PettaAtom *head_tmpl = emit_clause->args[1];
            uint32_t added_total = 0;
            bool changed = true;
            while (changed && eng->status == PETTA_STATUS_OK) {
                changed = false;
                for (uint32_t i = 0; i < eng->nstore; i++) {
                    if (!eng->store[i].alive || pats->arity == 0) continue;
                    PettaEnv env1;
                    if (!petta_match_pattern(pats->args[0], eng->store[i].atom, &env1)) continue;
                    uint32_t j_limit = (pats->arity >= 2) ? eng->nstore : 1u;
                    for (uint32_t j = 0; j < j_limit; j++) {
                        PettaEnv env_join = petta_env_clone(&env1);
                        if (pats->arity >= 2) {
                            if (!eng->store[j].alive) {
                                petta_env_free(&env_join);
                                continue;
                            }
                            PettaAtom *p2_sub = petta_subst_env(pats->args[1], &env_join);
                            PettaEnv env2;
                            bool ok2 = petta_match_pattern(p2_sub, eng->store[j].atom, &env2);
                            petta_atom_free(p2_sub);
                            if (!ok2) {
                                petta_env_free(&env_join);
                                continue;
                            }
                            for (uint32_t b = 0; b < env2.nbinds; b++)
                                petta_env_bind(&env_join, env2.binds[b].var, env2.binds[b].val);
                            petta_env_free(&env2);
                        }
                        bool guards_ok = true;
                        for (uint32_t g = 0; g < guards->arity; g++) {
                            PettaAtom *gsub = petta_subst_env(guards->args[g], &env_join);
                            PettaAtom *gval = petta_eval_one(eng, gsub);
                            petta_atom_free(gsub);
                            if (!petta_atom_is_truthy(gval)) guards_ok = false;
                            petta_atom_free(gval);
                            if (!guards_ok) break;
                        }
                        if (guards_ok) {
                            PettaAtom *derived = petta_subst_env(head_tmpl, &env_join);
                            Term dterm = petta_encode_tc_term(eng, derived);
                            Occ keep_occs[1] = { eng->store[i].tc_occ };
                            Term inst[TC_VARS];
                            memset(inst, 0, sizeof(inst));
                            inst[0] = eng->store[i].tc_term;
                            inst[1] = dterm;
                            TcPreparedStep cand;
                            memset(&cand, 0, sizeof(cand));
                            cand.rule = eng->rule_infer_atom;
                            cand.keep = keep_occs;
                            cand.inst = inst;
                            TcPreparedEffect eff;
                            TcAdmissionReceipt rec;
                            TcRefusalReason ref = TC_REFUSE_NONE;
                            if (tc_bridge_execute_candidate(
                                    &cand, &eng->profile_set, &eff, &eng->last_event, &rec, &ref) == TC_BRIDGE_ADMITTED) {
                                eng->last_receipt = rec;
                                eng->tc_events_admitted++;
                                eng->subcalc_datalog_inferred++;
                                petta_ensure_store_cap(eng, eng->nstore + 1u);
                                PettaStoreEntry *se = &eng->store[eng->nstore++];
                                se->alive = true;
                                se->id = eng->next_occ_id++;
                                se->atom = derived;
                                se->tc_term = dterm;
                                se->tc_occ = rec.out;
                                added_total++;
                                changed = true;
                            } else {
                                petta_atom_free(derived);
                            }
                        }
                        petta_env_free(&env_join);
                    }
                    petta_env_free(&env1);
                }
            }
            petta_vallist_push_take(out_vals, petta_atom_int((int64_t)added_total));
            return true;
        }
    }

    /* Sub-Calculus 3a (LinearConsumption): (take-atom! &self $pattern $template) */
    if (strcmp(op, "take-atom!") == 0 && expr->arity == 4) {
        const PettaAtom *pat = expr->args[2];
        const PettaAtom *tmpl = expr->args[3];
        for (uint32_t i = 0; i < eng->nstore; i++) {
            if (!eng->store[i].alive || !tc_alive(eng->store[i].tc_occ)) continue;
            PettaEnv menv;
            if (petta_match_pattern(pat, eng->store[i].atom, &menv)) {
                Occ take_occs[1] = { eng->store[i].tc_occ };
                Term inst[TC_VARS];
                memset(inst, 0, sizeof(inst));
                inst[0] = eng->store[i].tc_term;
                TcPreparedStep cand;
                memset(&cand, 0, sizeof(cand));
                cand.rule = eng->rule_remove_atom;
                cand.take = take_occs;
                cand.inst = inst;
                TcPreparedEffect eff;
                TcAdmissionReceipt rec;
                TcRefusalReason ref = TC_REFUSE_NONE;
                if (tc_bridge_execute_candidate(
                        &cand, &eng->profile_linear, &eff, &eng->last_event, &rec, &ref) == TC_BRIDGE_ADMITTED) {
                    eng->last_receipt = rec;
                    eng->tc_events_admitted++;
                    eng->subcalc_linear_taken++;
                    eng->store[i].alive = false;
                    PettaAtom *sub = petta_subst_env(tmpl, &menv);
                    petta_env_free(&menv);
                    petta_eval_expr(eng, sub, out_vals);
                    petta_atom_free(sub);
                    return true;
                }
                petta_env_free(&menv);
            }
        }
        petta_vallist_push_take(out_vals, petta_atom_sym("Empty"));
        return true;
    }

    /* Sub-Calculus 3b (LinearReplacement): (replace-atom! &self $old_pat $new_tmpl) */
    if (strcmp(op, "replace-atom!") == 0 && expr->arity == 4) {
        const PettaAtom *old_pat = expr->args[2];
        const PettaAtom *new_tmpl = expr->args[3];
        for (uint32_t i = 0; i < eng->nstore; i++) {
            if (!eng->store[i].alive || !tc_alive(eng->store[i].tc_occ)) continue;
            PettaEnv menv;
            if (petta_match_pattern(old_pat, eng->store[i].atom, &menv)) {
                PettaAtom *new_sub = petta_subst_env(new_tmpl, &menv);
                petta_env_free(&menv);
                PettaAtom *new_val = petta_eval_one(eng, new_sub);
                petta_atom_free(new_sub);
                Term new_tc = petta_encode_tc_term(eng, new_val);
                Occ take_occs[1] = { eng->store[i].tc_occ };
                Term inst[TC_VARS];
                memset(inst, 0, sizeof(inst));
                inst[0] = eng->store[i].tc_term;
                inst[1] = new_tc;
                TcPreparedStep cand;
                memset(&cand, 0, sizeof(cand));
                cand.rule = eng->rule_replace_atom;
                cand.take = take_occs;
                cand.inst = inst;
                TcPreparedEffect eff;
                TcAdmissionReceipt rec;
                TcRefusalReason ref = TC_REFUSE_NONE;
                if (tc_bridge_execute_candidate(
                        &cand, &eng->profile_linear, &eff, &eng->last_event, &rec, &ref) == TC_BRIDGE_ADMITTED) {
                    eng->last_receipt = rec;
                    eng->tc_events_admitted++;
                    eng->subcalc_linear_taken++;
                    eng->store[i].alive = false;
                    petta_ensure_store_cap(eng, eng->nstore + 1u);
                    PettaStoreEntry *se = &eng->store[eng->nstore++];
                    se->alive = true;
                    se->id = eng->next_occ_id++;
                    se->atom = new_val;
                    se->tc_term = new_tc;
                    se->tc_occ = rec.out;
                    petta_vallist_push_clone(out_vals, new_val);
                    return true;
                }
                petta_atom_free(new_val);
            }
        }
        petta_vallist_push_take(out_vals, petta_atom_sym("Empty"));
        return true;
    }

    /* Sub-Calculus 4 (RefinedCHR Simpagation):
     * (simpagate! &self $keep_pat $rem_pat $guard $body_tmpl) */
    if (strcmp(op, "simpagate!") == 0 && expr->arity == 6) {
        const PettaAtom *kpat = expr->args[2];
        const PettaAtom *rpat = expr->args[3];
        const PettaAtom *gexpr = expr->args[4];
        const PettaAtom *btmpl = expr->args[5];
        for (uint32_t i = 0; i < eng->nstore; i++) {
            if (!eng->store[i].alive || !tc_alive(eng->store[i].tc_occ)) continue;
            PettaEnv kenv;
            if (!petta_match_pattern(kpat, eng->store[i].atom, &kenv)) continue;
            for (uint32_t j = 0; j < eng->nstore; j++) {
                if (i == j || !eng->store[j].alive || !tc_alive(eng->store[j].tc_occ)) continue;
                PettaEnv jenv = petta_env_clone(&kenv);
                PettaAtom *rpat_sub = petta_subst_env(rpat, &jenv);
                PettaEnv renv;
                bool ok_r = petta_match_pattern(rpat_sub, eng->store[j].atom, &renv);
                petta_atom_free(rpat_sub);
                if (!ok_r) {
                    petta_env_free(&jenv);
                    continue;
                }
                for (uint32_t b = 0; b < renv.nbinds; b++)
                    petta_env_bind(&jenv, renv.binds[b].var, renv.binds[b].val);
                petta_env_free(&renv);

                PettaAtom *gsub = petta_subst_env(gexpr, &jenv);
                PettaAtom *gval = petta_eval_one(eng, gsub);
                petta_atom_free(gsub);
                bool gh = petta_atom_is_truthy(gval);
                petta_atom_free(gval);
                if (gh) {
                    PettaAtom *bsub = petta_subst_env(btmpl, &jenv);
                    PettaAtom *bval = petta_eval_one(eng, bsub);
                    petta_atom_free(bsub);
                    Term b_tc = petta_encode_tc_term(eng, bval);
                    Occ keep_occs[1] = { eng->store[i].tc_occ };
                    Occ take_occs[1] = { eng->store[j].tc_occ };
                    Term inst[TC_VARS];
                    memset(inst, 0, sizeof(inst));
                    inst[0] = eng->store[i].tc_term;
                    inst[1] = eng->store[j].tc_term;
                    inst[2] = b_tc;
                    TcPreparedStep cand;
                    memset(&cand, 0, sizeof(cand));
                    cand.rule = eng->rule_simpagate_consume;
                    cand.keep = keep_occs;
                    cand.take = take_occs;
                    cand.inst = inst;
                    TcPreparedEffect eff;
                    TcAdmissionReceipt rec;
                    TcRefusalReason ref = TC_REFUSE_NONE;
                    if (tc_bridge_execute_candidate(
                            &cand, &eng->profile_linear, &eff, &eng->last_event, &rec, &ref) == TC_BRIDGE_ADMITTED) {
                        eng->last_receipt = rec;
                        eng->tc_events_admitted++;
                        eng->subcalc_simpagate_fired++;
                        eng->store[j].alive = false;
                        petta_ensure_store_cap(eng, eng->nstore + 1u);
                        PettaStoreEntry *se = &eng->store[eng->nstore++];
                        se->alive = true;
                        se->id = eng->next_occ_id++;
                        se->atom = bval;
                        se->tc_term = b_tc;
                        se->tc_occ = rec.out;
                        petta_env_free(&jenv);
                        petta_env_free(&kenv);
                        petta_vallist_push_clone(out_vals, bval);
                        return true;
                    }
                    petta_atom_free(bval);
                }
                petta_env_free(&jenv);
            }
            petta_env_free(&kenv);
        }
        petta_vallist_push_take(out_vals, petta_atom_sym("Empty"));
        return true;
    }

    /* Sub-Calculus 5 (Synchronized Channel Comm):
     * (send-chan! &self $chan $msg) & (comm! &self $chan $msg_pat $body) */
    if (strcmp(op, "send-chan!") == 0 && expr->arity == 4) {
        PettaAtom *ch = petta_eval_one(eng, expr->args[2]);
        PettaAtom *msg = petta_eval_one(eng, expr->args[3]);
        PettaAtom *env_args[3] = { petta_atom_sym("ChannelMsg"), ch, msg };
        PettaAtom *envelope = petta_atom_expr(3, env_args);
        petta_store_add_atom(eng, envelope);
        petta_atom_free(envelope);
        petta_vallist_push_take(out_vals, petta_atom_sym("Sent"));
        return true;
    }
    if (strcmp(op, "comm!") == 0 && expr->arity == 5) {
        PettaAtom *ch = petta_eval_one(eng, expr->args[2]);
        const PettaAtom *mpat = expr->args[3];
        const PettaAtom *body = expr->args[4];
        PettaAtom *rw_args[2] = { petta_atom_sym("ChannelRecv"), petta_atom_clone(ch) };
        PettaAtom *rw = petta_atom_expr(2, rw_args);
        for (uint32_t i = 0; i < eng->nstore; i++) {
            if (!eng->store[i].alive || !tc_alive(eng->store[i].tc_occ)) continue;
            const PettaAtom *a = eng->store[i].atom;
            if (a->kind == PETTA_ATOM_EXPR && a->arity == 3 &&
                a->args[0]->kind == PETTA_ATOM_SYM &&
                strcmp(a->args[0]->text, "ChannelMsg") == 0 &&
                petta_atom_eq(a->args[1], ch)) {
                PettaEnv menv;
                if (petta_match_pattern(mpat, a->args[2], &menv)) {
                    petta_store_add_atom(eng, rw);
                    uint32_t rw_idx = eng->nstore - 1u;
                    PettaAtom *bsub = petta_subst_env(body, &menv);
                    petta_env_free(&menv);
                    PettaAtom *bval = petta_eval_one(eng, bsub);
                    petta_atom_free(bsub);
                    Term b_tc = petta_encode_tc_term(eng, bval);
                    Occ take_occs[2] = { eng->store[i].tc_occ, eng->store[rw_idx].tc_occ };
                    Term inst[TC_VARS];
                    memset(inst, 0, sizeof(inst));
                    inst[0] = eng->store[i].tc_term;
                    inst[1] = eng->store[rw_idx].tc_term;
                    inst[2] = b_tc;
                    TcPreparedStep cand;
                    memset(&cand, 0, sizeof(cand));
                    cand.rule = eng->rule_comm_sync;
                    cand.take = take_occs;
                    cand.inst = inst;
                    TcPreparedEffect eff;
                    TcAdmissionReceipt rec;
                    TcRefusalReason ref = TC_REFUSE_NONE;
                    if (tc_bridge_execute_candidate(
                            &cand, &eng->profile_linear, &eff, &eng->last_event, &rec, &ref) == TC_BRIDGE_ADMITTED) {
                        eng->last_receipt = rec;
                        eng->tc_events_admitted++;
                        eng->subcalc_comm_synced++;
                        eng->store[i].alive = false;
                        eng->store[rw_idx].alive = false;
                        petta_ensure_store_cap(eng, eng->nstore + 1u);
                        PettaStoreEntry *se = &eng->store[eng->nstore++];
                        se->alive = true;
                        se->id = eng->next_occ_id++;
                        se->atom = bval;
                        se->tc_term = b_tc;
                        se->tc_occ = rec.out;
                        petta_atom_free(rw);
                        petta_atom_free(ch);
                        petta_vallist_push_clone(out_vals, bval);
                        return true;
                    }
                    petta_atom_free(bval);
                }
            }
        }
        petta_atom_free(rw);
        petta_atom_free(ch);
        petta_vallist_push_take(out_vals, petta_atom_sym("Blocked"));
        return true;
    }
    return false;
}

static void petta_match_conj(
    PettaTcalcEngine *eng,
    const char *space_name,
    const PettaAtom *conj_pat,
    uint32_t cidx,
    const PettaAtom *tmpl,
    PettaValList *out_vals)
{
    if (eng->status != PETTA_STATUS_OK) return;
    if (cidx >= conj_pat->arity) {
        petta_eval_expr(eng, tmpl, out_vals);
        return;
    }
    const PettaAtom *sub_pat = conj_pat->args[cidx];
    for (uint32_t i = 0; i < eng->nstore && eng->status == PETTA_STATUS_OK; i++) {
        if ((i & 15u) == 15u) {
            eng->steps_executed++;
            if (eng->max_steps > 0 && eng->steps_executed >= eng->max_steps) {
                eng->status = PETTA_STATUS_BUDGET_EXHAUSTED;
                break;
            }
        }
        if (!eng->store[i].alive || !tc_alive(eng->store[i].tc_occ)) continue;
        if (!petta_space_matches(&eng->store[i], space_name)) continue;
        PettaEnv menv;
        if (petta_match_pattern(sub_pat, eng->store[i].atom, &menv)) {
            PettaAtom *next_conj = petta_subst_env(conj_pat, &menv);
            PettaAtom *next_tmpl = petta_subst_env(tmpl, &menv);
            petta_env_free(&menv);
            petta_match_conj(eng, space_name, next_conj, cidx + 1u, next_tmpl, out_vals);
            petta_atom_free(next_conj);
            petta_atom_free(next_tmpl);
        }
    }
}

static __attribute__((noinline)) bool petta_eval_subcalc(
    PettaTcalcEngine *eng,
    const char *op,
    const PettaAtom *expr,
    PettaValList *out_vals)
{
    /* Sub-Calculus 1 (ReadOnlyQuery): (match &self $pattern $template) */
    if (strcmp(op, "match") == 0 && expr->arity == 4) {
        if (expr->args[1]->kind == PETTA_ATOM_VAR) {
            PettaAtom *eargs[3] = {
                petta_atom_sym("Error"),
                petta_atom_sym("instantiation_error"),
                petta_atom_sym("match")
            };
            petta_vallist_push_take(out_vals, petta_atom_expr(3, eargs));
            return true;
        }
        PettaAtom *eval_sp = NULL;
        const PettaAtom *sp_atom = expr->args[1];
        if (sp_atom->kind == PETTA_ATOM_EXPR) {
            eval_sp = petta_eval_one(eng, sp_atom);
            sp_atom = eval_sp;
        }
        if (sp_atom->kind != PETTA_ATOM_SYM) {
            petta_atom_free(eval_sp);
            PettaAtom *eargs[3] = {
                petta_atom_sym("Error"),
                petta_atom_sym("type_error"),
                petta_atom_sym("match")
            };
            petta_vallist_push_take(out_vals, petta_atom_expr(3, eargs));
            return true;
        }
        char space_buf[64];
        snprintf(space_buf, sizeof(space_buf), "%s", sp_atom->text);
        petta_atom_free(eval_sp);
        const char *space_name = space_buf;
        eng->subcalc_queries_run++;
        const PettaAtom *pat = expr->args[2];
        const PettaAtom *tmpl = expr->args[3];
        if (pat->kind == PETTA_ATOM_EXPR && pat->arity >= 1 &&
            pat->args[0]->kind == PETTA_ATOM_SYM && strcmp(pat->args[0]->text, ",") == 0) {
            petta_match_conj(eng, space_name, pat, 1u, tmpl, out_vals);
            return true;
        }
        for (uint32_t i = 0; i < eng->nstore && eng->status == PETTA_STATUS_OK; i++) {
            if ((i & 15u) == 15u) {
                eng->steps_executed++;
                if (eng->max_steps > 0 && eng->steps_executed >= eng->max_steps) {
                    eng->status = PETTA_STATUS_BUDGET_EXHAUSTED;
                    break;
                }
            }
            if (!eng->store[i].alive || !tc_alive(eng->store[i].tc_occ)) continue;
            if (!petta_space_matches(&eng->store[i], space_name)) continue;
            if (eng->store[i].atom->has_vars) {
                PettaAtom *db_atom = petta_freshen_vars(eng->store[i].atom, ++eng->var_freshen_seq);
                PettaEnv uenv;
                petta_env_init(&uenv);
                if (petta_unify_atoms(pat, db_atom, &uenv)) {
                    PettaAtom *inst = petta_subst_env_trans(tmpl, &uenv);
                    petta_env_free(&uenv);
                    petta_atom_free(db_atom);
                    petta_eval_expr(eng, inst, out_vals);
                    petta_atom_free(inst);
                } else {
                    petta_env_free(&uenv);
                    petta_atom_free(db_atom);
                }
            } else {
                PettaEnv menv;
                if (petta_match_pattern(pat, eng->store[i].atom, &menv)) {
                    PettaAtom *inst = petta_subst_env(tmpl, &menv);
                    petta_env_free(&menv);
                    petta_eval_expr(eng, inst, out_vals);
                    petta_atom_free(inst);
                }
            }
        }
        bool want_rules = (strcmp(space_name, "&self") == 0 &&
            ((pat->kind == PETTA_ATOM_EXPR && pat->arity == 3 &&
              pat->args[0]->kind == PETTA_ATOM_SYM && strcmp(pat->args[0]->text, "=") == 0) ||
             (tmpl->kind == PETTA_ATOM_EXPR && tmpl->arity >= 1 &&
              tmpl->args[0]->kind == PETTA_ATOM_SYM && strcmp(tmpl->args[0]->text, "remove-atom") == 0)));
        if (want_rules) {
            uint32_t nr_snap = eng->nrules;
            for (uint32_t r = 0; r < nr_snap && eng->status == PETTA_STATUS_OK; r++) {
                if (eng->rules[r].removed) continue;
                PettaAtom *eq_args[3] = {
                    petta_atom_sym("="),
                    petta_atom_clone(eng->rules[r].lhs),
                    petta_atom_clone(eng->rules[r].rhs)
                };
                PettaAtom *raw_eq = petta_atom_expr(3, eq_args);
                bool in_store = false;
                for (uint32_t s = 0; s < eng->nstore; s++) {
                    if (eng->store[s].alive && petta_space_matches(&eng->store[s], "&self") &&
                        petta_atom_alpha_eq(eng->store[s].atom, raw_eq)) {
                        in_store = true;
                        break;
                    }
                }
                if (in_store) {
                    petta_atom_free(raw_eq);
                    continue;
                }
                PettaAtom *db_eq = petta_freshen_vars(raw_eq, ++eng->var_freshen_seq);
                petta_atom_free(raw_eq);
                PettaEnv uenv;
                petta_env_init(&uenv);
                if (petta_unify_atoms(pat, db_eq, &uenv)) {
                    PettaAtom *inst = petta_subst_env_trans(tmpl, &uenv);
                    petta_env_free(&uenv);
                    petta_atom_free(db_eq);
                    petta_eval_expr(eng, inst, out_vals);
                    petta_atom_free(inst);
                } else {
                    petta_env_free(&uenv);
                    petta_atom_free(db_eq);
                }
            }
        }
        return true;
    }
    return petta_eval_mutating_subcalc(eng, op, expr, out_vals);
}

static inline bool petta_has_user_rule(const PettaTcalcEngine *eng, const char *op, uint32_t arity) {
    uint32_t h = petta_str_fnv1a(op);
    if (!eng->has_var_head_rules) {
        uint32_t r1 = eng->rule_bucket_head[h & 255u];
        while (r1 != 0u) {
            uint32_t r = r1 - 1u;
            r1 = eng->rules[r].next_in_bucket;
            if (eng->rules[r].removed) continue;
            if ((eng->rules[r].arity == 0u || eng->rules[r].arity == arity) &&
                eng->rules[r].head_hash == h &&
                eng->rules[r].lhs->kind == PETTA_ATOM_EXPR &&
                eng->rules[r].lhs->arity > 0 &&
                eng->rules[r].lhs->args[0]->kind == PETTA_ATOM_SYM &&
                strcmp(eng->rules[r].lhs->args[0]->text, op) == 0) {
                return true;
            }
        }
        return false;
    }
    for (uint32_t r = 0; r < eng->nrules; r++) {
        if (eng->rules[r].removed) continue;
        if ((eng->rules[r].arity == 0u || eng->rules[r].arity == arity) &&
            eng->rules[r].lhs->kind == PETTA_ATOM_EXPR &&
            eng->rules[r].lhs->arity > 0 &&
            eng->rules[r].lhs->args[0]->kind == PETTA_ATOM_SYM &&
            strcmp(eng->rules[r].lhs->args[0]->text, op) == 0) {
            return true;
        }
    }
    return false;
}

static inline bool petta_has_higher_arity_rule(const PettaTcalcEngine *eng, const char *op, uint32_t arity) {
    bool has_higher = false;
    for (uint32_t r = 0; r < eng->nrules; r++) {
        if (eng->rules[r].removed) continue;
        if (eng->rules[r].lhs->kind == PETTA_ATOM_EXPR &&
            eng->rules[r].lhs->arity > 0 &&
            eng->rules[r].lhs->args[0]->kind == PETTA_ATOM_SYM &&
            strcmp(eng->rules[r].lhs->args[0]->text, op) == 0) {
            if (eng->rules[r].arity == arity) return false;
            if (eng->rules[r].arity > arity) has_higher = true;
        }
    }
    return has_higher;
}

static inline bool petta_atom_as_double(const PettaAtom *a, double *out_d, bool *out_is_float) {
    if (!a) return false;
    if (a->kind == PETTA_ATOM_INT) {
        *out_d = (double)a->ival;
        *out_is_float = false;
        return true;
    }
    if (a->kind == PETTA_ATOM_SYM) {
        if (strcmp(a->text, "pi") == 0) {
            *out_d = 3.14159265358979323846;
            *out_is_float = true;
            return true;
        }
        if (strcmp(a->text, "inf") == 0) {
            *out_d = HUGE_VAL;
            *out_is_float = true;
            return true;
        }
        if (strcmp(a->text, "-inf") == 0) {
            *out_d = -HUGE_VAL;
            *out_is_float = true;
            return true;
        }
        if (strcmp(a->text, "nan") == 0) {
            *out_d = NAN;
            *out_is_float = true;
            return true;
        }
        const char *s = a->text;
        if ((*s == '-' || *s == '+') && s[1]) s++;
        if (isdigit((unsigned char)*s) &&
            (strchr(s, '.') != NULL || strchr(s, 'e') != NULL || strchr(s, 'E') != NULL)) {
            char *endp = NULL;
            double v = strtod(a->text, &endp);
            if (endp && endp != a->text && *endp == '\0') {
                *out_d = v;
                *out_is_float = true;
                return true;
            }
        }
    }
    return false;
}

static inline int64_t petta_math_trunc(double d) { return (int64_t)d; }
static inline int64_t petta_math_floor(double d) {
    int64_t t = (int64_t)d;
    return (d < (double)t) ? (t - 1) : t;
}
static inline int64_t petta_math_ceil(double d) {
    int64_t t = (int64_t)d;
    return (d > (double)t) ? (t + 1) : t;
}
static inline int64_t petta_math_round(double d) {
    return (int64_t)(d >= 0.0 ? (d + 0.5) : (d - 0.5));
}
static inline double petta_math_sqrt(double d) {
    if (d < 0.0) return __builtin_nan("");
    if (d == 0.0 || __builtin_isinf(d) || __builtin_isnan(d)) return d;
    double x = d > 1.0 ? d : 1.0;
    for (int i = 0; i < 32; i++) x = 0.5 * (x + d / x);
    return x;
}
static inline double petta_math_ln(double d) {
    if (d < 0.0) return __builtin_nan("");
    if (d == 0.0) return -__builtin_huge_val();
    if (__builtin_isinf(d) || __builtin_isnan(d)) return d;
    int k = 0;
    while (d > 2.0) { d *= 0.5; k++; }
    while (d < 0.5) { d *= 2.0; k--; }
    double y = (d - 1.0) / (d + 1.0);
    double y2 = y * y, term = y, sum = 0.0;
    for (int n = 1; n <= 39; n += 2) { sum += term / (double)n; term *= y2; }
    return 2.0 * sum + (double)k * 0.69314718055994530942;
}
static inline double petta_math_exp(double x) {
    if (__builtin_isnan(x)) return x;
    if (x > 709.0) return __builtin_huge_val();
    if (x < -709.0) return 0.0;
    int k = (int)(x / 0.69314718055994530942);
    double r = x - (double)k * 0.69314718055994530942;
    double term = 1.0, sum = 1.0;
    for (int n = 1; n <= 28; n++) { term *= r / (double)n; sum += term; }
    if (k >= 0) { for (int i = 0; i < k; i++) sum *= 2.0; }
    else { for (int i = 0; i < -k; i++) sum *= 0.5; }
    return sum;
}
static inline double petta_math_pow(double a, double b) {
    if (b == 0.0) return 1.0;
    if (a == 0.0) return b > 0.0 ? 0.0 : __builtin_huge_val();
    int64_t bi = (int64_t)b;
    if ((double)bi == b && bi >= -64 && bi <= 64) {
        double r = 1.0;
        int64_t e = bi >= 0 ? bi : -bi;
        for (int64_t i = 0; i < e; i++) r *= a;
        return bi >= 0 ? r : (1.0 / r);
    }
    if (a < 0.0) return __builtin_nan("");
    return petta_math_exp(b * petta_math_ln(a));
}
static inline double petta_math_sin(double x) {
    if (__builtin_isnan(x) || __builtin_isinf(x)) return __builtin_nan("");
    const double two_pi = 6.28318530717958647692;
    int64_t q = (int64_t)(x / two_pi);
    x -= (double)q * two_pi;
    double term = x, sum = x, x2 = -x * x;
    for (int n = 2; n <= 26; n += 2) {
        term *= x2 / ((double)n * (double)(n + 1));
        sum += term;
    }
    return __builtin_fabs(sum) < 1e-15 ? 0.0 : sum;
}
static inline double petta_math_cos(double x) {
    if (__builtin_isnan(x) || __builtin_isinf(x)) return __builtin_nan("");
    const double two_pi = 6.28318530717958647692;
    int64_t q = (int64_t)(x / two_pi);
    x -= (double)q * two_pi;
    double term = 1.0, sum = 1.0, x2 = -x * x;
    for (int n = 1; n <= 25; n += 2) {
        term *= x2 / ((double)n * (double)(n + 1));
        sum += term;
    }
    return __builtin_fabs(sum) < 1e-15 ? 0.0 : sum;
}
static inline double petta_math_tan(double x) {
    return petta_math_sin(x) / petta_math_cos(x);
}
static inline double petta_math_atan(double x) {
    if (__builtin_isnan(x)) return x;
    if (x == 0.0) return 0.0;
    bool neg = x < 0.0;
    if (neg) x = -x;
    bool inv = x > 1.0;
    if (inv) x = 1.0 / x;
    int folds = 0;
    while (x > 0.2679491924311227) {
        x = (x * 1.7320508075688772 - 1.0) / (1.7320508075688772 + x);
        folds++;
    }
    double x2 = -x * x, term = x, sum = 0.0;
    for (int n = 1; n <= 35; n += 2) { sum += term / (double)n; term *= x2; }
    sum += (double)folds * 0.52359877559829887308;
    if (inv) sum = 1.57079632679489661923 - sum;
    return neg ? -sum : sum;
}
static inline double petta_math_asin(double x) {
    if (x < -1.0 || x > 1.0 || __builtin_isnan(x)) return __builtin_nan("");
    if (x == 1.0) return 1.57079632679489661923;
    if (x == -1.0) return -1.57079632679489661923;
    return petta_math_atan(x / petta_math_sqrt(1.0 - x * x));
}
static inline double petta_math_acos(double x) {
    if (x < -1.0 || x > 1.0 || __builtin_isnan(x)) return __builtin_nan("");
    return 1.57079632679489661923 - petta_math_asin(x);
}

static inline PettaAtom *petta_atom_float(double d) {
    if (__builtin_isinf(d)) return petta_atom_sym(d < 0 ? "-inf" : "inf");
    if (__builtin_isnan(d)) return petta_atom_sym("nan");
    char buf[64];
    snprintf(buf, sizeof(buf), "%.16g", d);
    if (strtod(buf, NULL) != d) {
        snprintf(buf, sizeof(buf), "%.17g", d);
    }
    if (!strchr(buf, '.') && !strchr(buf, 'e') && !strchr(buf, 'E')) {
        strncat(buf, ".0", sizeof(buf) - strlen(buf) - 1);
    }
    return petta_atom_sym(buf);
}

static inline bool petta_atom_is_error(const PettaAtom *a) {
    if (!a) return false;
    if (a->kind == PETTA_ATOM_SYM && strcmp(a->text, "Error") == 0) return true;
    return (a->kind == PETTA_ATOM_EXPR && a->arity >= 1 &&
            a->args[0]->kind == PETTA_ATOM_SYM && strcmp(a->args[0]->text, "Error") == 0);
}

static inline const char *petta_atom_metatype_str(const PettaAtom *v) {
    if (!v) return "Symbol";
    if (v->kind == PETTA_ATOM_VAR) return "Variable";
    if (v->kind == PETTA_ATOM_EXPR) return "Expression";
    if (v->kind == PETTA_ATOM_INT || v->kind == PETTA_ATOM_STR) return "Grounded";
    if (v->kind == PETTA_ATOM_SYM) {
        double d = 0.0;
        bool is_f = false;
        if (petta_atom_is_truthy(v) || petta_atom_is_falsy(v) || v->text[0] == '&' ||
            petta_atom_as_double(v, &d, &is_f))
            return "Grounded";
    }
    return "Symbol";
}

static inline PettaAtom *petta_builtin_op_type(const char *op) {
    const char *src = NULL;
    if (strcmp(op, "+") == 0 || strcmp(op, "-") == 0 || strcmp(op, "*") == 0 ||
        strcmp(op, "/") == 0 || strcmp(op, "%") == 0 || strcmp(op, "pow-math") == 0 ||
        strcmp(op, "log-math") == 0 || strcmp(op, "min") == 0 || strcmp(op, "max") == 0) {
        src = "(-> Number Number Number)";
    } else if (strcmp(op, "<") == 0 || strcmp(op, "<=") == 0 ||
               strcmp(op, ">") == 0 || strcmp(op, ">=") == 0) {
        src = "(-> Number Number Bool)";
    } else if (strcmp(op, "==") == 0 || strcmp(op, "!=") == 0) {
        src = "(-> $a $b Bool)";
    } else if (strcmp(op, "sqrt-math") == 0 || strcmp(op, "abs-math") == 0 ||
               strcmp(op, "trunc-math") == 0 || strcmp(op, "ceil-math") == 0 ||
               strcmp(op, "floor-math") == 0 || strcmp(op, "round-math") == 0 ||
               strcmp(op, "sin-math") == 0 || strcmp(op, "asin-math") == 0 ||
               strcmp(op, "cos-math") == 0 || strcmp(op, "acos-math") == 0 ||
               strcmp(op, "tan-math") == 0 || strcmp(op, "atan-math") == 0 ||
               strcmp(op, "exp") == 0) {
        src = "(-> Number Number)";
    } else if (strcmp(op, "min-atom") == 0 || strcmp(op, "max-atom") == 0) {
        src = "(-> $a Number)";
    } else if (strcmp(op, "isnan-math") == 0 || strcmp(op, "isinf-math") == 0) {
        src = "(-> Number Bool)";
    } else if (strcmp(op, "and") == 0 || strcmp(op, "or") == 0 || strcmp(op, "xor") == 0) {
        src = "(-> Bool Bool Bool)";
    } else if (strcmp(op, "not") == 0) {
        src = "(-> Bool Bool)";
    }
    if (!src) return NULL;
    const char *p = src;
    return petta_parse_expr(&p);
}

static void petta_get_type_candidates_ex(
    PettaTcalcEngine *eng,
    const PettaAtom *x,
    PettaValList *out_types,
    PettaEnv *out_val_envs,
    uint32_t *out_val_env_count,
    uint32_t *out_val_env_cap);

static void petta_push_type_cand(
    PettaValList *out_types,
    PettaEnv *out_val_envs,
    uint32_t *out_val_env_count,
    uint32_t *out_val_env_cap,
    PettaAtom *type_atom,
    const PettaEnv *venv)
{
    petta_vallist_push_take(out_types, type_atom);
    if (out_val_envs && out_val_env_count && out_val_env_cap) {
        if (*out_val_env_count >= *out_val_env_cap) {
            return;
        }
        out_val_envs[(*out_val_env_count)++] = venv ? petta_env_clone(venv) : (PettaEnv){0};
    }
}

static void petta_match_fn_type_args(
    PettaTcalcEngine *eng,
    const PettaAtom *x,
    const PettaAtom *arrow,
    uint32_t arg_idx,
    const PettaEnv *tenv,
    const PettaEnv *venv,
    PettaValList *out_types,
    PettaEnv *out_val_envs,
    uint32_t *out_val_env_count,
    uint32_t *out_val_env_cap)
{
    if (arg_idx >= x->arity) {
        PettaAtom *ret_sub = petta_subst_env(arrow->args[x->arity], tenv);
        petta_push_type_cand(out_types, out_val_envs, out_val_env_count, out_val_env_cap, ret_sub, venv);
        return;
    }
    const PettaAtom *p_raw = arrow->args[arg_idx];
    const PettaAtom *arg = x->args[arg_idx];
    if (p_raw->kind == PETTA_ATOM_SYM && strcmp(p_raw->text, "%Undefined%") == 0) {
        petta_match_fn_type_args(eng, x, arrow, arg_idx + 1u, tenv, venv,
                                 out_types, out_val_envs, out_val_env_count, out_val_env_cap);
        return;
    }
    if (arg->kind == PETTA_ATOM_VAR) {
        petta_match_fn_type_args(eng, x, arrow, arg_idx + 1u, tenv, venv,
                                 out_types, out_val_envs, out_val_env_count, out_val_env_cap);
        return;
    }
    PettaAtom *req = petta_subst_env(p_raw, tenv);
    PettaValList acands;
    petta_vallist_init(&acands);
    PettaEnv avenvs[16];
    memset(avenvs, 0, sizeof(avenvs));
    uint32_t av_cnt = 0, av_cap = 16;
    PettaAtom *arg_sub = petta_subst_env(arg, venv);
    petta_get_type_candidates_ex(eng, arg_sub, &acands, avenvs, &av_cnt, &av_cap);
    petta_atom_free(arg_sub);

    if (req->kind == PETTA_ATOM_VAR) {
        if (acands.count > 0) {
            for (uint32_t c = 0; c < acands.count; c++) {
                PettaEnv tenv2 = petta_env_clone(tenv);
                petta_env_bind(&tenv2, req->text, acands.items[c]);
                PettaEnv venv2 = petta_env_clone(venv);
                if (c < av_cnt) {
                    for (uint32_t b = 0; b < avenvs[c].nbinds; b++)
                        petta_env_bind(&venv2, avenvs[c].binds[b].var, avenvs[c].binds[b].val);
                }
                petta_match_fn_type_args(eng, x, arrow, arg_idx + 1u, &tenv2, &venv2,
                                         out_types, out_val_envs, out_val_env_count, out_val_env_cap);
                petta_env_free(&venv2);
                petta_env_free(&tenv2);
            }
        } else {
            PettaEnv tenv2 = petta_env_clone(tenv);
            PettaAtom *undef = petta_atom_sym("%Undefined%");
            petta_env_bind(&tenv2, req->text, undef);
            petta_atom_free(undef);
            petta_match_fn_type_args(eng, x, arrow, arg_idx + 1u, &tenv2, venv,
                                     out_types, out_val_envs, out_val_env_count, out_val_env_cap);
            petta_env_free(&tenv2);
        }
    } else if (req->kind == PETTA_ATOM_SYM && strcmp(req->text, "%Undefined%") == 0) {
        if (acands.count == 0) {
            petta_match_fn_type_args(eng, x, arrow, arg_idx + 1u, tenv, venv,
                                     out_types, out_val_envs, out_val_env_count, out_val_env_cap);
        } else {
            for (uint32_t c = 0; c < acands.count; c++) {
                if (acands.items[c]->kind == PETTA_ATOM_SYM &&
                    strcmp(acands.items[c]->text, "%Undefined%") == 0) {
                    PettaEnv venv2 = petta_env_clone(venv);
                    if (c < av_cnt) {
                        for (uint32_t b = 0; b < avenvs[c].nbinds; b++)
                            petta_env_bind(&venv2, avenvs[c].binds[b].var, avenvs[c].binds[b].val);
                    }
                    petta_match_fn_type_args(eng, x, arrow, arg_idx + 1u, tenv, &venv2,
                                             out_types, out_val_envs, out_val_env_count, out_val_env_cap);
                    petta_env_free(&venv2);
                }
            }
        }
    } else {
        for (uint32_t c = 0; c < acands.count; c++) {
            PettaEnv tenv2 = petta_env_clone(tenv);
            if (petta_unify_atoms(req, acands.items[c], &tenv2)) {
                PettaEnv venv2 = petta_env_clone(venv);
                if (c < av_cnt) {
                    for (uint32_t b = 0; b < avenvs[c].nbinds; b++)
                        petta_env_bind(&venv2, avenvs[c].binds[b].var, avenvs[c].binds[b].val);
                }
                petta_match_fn_type_args(eng, x, arrow, arg_idx + 1u, &tenv2, &venv2,
                                         out_types, out_val_envs, out_val_env_count, out_val_env_cap);
                petta_env_free(&venv2);
            }
            petta_env_free(&tenv2);
        }
    }

    for (uint32_t c = 0; c < av_cnt; c++) petta_env_free(&avenvs[c]);
    petta_vallist_free(&acands);
    petta_atom_free(req);
}

static void petta_get_type_candidates_ex(
    PettaTcalcEngine *eng,
    const PettaAtom *x,
    PettaValList *out_types,
    PettaEnv *out_val_envs,
    uint32_t *out_val_env_count,
    uint32_t *out_val_env_cap)
{
    if (!x || eng->status != PETTA_STATUS_OK) return;

    /* Also check user-defined `(= (get-type pat) rhs)` rules if any exist */
    if (petta_has_user_rule(eng, "get-type", 2)) {
        PettaAtom *gt_args[2] = { petta_atom_sym("get-type"), petta_atom_clone(x) };
        PettaAtom *gt_call = petta_atom_expr(2, gt_args);
        for (uint32_t r = 0; r < eng->nrules && eng->status == PETTA_STATUS_OK; r++) {
            if (eng->rules[r].removed || eng->rules[r].arity != 2u) continue;
            if (eng->rules[r].lhs->args[0]->kind != PETTA_ATOM_SYM ||
                strcmp(eng->rules[r].lhs->args[0]->text, "get-type") != 0) continue;
            PettaEnv renv;
            if (petta_match_pattern(eng->rules[r].lhs, gt_call, &renv)) {
                PettaAtom *rhs_inst = petta_subst_env(eng->rules[r].rhs, &renv);
                petta_env_free(&renv);
                PettaValList rvals;
                petta_vallist_init(&rvals);
                petta_eval_expr(eng, rhs_inst, &rvals);
                petta_atom_free(rhs_inst);
                for (uint32_t k = 0; k < rvals.count; k++) {
                    if (!petta_atom_is_error(rvals.items[k])) {
                        petta_push_type_cand(out_types, out_val_envs, out_val_env_count, out_val_env_cap,
                                             petta_atom_clone(rvals.items[k]), NULL);
                    }
                }
                petta_vallist_free(&rvals);
            }
        }
        petta_atom_free(gt_call);
    }

    if (x->kind == PETTA_ATOM_INT) {
        petta_push_type_cand(out_types, out_val_envs, out_val_env_count, out_val_env_cap,
                             petta_atom_sym("Number"), NULL);
        return;
    }
    if (x->kind == PETTA_ATOM_SYM) {
        double d = 0.0;
        bool is_f = false;
        if (petta_atom_as_double(x, &d, &is_f)) {
            petta_push_type_cand(out_types, out_val_envs, out_val_env_count, out_val_env_cap,
                                 petta_atom_sym("Number"), NULL);
            return;
        }
        if (petta_atom_is_truthy(x) || petta_atom_is_falsy(x)) {
            petta_push_type_cand(out_types, out_val_envs, out_val_env_count, out_val_env_cap,
                                 petta_atom_sym("Bool"), NULL);
            return;
        }
    }
    if (x->kind == PETTA_ATOM_VAR) {
        petta_push_type_cand(out_types, out_val_envs, out_val_env_count, out_val_env_cap,
                             petta_atom_var("z"), NULL);
        return;
    }
    if (x->kind == PETTA_ATOM_STR) {
        petta_push_type_cand(out_types, out_val_envs, out_val_env_count, out_val_env_cap,
                             petta_atom_sym("String"), NULL);
        return;
    }

    if (x->kind == PETTA_ATOM_EXPR && x->arity >= 1) {
        uint32_t before_fn = out_types->count;
        const PettaAtom *f = x->args[0];
        if (f->kind == PETTA_ATOM_SYM) {
            bool found_sig = false;
            for (uint32_t i = 0; i < eng->nstore; i++) {
                if (!eng->store[i].alive) continue;
                if (!petta_space_matches(&eng->store[i], "&self")) continue;
                const PettaAtom *a = eng->store[i].atom;
                if (a->kind == PETTA_ATOM_EXPR && a->arity == 3 &&
                    a->args[0]->kind == PETTA_ATOM_SYM && strcmp(a->args[0]->text, ":") == 0 &&
                    a->args[1]->kind == PETTA_ATOM_SYM && strcmp(a->args[1]->text, f->text) == 0 &&
                    a->args[2]->kind == PETTA_ATOM_EXPR && a->args[2]->arity == x->arity + 1u &&
                    a->args[2]->args[0]->kind == PETTA_ATOM_SYM &&
                    strcmp(a->args[2]->args[0]->text, "->") == 0) {
                    found_sig = true;
                    PettaEnv tenv = {0}, venv = {0};
                    petta_match_fn_type_args(eng, x, a->args[2], 1u, &tenv, &venv,
                                             out_types, out_val_envs, out_val_env_count, out_val_env_cap);
                    petta_env_free(&tenv);
                    petta_env_free(&venv);
                }
            }
            if (!found_sig) {
                PettaAtom *btype = petta_builtin_op_type(f->text);
                if (btype && btype->kind == PETTA_ATOM_EXPR && btype->arity == x->arity + 1u) {
                    PettaEnv tenv = {0}, venv = {0};
                    petta_match_fn_type_args(eng, x, btype, 1u, &tenv, &venv,
                                             out_types, out_val_envs, out_val_env_count, out_val_env_cap);
                    petta_env_free(&tenv);
                    petta_env_free(&venv);
                }
                petta_atom_free(btype);
            }
        }
        /* Also check direct `(: pat T)` in `&self` matching expression `x` */
        for (uint32_t i = 0; i < eng->nstore; i++) {
            if (!eng->store[i].alive) continue;
            if (!petta_space_matches(&eng->store[i], "&self")) continue;
            const PettaAtom *a = eng->store[i].atom;
            if (a->kind == PETTA_ATOM_EXPR && a->arity == 3 &&
                a->args[0]->kind == PETTA_ATOM_SYM && strcmp(a->args[0]->text, ":") == 0 &&
                a->args[1]->kind == PETTA_ATOM_EXPR) {
                PettaEnv menv;
                if (petta_match_pattern(a->args[1], x, &menv)) {
                    PettaAtom *tsub = petta_subst_env(a->args[2], &menv);
                    petta_push_type_cand(out_types, out_val_envs, out_val_env_count, out_val_env_cap,
                                         tsub, &menv);
                    petta_env_free(&menv);
                }
            }
        }
        /* If no function type or pattern type matched, map `get-type` across tuple elements */
        if (out_types->count == before_fn && x->arity <= 8u) {
            PettaValList elists[8];
            uint32_t idx[8];
            for (uint32_t k = 0; k < x->arity; k++) {
                petta_vallist_init(&elists[k]);
                idx[k] = 0;
                petta_get_type_candidates_ex(eng, x->args[k], &elists[k], NULL, NULL, NULL);
                if (elists[k].count == 0) {
                    petta_vallist_push_take(&elists[k], petta_atom_sym("%Undefined%"));
                }
            }
            while (true) {
                PettaAtom *targs[8];
                for (uint32_t k = 0; k < x->arity; k++) {
                    targs[k] = petta_atom_clone(elists[k].items[idx[k]]);
                }
                petta_push_type_cand(out_types, out_val_envs, out_val_env_count, out_val_env_cap,
                                     petta_atom_expr(x->arity, targs), NULL);
                int32_t pos = (int32_t)x->arity - 1;
                while (pos >= 0) {
                    idx[pos]++;
                    if (idx[pos] < elists[pos].count) break;
                    idx[pos] = 0;
                    pos--;
                }
                if (pos < 0) break;
            }
            for (uint32_t k = 0; k < x->arity; k++) petta_vallist_free(&elists[k]);
        }
        return;
    }

    if (x->kind == PETTA_ATOM_SYM) {
        uint32_t before_sym = out_types->count;
        for (uint32_t i = 0; i < eng->nstore; i++) {
            if (!eng->store[i].alive) continue;
            if (!petta_space_matches(&eng->store[i], "&self")) continue;
            const PettaAtom *a = eng->store[i].atom;
            if (a->kind == PETTA_ATOM_EXPR && a->arity == 3 &&
                a->args[0]->kind == PETTA_ATOM_SYM && strcmp(a->args[0]->text, ":") == 0 &&
                a->args[1]->kind == PETTA_ATOM_SYM && strcmp(a->args[1]->text, x->text) == 0) {
                petta_push_type_cand(out_types, out_val_envs, out_val_env_count, out_val_env_cap,
                                     petta_atom_clone(a->args[2]), NULL);
            }
        }
        if (out_types->count == before_sym) {
            PettaAtom *btype = petta_builtin_op_type(x->text);
            if (btype) {
                petta_push_type_cand(out_types, out_val_envs, out_val_env_count, out_val_env_cap,
                                     btype, NULL);
            }
        }
    }
}

static bool petta_check_single_val_type(
    PettaTcalcEngine *eng,
    const PettaAtom *val,
    const PettaAtom *raw_type,
    const PettaAtom *call_term,
    const PettaAtom *arrow,
    uint32_t next_idx,
    const PettaAtom *out_val,
    const PettaEnv *tenv);

static bool petta_typecheck_arrow_step(
    PettaTcalcEngine *eng,
    const PettaAtom *call_term,
    const PettaAtom *arrow,
    uint32_t idx,
    const PettaAtom *out_val,
    const PettaEnv *tenv)
{
    if (idx < call_term->arity) {
        return petta_check_single_val_type(
            eng, call_term->args[idx], arrow->args[idx], call_term, arrow, idx + 1u, out_val, tenv);
    }
    if (!out_val) return true;
    return petta_check_single_val_type(
        eng, out_val, arrow->args[call_term->arity], call_term, arrow, call_term->arity + 1u, NULL, tenv);
}

static bool petta_check_single_val_type(
    PettaTcalcEngine *eng,
    const PettaAtom *val,
    const PettaAtom *raw_type,
    const PettaAtom *call_term,
    const PettaAtom *arrow,
    uint32_t next_idx,
    const PettaAtom *out_val,
    const PettaEnv *tenv)
{
    if (raw_type->kind == PETTA_ATOM_SYM &&
        (strcmp(raw_type->text, "Atom") == 0 ||
         strcmp(raw_type->text, "%Undefined%") == 0 ||
         strcmp(raw_type->text, "_") == 0)) {
        return (next_idx <= call_term->arity)
            ? petta_typecheck_arrow_step(eng, call_term, arrow, next_idx, out_val, tenv)
            : true;
    }
    if (val->kind == PETTA_ATOM_VAR) {
        return (next_idx <= call_term->arity)
            ? petta_typecheck_arrow_step(eng, call_term, arrow, next_idx, out_val, tenv)
            : true;
    }
    PettaAtom *req = petta_subst_env(raw_type, tenv);
    PettaValList cands;
    petta_vallist_init(&cands);
    petta_get_type_candidates_ex(eng, val, &cands, NULL, NULL, NULL);
    bool ok = false;

    if (req->kind == PETTA_ATOM_VAR) {
        if (cands.count > 0) {
            for (uint32_t c = 0; c < cands.count && !ok; c++) {
                PettaEnv tenv2 = petta_env_clone(tenv);
                petta_env_bind(&tenv2, req->text, cands.items[c]);
                ok = (next_idx <= call_term->arity)
                    ? petta_typecheck_arrow_step(eng, call_term, arrow, next_idx, out_val, &tenv2)
                    : true;
                petta_env_free(&tenv2);
            }
        } else {
            PettaEnv tenv2 = petta_env_clone(tenv);
            PettaAtom *undef = petta_atom_sym("%Undefined%");
            petta_env_bind(&tenv2, req->text, undef);
            petta_atom_free(undef);
            ok = (next_idx <= call_term->arity)
                ? petta_typecheck_arrow_step(eng, call_term, arrow, next_idx, out_val, &tenv2)
                : true;
            petta_env_free(&tenv2);
        }
    } else if (req->kind == PETTA_ATOM_SYM && strcmp(req->text, "%Undefined%") == 0) {
        bool has_undef = (cands.count == 0);
        for (uint32_t c = 0; c < cands.count && !has_undef; c++) {
            if (cands.items[c]->kind == PETTA_ATOM_SYM &&
                strcmp(cands.items[c]->text, "%Undefined%") == 0)
                has_undef = true;
        }
        if (has_undef) {
            ok = (next_idx <= call_term->arity)
                ? petta_typecheck_arrow_step(eng, call_term, arrow, next_idx, out_val, tenv)
                : true;
        }
    } else if (cands.count > 0) {
        for (uint32_t c = 0; c < cands.count && !ok; c++) {
            PettaEnv tenv2 = petta_env_clone(tenv);
            if (petta_unify_atoms(req, cands.items[c], &tenv2)) {
                ok = (next_idx <= call_term->arity)
                    ? petta_typecheck_arrow_step(eng, call_term, arrow, next_idx, out_val, &tenv2)
                    : true;
            }
            petta_env_free(&tenv2);
        }
    } else {
        /* Fallback to get-metatype when get-type produces 0 candidates */
        PettaAtom *mt = petta_atom_sym(petta_atom_metatype_str(val));
        PettaEnv tenv2 = petta_env_clone(tenv);
        if (petta_unify_atoms(req, mt, &tenv2)) {
            ok = (next_idx <= call_term->arity)
                ? petta_typecheck_arrow_step(eng, call_term, arrow, next_idx, out_val, &tenv2)
                : true;
        }
        petta_env_free(&tenv2);
        petta_atom_free(mt);
    }

    petta_vallist_free(&cands);
    petta_atom_free(req);
    return ok;
}

static inline bool petta_call_has_arrow_sig(
    PettaTcalcEngine *eng,
    const char *head_name,
    uint32_t call_arity,
    bool *out_ret_is_atom)
{
    if (out_ret_is_atom) *out_ret_is_atom = false;
    bool any = false;
    for (uint32_t i = 0; i < eng->nstore; i++) {
        if (!eng->store[i].alive) continue;
        if (!petta_space_matches(&eng->store[i], "&self")) continue;
        const PettaAtom *a = eng->store[i].atom;
        if (a->kind == PETTA_ATOM_EXPR && a->arity == 3 &&
            a->args[0]->kind == PETTA_ATOM_SYM && strcmp(a->args[0]->text, ":") == 0 &&
            a->args[1]->kind == PETTA_ATOM_SYM && strcmp(a->args[1]->text, head_name) == 0 &&
            a->args[2]->kind == PETTA_ATOM_EXPR && a->args[2]->arity == call_arity + 1u &&
            a->args[2]->args[0]->kind == PETTA_ATOM_SYM &&
            strcmp(a->args[2]->args[0]->text, "->") == 0) {
            any = true;
            const PettaAtom *ret = a->args[2]->args[call_arity];
            if (out_ret_is_atom && ret->kind == PETTA_ATOM_SYM && strcmp(ret->text, "Atom") == 0) {
                *out_ret_is_atom = true;
            }
        }
    }
    return any;
}

static inline bool petta_typecheck_call_and_out(
    PettaTcalcEngine *eng,
    const PettaAtom *call_term,
    const PettaAtom *out_val)
{
    if (!call_term || call_term->arity == 0 || call_term->args[0]->kind != PETTA_ATOM_SYM)
        return true;
    const char *head_name = call_term->args[0]->text;
    bool has_sig = false;
    for (uint32_t i = 0; i < eng->nstore; i++) {
        if (!eng->store[i].alive) continue;
        if (!petta_space_matches(&eng->store[i], "&self")) continue;
        const PettaAtom *a = eng->store[i].atom;
        if (a->kind == PETTA_ATOM_EXPR && a->arity == 3 &&
            a->args[0]->kind == PETTA_ATOM_SYM && strcmp(a->args[0]->text, ":") == 0 &&
            a->args[1]->kind == PETTA_ATOM_SYM && strcmp(a->args[1]->text, head_name) == 0 &&
            a->args[2]->kind == PETTA_ATOM_EXPR && a->args[2]->arity == call_term->arity + 1u &&
            a->args[2]->args[0]->kind == PETTA_ATOM_SYM &&
            strcmp(a->args[2]->args[0]->text, "->") == 0) {
            has_sig = true;
            PettaEnv tenv = {0};
            bool ok = petta_typecheck_arrow_step(eng, call_term, a->args[2], 1u, out_val, &tenv);
            petta_env_free(&tenv);
            if (ok) return true;
        }
    }
    return !has_sig;
}

static inline bool petta_load_space_program(
    PettaTcalcEngine *eng,
    const char *space_name,
    const char *program_text,
    PettaValList *out_last_result);

static inline int petta_atom_cmp(const PettaAtom *a, const PettaAtom *b) {
    if (a == b) return 0;
    if (!a) return -1;
    if (!b) return 1;
    double da = 0.0, db = 0.0;
    bool fa = false, fb = false;
    bool na = petta_atom_as_double(a, &da, &fa);
    bool nb = petta_atom_as_double(b, &db, &fb);
    int ra = na ? 1 : (a->kind == PETTA_ATOM_EXPR ? 3 : 2);
    int rb = nb ? 1 : (b->kind == PETTA_ATOM_EXPR ? 3 : 2);
    if (ra != rb) return (ra < rb) ? -1 : 1;
    if (ra == 1) {
        if (da < db) return -1;
        if (da > db) return 1;
        return 0;
    }
    if (ra == 2) {
        return strcmp(a->text ? a->text : "", b->text ? b->text : "");
    }
    uint32_t m = (a->arity < b->arity) ? a->arity : b->arity;
    for (uint32_t i = 0; i < m; i++) {
        int c = petta_atom_cmp(a->args[i], b->args[i]);
        if (c != 0) return c;
    }
    return (a->arity < b->arity) ? -1 : (a->arity > b->arity ? 1 : 0);
}

static __attribute__((noinline)) bool petta_eval_builtin_atomop(
    PettaTcalcEngine *eng,
    const char *op,
    const PettaAtom *expr,
    PettaValList *out_vals)
{
    /* (empty) -> 0 results */
    if (strcmp(op, "empty") == 0 && expr->arity == 1) {
        return true;
    }

    /* (test <expr> <expected>) and assertEqual / assertAlphaEqual / assertEqualToResult / assertAlphaEqualToResult */
    if ((strcmp(op, "test") == 0 || strcmp(op, "assertEqual") == 0 ||
         strcmp(op, "assertAlphaEqual") == 0 || strcmp(op, "assertEqualToResult") == 0 ||
         strcmp(op, "assertAlphaEqualToResult") == 0) && expr->arity == 3) {
        bool is_to_res = (strcmp(op, "assertEqualToResult") == 0 ||
                          strcmp(op, "assertAlphaEqualToResult") == 0);
        bool is_assert_fn = (strcmp(op, "test") != 0);
        PettaValList alist;
        petta_vallist_init(&alist);
        petta_eval_expr(eng, expr->args[1], &alist);
        if (eng->status != PETTA_STATUS_OK) {
            petta_vallist_free(&alist);
            return true;
        }
        PettaAtom *actual_val = NULL;
        if (is_to_res || alist.count != 1) {
            actual_val = petta_atom_expr(alist.count, alist.items);
            free(alist.items);
            alist.items = NULL;
            alist.count = 0;
            alist.cap = 0;
        } else {
            actual_val = petta_atom_clone(alist.items[0]);
            petta_vallist_free(&alist);
        }
        PettaAtom *exp_val = NULL;
        if (is_to_res) {
            if (expr->args[2]->kind == PETTA_ATOM_EXPR) {
                exp_val = petta_atom_clone(expr->args[2]);
            } else {
                PettaAtom *one[1] = { petta_atom_clone(expr->args[2]) };
                exp_val = petta_atom_expr(1, one);
            }
        } else {
            PettaValList elist;
            petta_vallist_init(&elist);
            petta_eval_expr(eng, expr->args[2], &elist);
            if (eng->status != PETTA_STATUS_OK) {
                petta_vallist_free(&elist);
                petta_atom_free(actual_val);
                return true;
            }
            if (elist.count != 1) {
                exp_val = petta_atom_expr(elist.count, elist.items);
                free(elist.items);
                elist.items = NULL;
                elist.count = 0;
                elist.cap = 0;
            } else {
                exp_val = petta_atom_clone(elist.items[0]);
                petta_vallist_free(&elist);
            }
        }
        if (is_assert_fn) {
            bool ok = petta_atom_alpha_eq(actual_val, exp_val);
            petta_atom_free(actual_val);
            petta_atom_free(exp_val);
            petta_vallist_push_take(out_vals, petta_atom_sym(ok ? "True" : "False"));
            return true;
        }
        PettaAtom *targs[3] = { petta_atom_sym("test"), actual_val, exp_val };
        petta_vallist_push_take(out_vals, petta_atom_expr(3, targs));
        return true;
    }

    /* (once <expr>) -> first result only (with fast short-circuit for (once (match &space ...))) */
    if (strcmp(op, "once") == 0 && expr->arity == 2) {
        const PettaAtom *inner = expr->args[1];
        if (inner->kind == PETTA_ATOM_EXPR && inner->arity == 4 &&
            inner->args[0]->kind == PETTA_ATOM_SYM &&
            strcmp(inner->args[0]->text, "match") == 0 &&
            inner->args[1]->kind == PETTA_ATOM_SYM) {
            const char *space_name = inner->args[1]->text;
            const PettaAtom *pat = inner->args[2];
            const PettaAtom *tmpl = inner->args[3];
            if (!(pat->kind == PETTA_ATOM_EXPR && pat->arity >= 1 &&
                  pat->args[0]->kind == PETTA_ATOM_SYM && strcmp(pat->args[0]->text, ",") == 0)) {
                eng->subcalc_queries_run++;
                for (uint32_t i = 0; i < eng->nstore && eng->status == PETTA_STATUS_OK; i++) {
                    if ((i & 15u) == 15u) {
                        eng->steps_executed++;
                        if (eng->max_steps > 0 && eng->steps_executed >= eng->max_steps) {
                            eng->status = PETTA_STATUS_BUDGET_EXHAUSTED;
                            break;
                        }
                    }
                    if (!eng->store[i].alive || !tc_alive(eng->store[i].tc_occ)) continue;
                    if (!petta_space_matches(&eng->store[i], space_name)) continue;
                    PettaEnv menv;
                    if (petta_match_pattern(pat, eng->store[i].atom, &menv)) {
                        PettaAtom *inst = petta_subst_env(tmpl, &menv);
                        petta_env_free(&menv);
                        PettaValList vlist;
                        petta_vallist_init(&vlist);
                        petta_eval_expr(eng, inst, &vlist);
                        petta_atom_free(inst);
                        if (vlist.count > 0) {
                            petta_vallist_push_clone(out_vals, vlist.items[0]);
                            petta_vallist_free(&vlist);
                            return true;
                        }
                        petta_vallist_free(&vlist);
                    }
                }
                return true;
            }
        }
        PettaValList vlist;
        petta_vallist_init(&vlist);
        petta_eval_expr(eng, inner, &vlist);
        if (vlist.count > 0 && eng->status == PETTA_STATUS_OK) {
            petta_vallist_push_clone(out_vals, vlist.items[0]);
        }
        petta_vallist_free(&vlist);
        return true;
    }

    /* (progn e1 ... en) -> evaluate in sequence, return values of en */
    if (strcmp(op, "progn") == 0 && expr->arity >= 1) {
        if (expr->arity == 1) {
            petta_vallist_push_take(out_vals, petta_atom_expr(0, NULL));
            return true;
        }
        for (uint32_t i = 1; i + 1 < expr->arity && eng->status == PETTA_STATUS_OK; i++) {
            PettaValList tmp;
            petta_vallist_init(&tmp);
            petta_eval_expr(eng, expr->args[i], &tmp);
            bool empty_step = (tmp.count == 0);
            petta_vallist_free(&tmp);
            if (empty_step) return true;
        }
        if (eng->status == PETTA_STATUS_OK) {
            petta_eval_expr(eng, expr->args[expr->arity - 1u], out_vals);
        }
        return true;
    }

    /* (prog1 e1 e2 ... en) -> evaluate e1, then e2..en, return values of e1 */
    if (strcmp(op, "prog1") == 0 && expr->arity >= 2) {
        PettaValList first_vals;
        petta_vallist_init(&first_vals);
        petta_eval_expr(eng, expr->args[1], &first_vals);
        if (first_vals.count == 0 || eng->status != PETTA_STATUS_OK) {
            petta_vallist_free(&first_vals);
            return true;
        }
        for (uint32_t i = 2; i < expr->arity && eng->status == PETTA_STATUS_OK; i++) {
            PettaValList tmp;
            petta_vallist_init(&tmp);
            petta_eval_expr(eng, expr->args[i], &tmp);
            bool empty_step = (tmp.count == 0);
            petta_vallist_free(&tmp);
            if (empty_step) {
                petta_vallist_free(&first_vals);
                return true;
            }
        }
        for (uint32_t i = 0; i < first_vals.count; i++) {
            petta_vallist_push_clone(out_vals, first_vals.items[i]);
        }
        petta_vallist_free(&first_vals);
        return true;
    }

    /* (eval <expr>) / (evalc <expr> <space>) / (reduce <expr>) / (call <expr>) / (id <expr>) / (cut) / (nop ...) / (catch <expr>) / (|-> ...) */
    if (((strcmp(op, "eval") == 0 || strcmp(op, "reduce") == 0 || strcmp(op, "call") == 0) && expr->arity == 2 &&
         !petta_has_user_rule(eng, op, expr->arity)) ||
        (strcmp(op, "evalc") == 0 && expr->arity == 3 && !petta_has_user_rule(eng, op, expr->arity))) {
        PettaValList vlist;
        petta_vallist_init(&vlist);
        petta_eval_expr(eng, expr->args[1], &vlist);
        for (uint32_t i = 0; i < vlist.count && eng->status == PETTA_STATUS_OK; i++) {
            vlist.items[i]->nf_epoch = 0;
            petta_eval_expr(eng, vlist.items[i], out_vals);
        }
        petta_vallist_free(&vlist);
        return true;
    }
    if (strcmp(op, "catch") == 0 && expr->arity == 2) {
        PettaValList cvals;
        petta_vallist_init(&cvals);
        petta_eval_expr(eng, expr->args[1], &cvals);
        if (eng->status == PETTA_STATUS_FAULT) {
            eng->status = PETTA_STATUS_OK;
            eng->fault = PETTA_FAULT_NONE;
            petta_vallist_free(&cvals);
            PettaAtom *eargs[3] = {
                petta_atom_sym("Error"),
                petta_atom_sym("type_error"),
                petta_atom_sym("caught")
            };
            petta_vallist_push_take(out_vals, petta_atom_expr(3, eargs));
            return true;
        }
        for (uint32_t i = 0; i < cvals.count; i++) {
            petta_vallist_push_clone(out_vals, cvals.items[i]);
        }
        petta_vallist_free(&cvals);
        return true;
    }
    if (strcmp(op, "if-error") == 0 && expr->arity == 4) {
        PettaValList vlist;
        petta_vallist_init(&vlist);
        petta_eval_expr(eng, expr->args[1], &vlist);
        for (uint32_t i = 0; i < vlist.count && eng->status == PETTA_STATUS_OK; i++) {
            if (petta_atom_is_error(vlist.items[i])) {
                petta_eval_expr(eng, expr->args[2], out_vals);
            } else {
                petta_eval_expr(eng, expr->args[3], out_vals);
            }
        }
        petta_vallist_free(&vlist);
        return true;
    }
    if (strcmp(op, "return-on-error") == 0 && expr->arity == 3) {
        PettaValList vlist;
        petta_vallist_init(&vlist);
        petta_eval_expr(eng, expr->args[1], &vlist);
        for (uint32_t i = 0; i < vlist.count && eng->status == PETTA_STATUS_OK; i++) {
            if (petta_atom_is_error(vlist.items[i])) {
                petta_vallist_push_clone(out_vals, vlist.items[i]);
            } else {
                petta_eval_expr(eng, expr->args[2], out_vals);
            }
        }
        petta_vallist_free(&vlist);
        return true;
    }
    if (strcmp(op, "once") == 0 && expr->arity == 2 && !petta_has_user_rule(eng, op, expr->arity)) {
        PettaValList vlist;
        petta_vallist_init(&vlist);
        petta_eval_expr(eng, expr->args[1], &vlist);
        if (vlist.count > 0) {
            petta_vallist_push_clone(out_vals, vlist.items[0]);
        }
        petta_vallist_free(&vlist);
        return true;
    }
    if ((strcmp(op, "id") == 0 || strcmp(op, "unquote") == 0) &&
        expr->arity == 2 && !petta_has_user_rule(eng, op, expr->arity)) {
        petta_eval_expr(eng, expr->args[1], out_vals);
        return true;
    }
    if (strcmp(op, "|->") == 0 && expr->arity == 3) {
        petta_vallist_push_clone(out_vals, expr);
        return true;
    }
    if (strcmp(op, "cut") == 0 && expr->arity == 1) {
        eng->cut_fired = true;
        petta_vallist_push_take(out_vals, petta_atom_sym("True"));
        return true;
    }
    if (strcmp(op, "nop") == 0 && !petta_has_user_rule(eng, op, expr->arity)) {
        for (uint32_t i = 1; i < expr->arity && eng->status == PETTA_STATUS_OK; i++) {
            PettaValList tmp;
            petta_vallist_init(&tmp);
            petta_eval_expr(eng, expr->args[i], &tmp);
            petta_vallist_free(&tmp);
        }
        petta_vallist_push_take(out_vals, petta_atom_expr(0, NULL));
        return true;
    }

    /* (unify $target $pat $then $else) */
    if ((strcmp(op, "unify") == 0 || strcmp(op, "if-unify") == 0) && expr->arity == 5) {
        const PettaAtom *target = expr->args[1];
        const PettaAtom *pat = expr->args[2];
        const PettaAtom *then_br = expr->args[3];
        const PettaAtom *else_br = expr->args[4];
        if (target->kind == PETTA_ATOM_SYM && target->text[0] == '&') {
            const char *space_name = target->text;
            bool any_hit = false;
            for (uint32_t i = 0; i < eng->nstore && eng->status == PETTA_STATUS_OK; i++) {
                if (!eng->store[i].alive || !tc_alive(eng->store[i].tc_occ)) continue;
                if (!petta_space_matches(&eng->store[i], space_name)) continue;
                PettaEnv menv;
                if (petta_match_pattern(pat, eng->store[i].atom, &menv)) {
                    any_hit = true;
                    PettaAtom *inst = petta_subst_env(then_br, &menv);
                    petta_env_free(&menv);
                    petta_eval_expr(eng, inst, out_vals);
                    petta_atom_free(inst);
                }
            }
            if (!any_hit && eng->status == PETTA_STATUS_OK) {
                petta_eval_expr(eng, else_br, out_vals);
            }
            return true;
        }
        PettaValList tlist;
        petta_vallist_init(&tlist);
        petta_eval_expr(eng, target, &tlist);
        for (uint32_t i = 0; i < tlist.count && eng->status == PETTA_STATUS_OK; i++) {
            PettaEnv uenv;
            petta_env_init(&uenv);
            if (petta_unify_atoms(tlist.items[i], pat, &uenv)) {
                PettaAtom *inst = petta_subst_env(then_br, &uenv);
                petta_env_free(&uenv);
                petta_eval_expr(eng, inst, out_vals);
                petta_atom_free(inst);
            } else {
                petta_env_free(&uenv);
                petta_eval_expr(eng, else_br, out_vals);
            }
        }
        petta_vallist_free(&tlist);
        return true;
    }

    /* (if-equal $a $b $then $else) */
    if (strcmp(op, "if-equal") == 0 && expr->arity == 5) {
        PettaValList llist, rlist;
        petta_vallist_init(&llist);
        petta_vallist_init(&rlist);
        petta_eval_expr(eng, expr->args[1], &llist);
        petta_eval_expr(eng, expr->args[2], &rlist);
        for (uint32_t li = 0; li < llist.count && eng->status == PETTA_STATUS_OK; li++) {
            for (uint32_t ri = 0; ri < rlist.count && eng->status == PETTA_STATUS_OK; ri++) {
                if (petta_atom_alpha_eq(llist.items[li], rlist.items[ri])) {
                    petta_eval_expr(eng, expr->args[3], out_vals);
                } else {
                    petta_eval_expr(eng, expr->args[4], out_vals);
                }
            }
        }
        petta_vallist_free(&llist);
        petta_vallist_free(&rlist);
        return true;
    }

    /* (if-decons-expr $expr $hvar $tvar $then $else) */
    if (strcmp(op, "if-decons-expr") == 0 && expr->arity == 6) {
        PettaValList elist;
        petta_vallist_init(&elist);
        petta_eval_expr(eng, expr->args[1], &elist);
        for (uint32_t i = 0; i < elist.count && eng->status == PETTA_STATUS_OK; i++) {
            const PettaAtom *e = elist.items[i];
            if (e->kind == PETTA_ATOM_EXPR && e->arity >= 1) {
                uint32_t tlen = e->arity - 1u;
                PettaAtom **targs = tlen ? (PettaAtom **)calloc(tlen, sizeof(PettaAtom *)) : NULL;
                for (uint32_t k = 0; k < tlen; k++) targs[k] = petta_atom_clone(e->args[k + 1u]);
                PettaAtom *tail_a = petta_atom_expr(tlen, targs);
                free(targs);
                PettaEnv denv;
                petta_env_init(&denv);
                if (petta_match_pattern_inner(expr->args[2], e->args[0], &denv) &&
                    petta_match_pattern_inner(expr->args[3], tail_a, &denv)) {
                    PettaAtom *sub = petta_subst_env(expr->args[4], &denv);
                    petta_env_free(&denv);
                    petta_atom_free(tail_a);
                    petta_eval_expr(eng, sub, out_vals);
                    petta_atom_free(sub);
                } else {
                    petta_env_free(&denv);
                    petta_atom_free(tail_a);
                    petta_eval_expr(eng, expr->args[5], out_vals);
                }
            } else {
                petta_eval_expr(eng, expr->args[5], out_vals);
            }
        }
        petta_vallist_free(&elist);
        return true;
    }

    /* (maplist $fn $list) and (foldl $fn $list $acc) */
    if (strcmp(op, "maplist") == 0 && expr->arity == 3 && !petta_has_user_rule(eng, op, expr->arity)) {
        PettaAtom *fn_val = petta_eval_one(eng, expr->args[1]);
        PettaAtom *list_val = petta_eval_one(eng, expr->args[2]);
        if (list_val->kind == PETTA_ATOM_EXPR) {
            PettaAtom **margs = list_val->arity
                ? (PettaAtom **)calloc(list_val->arity, sizeof(PettaAtom *)) : NULL;
            for (uint32_t i = 0; i < list_val->arity && eng->status == PETTA_STATUS_OK; i++) {
                PettaAtom *step_expr = NULL;
                if (fn_val->kind == PETTA_ATOM_EXPR && fn_val->arity > 0 &&
                    !(fn_val->arity == 3 && fn_val->args[0]->kind == PETTA_ATOM_SYM &&
                      strcmp(fn_val->args[0]->text, "|->") == 0)) {
                    PettaAtom **fargs = (PettaAtom **)calloc(fn_val->arity + 1u, sizeof(PettaAtom *));
                    for (uint32_t k = 0; k < fn_val->arity; k++) fargs[k] = petta_atom_clone(fn_val->args[k]);
                    fargs[fn_val->arity] = petta_atom_clone(list_val->args[i]);
                    step_expr = petta_atom_expr(fn_val->arity + 1u, fargs);
                    free(fargs);
                } else {
                    PettaAtom *cargs[2] = { petta_atom_clone(fn_val), petta_atom_clone(list_val->args[i]) };
                    step_expr = petta_atom_expr(2, cargs);
                }
                margs[i] = petta_eval_one(eng, step_expr);
                petta_atom_free(step_expr);
            }
            PettaAtom *res = petta_atom_expr(list_val->arity, margs);
            free(margs);
            petta_atom_free(fn_val);
            petta_atom_free(list_val);
            petta_vallist_push_take(out_vals, res);
            return true;
        }
        petta_atom_free(fn_val);
        petta_atom_free(list_val);
        return false;
    }
    if (strcmp(op, "foldl") == 0 && expr->arity == 4 && !petta_has_user_rule(eng, op, expr->arity)) {
        PettaAtom *fn_val = petta_eval_one(eng, expr->args[1]);
        PettaAtom *list_val = petta_eval_one(eng, expr->args[2]);
        PettaAtom *acc_val = petta_eval_one(eng, expr->args[3]);
        if (list_val->kind == PETTA_ATOM_EXPR) {
            for (uint32_t i = 0; i < list_val->arity && eng->status == PETTA_STATUS_OK; i++) {
                PettaAtom *cargs[3] = {
                    petta_atom_clone(fn_val),
                    petta_atom_clone(list_val->args[i]),
                    petta_atom_clone(acc_val)
                };
                PettaAtom *step_expr = petta_atom_expr(3, cargs);
                PettaAtom *next_acc = petta_eval_one(eng, step_expr);
                petta_atom_free(step_expr);
                petta_atom_free(acc_val);
                acc_val = next_acc;
            }
        }
        petta_atom_free(fn_val);
        petta_atom_free(list_val);
        petta_vallist_push_take(out_vals, acc_val);
        return true;
    }

    /* Higher-order tuple operations: foldl-atom, map-atom, filter-atom */
    if (strcmp(op, "foldl-atom") == 0 && (expr->arity == 6 || expr->arity == 4)) {
        PettaAtom *list_val = petta_eval_one(eng, expr->args[1]);
        PettaAtom *acc_val = petta_eval_one(eng, expr->args[2]);
        if (list_val->kind == PETTA_ATOM_EXPR) {
            for (uint32_t i = 0; i < list_val->arity && eng->status == PETTA_STATUS_OK; i++) {
                PettaAtom *step_expr = NULL;
                if (expr->arity == 6) {
                    PettaEnv fenv;
                    petta_env_init(&fenv);
                    if (expr->args[3]->kind == PETTA_ATOM_VAR)
                        petta_env_bind(&fenv, expr->args[3]->text, acc_val);
                    if (expr->args[4]->kind == PETTA_ATOM_VAR)
                        petta_env_bind(&fenv, expr->args[4]->text, list_val->args[i]);
                    step_expr = petta_subst_env(expr->args[5], &fenv);
                    petta_env_free(&fenv);
                } else {
                    PettaAtom *cargs[3] = {
                        petta_atom_clone(expr->args[3]),
                        petta_atom_clone(acc_val),
                        petta_atom_clone(list_val->args[i])
                    };
                    step_expr = petta_atom_expr(3, cargs);
                }
                PettaAtom *next_acc = petta_eval_one(eng, step_expr);
                petta_atom_free(step_expr);
                petta_atom_free(acc_val);
                acc_val = next_acc;
            }
        }
        petta_atom_free(list_val);
        petta_vallist_push_take(out_vals, acc_val);
        return true;
    }
    if ((strcmp(op, "map-atom") == 0 || strcmp(op, "for-each-in-atom") == 0) &&
        (expr->arity == 4 || expr->arity == 3)) {
        PettaAtom *list_val = petta_eval_one(eng, expr->args[1]);
        if (list_val->kind == PETTA_ATOM_EXPR) {
            PettaAtom **margs = list_val->arity
                ? (PettaAtom **)calloc(list_val->arity, sizeof(PettaAtom *)) : NULL;
            for (uint32_t i = 0; i < list_val->arity && eng->status == PETTA_STATUS_OK; i++) {
                PettaAtom *step_expr = NULL;
                if (expr->arity == 4) {
                    PettaEnv menv;
                    petta_env_init(&menv);
                    if (expr->args[2]->kind == PETTA_ATOM_VAR)
                        petta_env_bind(&menv, expr->args[2]->text, list_val->args[i]);
                    step_expr = petta_subst_env(expr->args[3], &menv);
                    petta_env_free(&menv);
                } else {
                    const PettaAtom *fn = expr->args[2];
                    if (fn->kind == PETTA_ATOM_EXPR && fn->arity > 0 &&
                        !(fn->arity == 3 && fn->args[0]->kind == PETTA_ATOM_SYM &&
                          strcmp(fn->args[0]->text, "|->") == 0)) {
                        PettaAtom **fargs = (PettaAtom **)calloc(fn->arity + 1u, sizeof(PettaAtom *));
                        for (uint32_t k = 0; k < fn->arity; k++) fargs[k] = petta_atom_clone(fn->args[k]);
                        fargs[fn->arity] = petta_atom_clone(list_val->args[i]);
                        step_expr = petta_atom_expr(fn->arity + 1u, fargs);
                        free(fargs);
                    } else {
                        PettaAtom *cargs[2] = { petta_atom_clone(fn), petta_atom_clone(list_val->args[i]) };
                        step_expr = petta_atom_expr(2, cargs);
                    }
                }
                margs[i] = petta_eval_one(eng, step_expr);
                petta_atom_free(step_expr);
            }
            PettaAtom *res = petta_atom_expr(list_val->arity, margs);
            free(margs);
            petta_atom_free(list_val);
            petta_vallist_push_take(out_vals, res);
            return true;
        }
        petta_atom_free(list_val);
        return false;
    }
    if (strcmp(op, "forall") == 0 && expr->arity == 3) {
        PettaValList glist;
        petta_vallist_init(&glist);
        if (expr->args[1]->kind != PETTA_ATOM_EXPR) {
            PettaAtom *gcall_args[1] = { petta_atom_clone(expr->args[1]) };
            PettaAtom *gcall = petta_atom_expr(1, gcall_args);
            petta_eval_expr(eng, gcall, &glist);
            petta_atom_free(gcall);
        } else {
            petta_eval_expr(eng, expr->args[1], &glist);
        }
        PettaAtom *pred_fn = petta_eval_one(eng, expr->args[2]);
        bool all_ok = true;
        for (uint32_t i = 0; i < glist.count && eng->status == PETTA_STATUS_OK; i++) {
            PettaAtom *cargs[2] = { petta_atom_clone(pred_fn), petta_atom_clone(glist.items[i]) };
            PettaAtom *call = petta_atom_expr(2, cargs);
            PettaAtom *rval = petta_eval_one(eng, call);
            petta_atom_free(call);
            bool ok = petta_atom_is_truthy(rval);
            petta_atom_free(rval);
            if (!ok) {
                all_ok = false;
                break;
            }
        }
        petta_atom_free(pred_fn);
        petta_vallist_free(&glist);
        petta_vallist_push_take(out_vals, petta_atom_sym(all_ok ? "True" : "False"));
        return true;
    }
    if (strcmp(op, "foldall") == 0 && expr->arity == 4) {
        PettaAtom *acc = petta_eval_one(eng, expr->args[3]);
        PettaAtom *agg_fn = petta_eval_one(eng, expr->args[1]);
        PettaValList glist;
        petta_vallist_init(&glist);
        if (expr->args[2]->kind != PETTA_ATOM_EXPR) {
            PettaAtom *gcall_args[1] = { petta_atom_clone(expr->args[2]) };
            PettaAtom *gcall = petta_atom_expr(1, gcall_args);
            petta_eval_expr(eng, gcall, &glist);
            petta_atom_free(gcall);
        } else {
            petta_eval_expr(eng, expr->args[2], &glist);
        }
        for (uint32_t i = 0; i < glist.count && eng->status == PETTA_STATUS_OK; i++) {
            PettaAtom *cargs[3] = {
                petta_atom_clone(agg_fn),
                petta_atom_clone(acc),
                petta_atom_clone(glist.items[i])
            };
            PettaAtom *call = petta_atom_expr(3, cargs);
            PettaAtom *next_acc = petta_eval_one(eng, call);
            petta_atom_free(call);
            petta_atom_free(acc);
            acc = next_acc;
        }
        petta_atom_free(agg_fn);
        petta_vallist_free(&glist);
        petta_vallist_push_take(out_vals, acc);
        return true;
    }
    if (strcmp(op, "filter-atom") == 0 && (expr->arity == 4 || expr->arity == 3)) {
        PettaAtom *list_val = petta_eval_one(eng, expr->args[1]);
        if (list_val->kind == PETTA_ATOM_EXPR) {
            PettaValList kept;
            petta_vallist_init(&kept);
            for (uint32_t i = 0; i < list_val->arity && eng->status == PETTA_STATUS_OK; i++) {
                PettaAtom *step_expr = NULL;
                if (expr->arity == 4) {
                    PettaEnv fenv;
                    petta_env_init(&fenv);
                    if (expr->args[2]->kind == PETTA_ATOM_VAR)
                        petta_env_bind(&fenv, expr->args[2]->text, list_val->args[i]);
                    step_expr = petta_subst_env(expr->args[3], &fenv);
                    petta_env_free(&fenv);
                } else {
                    const PettaAtom *fn = expr->args[2];
                    if (fn->kind == PETTA_ATOM_EXPR && fn->arity > 0 &&
                        !(fn->arity == 3 && fn->args[0]->kind == PETTA_ATOM_SYM &&
                          strcmp(fn->args[0]->text, "|->") == 0)) {
                        PettaAtom **fargs = (PettaAtom **)calloc(fn->arity + 1u, sizeof(PettaAtom *));
                        for (uint32_t k = 0; k < fn->arity; k++) fargs[k] = petta_atom_clone(fn->args[k]);
                        fargs[fn->arity] = petta_atom_clone(list_val->args[i]);
                        step_expr = petta_atom_expr(fn->arity + 1u, fargs);
                        free(fargs);
                    } else {
                        PettaAtom *cargs[2] = { petta_atom_clone(fn), petta_atom_clone(list_val->args[i]) };
                        step_expr = petta_atom_expr(2, cargs);
                    }
                }
                PettaAtom *cval = petta_eval_one(eng, step_expr);
                petta_atom_free(step_expr);
                if (petta_atom_is_truthy(cval)) {
                    petta_vallist_push_clone(&kept, list_val->args[i]);
                }
                petta_atom_free(cval);
            }
            PettaAtom *res = petta_atom_expr(kept.count, kept.items);
            free(kept.items);
            petta_atom_free(list_val);
            petta_vallist_push_take(out_vals, res);
            return true;
        }
        petta_atom_free(list_val);
        return false;
    }

    /* Core Tuple / List / Reflection Atomops (cons-atom, cons, decons-atom, decons, car-atom, cdr-atom,
     * first-from-pair, second-from-pair, index-atom, size-atom, length, min-atom, max-atom,
     * =alpha, =@=, unique-atom, alpha-unique-atom, union-atom, intersection-atom, subtraction-atom,
     * is-member, is-alpha-member, exclude-item, append, reverse, is-var, is-expr, is-space, get-metatype) */
    if ((strcmp(op, "cons-atom") == 0 ||
         (strcmp(op, "cons") == 0 && !petta_has_user_rule(eng, op, expr->arity))) &&
        expr->arity == 3) {
        PettaValList hlist, tlist;
        petta_vallist_init(&hlist);
        petta_vallist_init(&tlist);
        petta_eval_expr(eng, expr->args[1], &hlist);
        petta_eval_expr(eng, expr->args[2], &tlist);
        for (uint32_t hi = 0; hi < hlist.count && eng->status == PETTA_STATUS_OK; hi++) {
            for (uint32_t ti = 0; ti < tlist.count && eng->status == PETTA_STATUS_OK; ti++) {
                PettaAtom *t = tlist.items[ti];
                if (t->kind == PETTA_ATOM_EXPR) {
                    PettaAtom **nargs = (PettaAtom **)calloc(t->arity + 1u, sizeof(PettaAtom *));
                    nargs[0] = petta_atom_clone(hlist.items[hi]);
                    for (uint32_t k = 0; k < t->arity; k++) nargs[k + 1u] = petta_atom_clone(t->args[k]);
                    petta_vallist_push_take(out_vals, petta_atom_expr(t->arity + 1u, nargs));
                    free(nargs);
                } else {
                    PettaAtom *cargs[3] = {
                        petta_atom_clone(expr->args[0]),
                        petta_atom_clone(hlist.items[hi]),
                        petta_atom_clone(t)
                    };
                    petta_vallist_push_take(out_vals, petta_atom_expr(3, cargs));
                }
            }
        }
        petta_vallist_free(&hlist);
        petta_vallist_free(&tlist);
        return true;
    }

    if ((strcmp(op, "decons-atom") == 0 ||
         (strcmp(op, "decons") == 0 && !petta_has_user_rule(eng, op, expr->arity))) &&
        expr->arity == 2) {
        PettaValList elist;
        petta_vallist_init(&elist);
        petta_eval_expr(eng, expr->args[1], &elist);
        for (uint32_t i = 0; i < elist.count && eng->status == PETTA_STATUS_OK; i++) {
            PettaAtom *e = elist.items[i];
            if (e->kind == PETTA_ATOM_EXPR && e->arity >= 1) {
                uint32_t tlen = e->arity - 1u;
                PettaAtom **targs = tlen ? (PettaAtom **)calloc(tlen, sizeof(PettaAtom *)) : NULL;
                for (uint32_t k = 0; k < tlen; k++) targs[k] = petta_atom_clone(e->args[k + 1u]);
                PettaAtom *pair[2] = { petta_atom_clone(e->args[0]), petta_atom_expr(tlen, targs) };
                free(targs);
                petta_vallist_push_take(out_vals, petta_atom_expr(2, pair));
            }
        }
        petta_vallist_free(&elist);
        return true;
    }

    if ((strcmp(op, "car-atom") == 0 || strcmp(op, "first-from-pair") == 0 ||
         (strcmp(op, "first") == 0 && !petta_has_user_rule(eng, op, expr->arity))) &&
        expr->arity == 2) {
        PettaValList elist;
        petta_vallist_init(&elist);
        petta_eval_expr(eng, expr->args[1], &elist);
        for (uint32_t i = 0; i < elist.count && eng->status == PETTA_STATUS_OK; i++) {
            PettaAtom *e = elist.items[i];
            if (e->kind == PETTA_ATOM_EXPR && e->arity >= 1) {
                petta_vallist_push_clone(out_vals, e->args[0]);
            }
        }
        petta_vallist_free(&elist);
        return true;
    }

    if (strcmp(op, "second-from-pair") == 0 && expr->arity == 2) {
        PettaValList elist;
        petta_vallist_init(&elist);
        petta_eval_expr(eng, expr->args[1], &elist);
        for (uint32_t i = 0; i < elist.count && eng->status == PETTA_STATUS_OK; i++) {
            PettaAtom *e = elist.items[i];
            if (e->kind == PETTA_ATOM_EXPR && e->arity >= 2) {
                petta_vallist_push_clone(out_vals, e->args[1]);
            }
        }
        petta_vallist_free(&elist);
        return true;
    }

    if (strcmp(op, "cdr-atom") == 0 && expr->arity == 2) {
        PettaValList elist;
        petta_vallist_init(&elist);
        petta_eval_expr(eng, expr->args[1], &elist);
        for (uint32_t i = 0; i < elist.count && eng->status == PETTA_STATUS_OK; i++) {
            PettaAtom *e = elist.items[i];
            if (e->kind == PETTA_ATOM_EXPR && e->arity >= 1) {
                uint32_t tlen = e->arity - 1u;
                PettaAtom **targs = tlen ? (PettaAtom **)calloc(tlen, sizeof(PettaAtom *)) : NULL;
                for (uint32_t k = 0; k < tlen; k++) targs[k] = petta_atom_clone(e->args[k + 1u]);
                petta_vallist_push_take(out_vals, petta_atom_expr(tlen, targs));
                free(targs);
            }
        }
        petta_vallist_free(&elist);
        return true;
    }

    if (strcmp(op, "index-atom") == 0 && expr->arity == 3) {
        PettaValList elist, ilist;
        petta_vallist_init(&elist);
        petta_vallist_init(&ilist);
        petta_eval_expr(eng, expr->args[1], &elist);
        petta_eval_expr(eng, expr->args[2], &ilist);
        for (uint32_t ei = 0; ei < elist.count && eng->status == PETTA_STATUS_OK; ei++) {
            PettaAtom *e = elist.items[ei];
            for (uint32_t ii = 0; ii < ilist.count && eng->status == PETTA_STATUS_OK; ii++) {
                PettaAtom *idx = ilist.items[ii];
                if (e->kind == PETTA_ATOM_EXPR && idx->kind == PETTA_ATOM_INT &&
                    idx->ival >= 0 && (uint64_t)idx->ival < (uint64_t)e->arity) {
                    petta_vallist_push_clone(out_vals, e->args[idx->ival]);
                }
            }
        }
        petta_vallist_free(&elist);
        petta_vallist_free(&ilist);
        return true;
    }

    if ((strcmp(op, "size-atom") == 0 ||
         (strcmp(op, "length") == 0 && !petta_has_user_rule(eng, op, expr->arity))) &&
        expr->arity == 2) {
        PettaValList elist;
        petta_vallist_init(&elist);
        petta_eval_expr(eng, expr->args[1], &elist);
        for (uint32_t i = 0; i < elist.count && eng->status == PETTA_STATUS_OK; i++) {
            PettaAtom *e = elist.items[i];
            if (e->kind == PETTA_ATOM_EXPR) {
                petta_vallist_push_take(out_vals, petta_atom_int((int64_t)e->arity));
            }
        }
        petta_vallist_free(&elist);
        return true;
    }

    if ((strcmp(op, "min-atom") == 0 || strcmp(op, "max-atom") == 0) && expr->arity == 2) {
        bool is_max = (strcmp(op, "max-atom") == 0);
        PettaValList elist;
        petta_vallist_init(&elist);
        petta_eval_expr(eng, expr->args[1], &elist);
        for (uint32_t i = 0; i < elist.count && eng->status == PETTA_STATUS_OK; i++) {
            PettaAtom *e = elist.items[i];
            if (e->kind != PETTA_ATOM_EXPR || e->arity == 0) {
                continue;
            }
            double best_d = 0.0;
            bool any_flt = false, f0 = false;
            if (!petta_atom_as_double(e->args[0], &best_d, &f0)) {
                eng->status = PETTA_STATUS_FAULT;
                eng->fault = PETTA_FAULT_TYPE;
                break;
            }
            if (f0) any_flt = true;
            PettaAtom *best_atom = e->args[0];
            bool ok_all = true;
            for (uint32_t k = 1; k < e->arity; k++) {
                double kd = 0.0;
                bool kf = false;
                if (!petta_atom_as_double(e->args[k], &kd, &kf)) {
                    eng->status = PETTA_STATUS_FAULT;
                    eng->fault = PETTA_FAULT_TYPE;
                    ok_all = false;
                    break;
                }
                if (kf) any_flt = true;
                if (is_max ? (kd > best_d) : (kd < best_d)) {
                    best_d = kd;
                    best_atom = e->args[k];
                }
            }
            if (!ok_all) break;
            if (any_flt && best_atom->kind != PETTA_ATOM_INT) {
                petta_vallist_push_clone(out_vals, best_atom);
            } else {
                petta_vallist_push_clone(out_vals, best_atom);
            }
        }
        petta_vallist_free(&elist);
        return true;
    }

    if ((strcmp(op, "sort-atom") == 0 ||
         ((strcmp(op, "msort") == 0 || strcmp(op, "sort") == 0) && !petta_has_user_rule(eng, op, expr->arity))) &&
        expr->arity == 2) {
        bool dedup = (strcmp(op, "sort") == 0);
        PettaValList elist;
        petta_vallist_init(&elist);
        petta_eval_expr(eng, expr->args[1], &elist);
        for (uint32_t i = 0; i < elist.count && eng->status == PETTA_STATUS_OK; i++) {
            PettaAtom *e = elist.items[i];
            if (e->kind != PETTA_ATOM_EXPR) continue;
            PettaAtom **sargs = e->arity > 0 ? (PettaAtom **)calloc(e->arity, sizeof(PettaAtom *)) : NULL;
            for (uint32_t k = 0; k < e->arity; k++) sargs[k] = petta_atom_clone(e->args[k]);
            for (uint32_t a = 0; a < e->arity; a++) {
                for (uint32_t b = a + 1; b < e->arity; b++) {
                    if (petta_atom_cmp(sargs[a], sargs[b]) > 0) {
                        PettaAtom *tmp = sargs[a];
                        sargs[a] = sargs[b];
                        sargs[b] = tmp;
                    }
                }
            }
            uint32_t out_n = e->arity;
            if (dedup && out_n > 1u) {
                uint32_t wr = 1u;
                for (uint32_t k = 1u; k < out_n; k++) {
                    if (petta_atom_cmp(sargs[wr - 1u], sargs[k]) == 0) {
                        petta_atom_free(sargs[k]);
                    } else {
                        sargs[wr++] = sargs[k];
                    }
                }
                out_n = wr;
            }
            PettaAtom *res = petta_atom_expr(out_n, sargs);
            free(sargs);
            petta_vallist_push_take(out_vals, res);
        }
        petta_vallist_free(&elist);
        return true;
    }

    if ((strcmp(op, "=alpha") == 0 || strcmp(op, "=@=") == 0) && expr->arity == 3) {
        PettaValList llist, rlist;
        petta_vallist_init(&llist);
        petta_vallist_init(&rlist);
        petta_eval_expr(eng, expr->args[1], &llist);
        petta_eval_expr(eng, expr->args[2], &rlist);
        for (uint32_t li = 0; li < llist.count && eng->status == PETTA_STATUS_OK; li++) {
            for (uint32_t ri = 0; ri < rlist.count && eng->status == PETTA_STATUS_OK; ri++) {
                bool eq = petta_atom_alpha_eq(llist.items[li], rlist.items[ri]);
                petta_vallist_push_take(out_vals, petta_atom_sym(eq ? "True" : "False"));
            }
        }
        petta_vallist_free(&llist);
        petta_vallist_free(&rlist);
        return true;
    }

    if ((strcmp(op, "unique-atom") == 0 || strcmp(op, "alpha-unique-atom") == 0 ||
         (strcmp(op, "list_to_set") == 0 && !petta_has_user_rule(eng, op, expr->arity))) &&
        expr->arity == 2) {
        bool use_alpha = (strcmp(op, "alpha-unique-atom") == 0);
        PettaValList elist;
        petta_vallist_init(&elist);
        petta_eval_expr(eng, expr->args[1], &elist);
        for (uint32_t i = 0; i < elist.count && eng->status == PETTA_STATUS_OK; i++) {
            PettaAtom *e = elist.items[i];
            if (e->kind == PETTA_ATOM_EXPR) {
                PettaValList u;
                petta_vallist_init(&u);
                for (uint32_t k = 0; k < e->arity; k++) {
                    bool seen = false;
                    for (uint32_t j = 0; j < u.count; j++) {
                        if (use_alpha ? petta_atom_alpha_eq(u.items[j], e->args[k])
                                      : petta_atom_eq(u.items[j], e->args[k])) {
                            seen = true;
                            break;
                        }
                    }
                    if (!seen) petta_vallist_push_clone(&u, e->args[k]);
                }
                PettaAtom *res = petta_atom_expr(u.count, u.items);
                free(u.items);
                petta_vallist_push_take(out_vals, res);
            }
        }
        petta_vallist_free(&elist);
        return true;
    }

    if (((strcmp(op, "/=\\") == 0 || strcmp(op, "\\=") == 0 || strcmp(op, "\\=/") == 0) && expr->arity == 3) ||
        ((strcmp(op, "/?\\") == 0 || strcmp(op, "\\?") == 0 || strcmp(op, "\\?/") == 0) && expr->arity == 4 &&
         expr->args[1]->kind == PETTA_ATOM_SYM && strcmp(expr->args[1]->text, "=") == 0)) {
        const PettaAtom *as_arg = (expr->arity == 4) ? expr->args[2] : expr->args[1];
        const PettaAtom *bs_arg = (expr->arity == 4) ? expr->args[3] : expr->args[2];
        int mode = (op[0] == '/') ? 0 : ((op[strlen(op) - 1] == '/') ? 2 : 1);
        PettaAtom *as_val = petta_eval_one(eng, as_arg);
        PettaAtom *bs_val = petta_eval_one(eng, bs_arg);
        if (as_val->kind == PETTA_ATOM_EXPR && bs_val->kind == PETTA_ATOM_EXPR) {
            PettaEnv uenv;
            petta_env_init(&uenv);
            PettaValList out;
            petta_vallist_init(&out);
            for (uint32_t i = 0; i < as_val->arity; i++) {
                PettaAtom *ai = petta_subst_env_trans(as_val->args[i], &uenv);
                bool matched = false;
                for (uint32_t j = 0; j < bs_val->arity; j++) {
                    PettaAtom *bj = petta_subst_env_trans(bs_val->args[j], &uenv);
                    PettaEnv tenv = petta_env_clone(&uenv);
                    if (petta_unify_atoms(ai, bj, &tenv)) {
                        petta_env_free(&uenv);
                        uenv = tenv;
                        matched = true;
                        petta_atom_free(bj);
                        break;
                    }
                    petta_env_free(&tenv);
                    petta_atom_free(bj);
                }
                PettaAtom *ai_fin = petta_subst_env_trans(ai, &uenv);
                petta_atom_free(ai);
                if (mode == 0 && matched) {
                    petta_vallist_push_take(&out, ai_fin);
                } else if ((mode == 1 || mode == 2) && !matched) {
                    petta_vallist_push_take(&out, ai_fin);
                } else {
                    petta_atom_free(ai_fin);
                }
            }
            if (mode == 2) {
                for (uint32_t j = 0; j < bs_val->arity; j++) {
                    petta_vallist_push_take(&out, petta_subst_env_trans(bs_val->args[j], &uenv));
                }
            }
            petta_env_free(&uenv);
            PettaAtom *res = petta_atom_expr(out.count, out.items);
            free(out.items);
            petta_atom_free(as_val);
            petta_atom_free(bs_val);
            petta_vallist_push_take(out_vals, res);
            return true;
        }
        petta_atom_free(as_val);
        petta_atom_free(bs_val);
    }

    if ((strcmp(op, "union-atom") == 0 || strcmp(op, "intersection-atom") == 0 ||
         strcmp(op, "subtraction-atom") == 0 ||
         (strcmp(op, "append") == 0 && !petta_has_user_rule(eng, op, expr->arity))) &&
        expr->arity == 3) {
        PettaValList llist, rlist;
        petta_vallist_init(&llist);
        petta_vallist_init(&rlist);
        petta_eval_expr(eng, expr->args[1], &llist);
        petta_eval_expr(eng, expr->args[2], &rlist);
        for (uint32_t li = 0; li < llist.count && eng->status == PETTA_STATUS_OK; li++) {
            PettaAtom *a = llist.items[li];
            for (uint32_t ri = 0; ri < rlist.count && eng->status == PETTA_STATUS_OK; ri++) {
                PettaAtom *b = rlist.items[ri];
                if (a->kind == PETTA_ATOM_EXPR && b->kind == PETTA_ATOM_EXPR) {
                    PettaValList out;
                    petta_vallist_init(&out);
                    if (strcmp(op, "append") == 0 || strcmp(op, "union-atom") == 0) {
                        for (uint32_t k = 0; k < a->arity; k++) petta_vallist_push_clone(&out, a->args[k]);
                        for (uint32_t k = 0; k < b->arity; k++) petta_vallist_push_clone(&out, b->args[k]);
                    } else if (strcmp(op, "intersection-atom") == 0) {
                        bool *used = b->arity ? (bool *)calloc(b->arity, sizeof(bool)) : NULL;
                        for (uint32_t k = 0; k < a->arity; k++) {
                            for (uint32_t j = 0; j < b->arity; j++) {
                                if (!used[j] && petta_atom_eq(a->args[k], b->args[j])) {
                                    used[j] = true;
                                    petta_vallist_push_clone(&out, a->args[k]);
                                    break;
                                }
                            }
                        }
                        free(used);
                    } else if (strcmp(op, "subtraction-atom") == 0) {
                        bool *used = b->arity ? (bool *)calloc(b->arity, sizeof(bool)) : NULL;
                        for (uint32_t k = 0; k < a->arity; k++) {
                            bool matched = false;
                            for (uint32_t j = 0; j < b->arity; j++) {
                                if (!used[j] && petta_atom_eq(a->args[k], b->args[j])) {
                                    used[j] = true;
                                    matched = true;
                                    break;
                                }
                            }
                            if (!matched) petta_vallist_push_clone(&out, a->args[k]);
                        }
                        free(used);
                    }
                    PettaAtom *res = petta_atom_expr(out.count, out.items);
                    free(out.items);
                    petta_vallist_push_take(out_vals, res);
                } else if (a->has_vars || b->has_vars) {
                    PettaAtom *cargs[3] = {
                        petta_atom_clone(expr->args[0]),
                        petta_atom_clone(a),
                        petta_atom_clone(b)
                    };
                    petta_vallist_push_take(out_vals, petta_atom_expr(3, cargs));
                }
            }
        }
        petta_vallist_free(&llist);
        petta_vallist_free(&rlist);
        return true;
    }

    if (strcmp(op, "reverse") == 0 && expr->arity == 2 && !petta_has_user_rule(eng, op, expr->arity)) {
        PettaValList elist;
        petta_vallist_init(&elist);
        petta_eval_expr(eng, expr->args[1], &elist);
        for (uint32_t i = 0; i < elist.count && eng->status == PETTA_STATUS_OK; i++) {
            PettaAtom *e = elist.items[i];
            if (e->kind == PETTA_ATOM_EXPR) {
                PettaAtom **rargs = e->arity ? (PettaAtom **)calloc(e->arity, sizeof(PettaAtom *)) : NULL;
                for (uint32_t k = 0; k < e->arity; k++)
                    rargs[k] = petta_atom_clone(e->args[e->arity - 1u - k]);
                petta_vallist_push_take(out_vals, petta_atom_expr(e->arity, rargs));
                free(rargs);
            }
        }
        petta_vallist_free(&elist);
        return true;
    }

    if ((strcmp(op, "is-member") == 0 || strcmp(op, "is-alpha-member") == 0 ||
         (strcmp(op, "member") == 0 && !petta_has_user_rule(eng, op, expr->arity))) &&
        expr->arity == 3) {
        bool use_alpha = (strcmp(op, "is-alpha-member") == 0);
        PettaValList xlist, llist;
        petta_vallist_init(&xlist);
        petta_vallist_init(&llist);
        petta_eval_expr(eng, expr->args[1], &xlist);
        petta_eval_expr(eng, expr->args[2], &llist);
        for (uint32_t xi = 0; xi < xlist.count && eng->status == PETTA_STATUS_OK; xi++) {
            PettaAtom *x = xlist.items[xi];
            for (uint32_t li = 0; li < llist.count && eng->status == PETTA_STATUS_OK; li++) {
                PettaAtom *l = llist.items[li];
                if (l->kind == PETTA_ATOM_EXPR) {
                    bool found = false;
                    for (uint32_t k = 0; k < l->arity; k++) {
                        bool hit = false;
                        if (use_alpha) {
                            if (x->kind == PETTA_ATOM_VAR) {
                                hit = (l->args[k]->kind == PETTA_ATOM_VAR);
                            } else {
                                PettaEnv uenv;
                                petta_env_init(&uenv);
                                hit = petta_unify_atoms(x, l->args[k], &uenv);
                                petta_env_free(&uenv);
                            }
                        } else {
                            hit = petta_atom_eq(x, l->args[k]);
                        }
                        if (hit) {
                            found = true;
                            break;
                        }
                    }
                    petta_vallist_push_take(out_vals, petta_atom_sym(found ? "True" : "False"));
                }
            }
        }
        petta_vallist_free(&xlist);
        petta_vallist_free(&llist);
        return true;
    }

    if (strcmp(op, "exclude-item") == 0 && expr->arity == 3) {
        PettaValList xlist, llist;
        petta_vallist_init(&xlist);
        petta_vallist_init(&llist);
        petta_eval_expr(eng, expr->args[1], &xlist);
        petta_eval_expr(eng, expr->args[2], &llist);
        for (uint32_t xi = 0; xi < xlist.count && eng->status == PETTA_STATUS_OK; xi++) {
            PettaAtom *x = xlist.items[xi];
            for (uint32_t li = 0; li < llist.count && eng->status == PETTA_STATUS_OK; li++) {
                PettaAtom *l = llist.items[li];
                if (l->kind == PETTA_ATOM_EXPR) {
                    PettaValList out;
                    petta_vallist_init(&out);
                    for (uint32_t k = 0; k < l->arity; k++) {
                        if (!petta_atom_eq(x, l->args[k])) {
                            petta_vallist_push_clone(&out, l->args[k]);
                        }
                    }
                    PettaAtom *res = petta_atom_expr(out.count, out.items);
                    free(out.items);
                    petta_vallist_push_take(out_vals, res);
                }
            }
        }
        petta_vallist_free(&xlist);
        petta_vallist_free(&llist);
        return true;
    }

    if ((strcmp(op, "unique") == 0 || strcmp(op, "alpha-unique") == 0) && expr->arity == 2) {
        bool use_alpha = (strcmp(op, "alpha-unique") == 0);
        PettaValList elist, u;
        petta_vallist_init(&elist);
        petta_vallist_init(&u);
        petta_eval_expr(eng, expr->args[1], &elist);
        for (uint32_t k = 0; k < elist.count; k++) {
            bool seen = false;
            for (uint32_t j = 0; j < u.count; j++) {
                if (use_alpha ? petta_atom_alpha_eq(u.items[j], elist.items[k])
                              : petta_atom_eq(u.items[j], elist.items[k])) {
                    seen = true;
                    break;
                }
            }
            if (!seen) {
                petta_vallist_push_clone(&u, elist.items[k]);
                petta_vallist_push_clone(out_vals, elist.items[k]);
            }
        }
        petta_vallist_free(&u);
        petta_vallist_free(&elist);
        return true;
    }
    if ((strcmp(op, "union") == 0 || strcmp(op, "intersection") == 0 || strcmp(op, "subtraction") == 0) &&
        expr->arity == 3) {
        PettaValList llist, rlist;
        petta_vallist_init(&llist);
        petta_vallist_init(&rlist);
        petta_eval_expr(eng, expr->args[1], &llist);
        petta_eval_expr(eng, expr->args[2], &rlist);
        if (strcmp(op, "union") == 0) {
            for (uint32_t k = 0; k < llist.count; k++) petta_vallist_push_clone(out_vals, llist.items[k]);
            for (uint32_t k = 0; k < rlist.count; k++) petta_vallist_push_clone(out_vals, rlist.items[k]);
        } else if (strcmp(op, "intersection") == 0) {
            bool *used = rlist.count ? (bool *)calloc(rlist.count, sizeof(bool)) : NULL;
            for (uint32_t k = 0; k < llist.count; k++) {
                for (uint32_t j = 0; j < rlist.count; j++) {
                    if (!used[j] && petta_atom_eq(llist.items[k], rlist.items[j])) {
                        used[j] = true;
                        petta_vallist_push_clone(out_vals, llist.items[k]);
                        break;
                    }
                }
            }
            free(used);
        } else {
            bool *used = rlist.count ? (bool *)calloc(rlist.count, sizeof(bool)) : NULL;
            for (uint32_t k = 0; k < llist.count; k++) {
                bool matched = false;
                for (uint32_t j = 0; j < rlist.count; j++) {
                    if (!used[j] && petta_atom_eq(llist.items[k], rlist.items[j])) {
                        used[j] = true;
                        matched = true;
                        break;
                    }
                }
                if (!matched) petta_vallist_push_clone(out_vals, llist.items[k]);
            }
            free(used);
        }
        petta_vallist_free(&llist);
        petta_vallist_free(&rlist);
        return true;
    }

    if ((strcmp(op, "is-var") == 0 || strcmp(op, "is-expr") == 0 ||
         strcmp(op, "is-space") == 0 || strcmp(op, "get-metatype") == 0) &&
        expr->arity == 2) {
        PettaValList vlist;
        petta_vallist_init(&vlist);
        petta_eval_expr(eng, expr->args[1], &vlist);
        for (uint32_t i = 0; i < vlist.count && eng->status == PETTA_STATUS_OK; i++) {
            PettaAtom *v = vlist.items[i];
            if (strcmp(op, "is-var") == 0) {
                petta_vallist_push_take(out_vals, petta_atom_sym(v->kind == PETTA_ATOM_VAR ? "True" : "False"));
            } else if (strcmp(op, "is-expr") == 0) {
                petta_vallist_push_take(out_vals, petta_atom_sym(v->kind == PETTA_ATOM_EXPR ? "True" : "False"));
            } else if (strcmp(op, "is-space") == 0) {
                bool sp = (v->kind == PETTA_ATOM_SYM && v->text[0] == '&');
                petta_vallist_push_take(out_vals, petta_atom_sym(sp ? "True" : "False"));
            } else {
                const char *mt = "Symbol";
                if (v->kind == PETTA_ATOM_VAR) mt = "Variable";
                else if (v->kind == PETTA_ATOM_EXPR) mt = "Expression";
                else if (v->kind == PETTA_ATOM_INT || v->kind == PETTA_ATOM_STR ||
                         (v->kind == PETTA_ATOM_SYM &&
                          (petta_atom_is_truthy(v) || petta_atom_is_falsy(v) || v->text[0] == '&')))
                    mt = "Grounded";
                petta_vallist_push_take(out_vals, petta_atom_sym(mt));
            }
        }
        petta_vallist_free(&vlist);
        return true;
    }

    if ((strcmp(op, "abs-math") == 0 || strcmp(op, "sqrt-math") == 0 ||
         strcmp(op, "exp") == 0 || strcmp(op, "exp-math") == 0 ||
         strcmp(op, "isinf-math") == 0 || strcmp(op, "isnan-math") == 0 ||
         strcmp(op, "trunc-math") == 0 || strcmp(op, "ceil-math") == 0 ||
         strcmp(op, "floor-math") == 0 || strcmp(op, "round-math") == 0 ||
         strcmp(op, "sin-math") == 0 || strcmp(op, "asin-math") == 0 ||
         strcmp(op, "cos-math") == 0 || strcmp(op, "acos-math") == 0 ||
         strcmp(op, "tan-math") == 0 || strcmp(op, "atan-math") == 0) &&
        expr->arity == 2) {
        PettaValList vlist;
        petta_vallist_init(&vlist);
        petta_eval_expr(eng, expr->args[1], &vlist);
        for (uint32_t i = 0; i < vlist.count && eng->status == PETTA_STATUS_OK; i++) {
            double d = 0.0;
            bool is_f = false;
            if (!petta_atom_as_double(vlist.items[i], &d, &is_f)) {
                eng->status = PETTA_STATUS_FAULT;
                eng->fault = PETTA_FAULT_TYPE;
                break;
            }
            if (strcmp(op, "abs-math") == 0) {
                if (!is_f && vlist.items[i]->kind == PETTA_ATOM_INT) {
                    int64_t x = vlist.items[i]->ival;
                    petta_vallist_push_take(out_vals, petta_atom_int(x < 0 ? -x : x));
                } else {
                    petta_vallist_push_take(out_vals, petta_atom_float(__builtin_fabs(d)));
                }
            } else if (strcmp(op, "sqrt-math") == 0) {
                petta_vallist_push_take(out_vals, petta_atom_float(petta_math_sqrt(d)));
            } else if (strcmp(op, "exp") == 0 || strcmp(op, "exp-math") == 0) {
                petta_vallist_push_take(out_vals, petta_atom_float(petta_math_exp(d)));
            } else if (strcmp(op, "isinf-math") == 0) {
                petta_vallist_push_take(out_vals, petta_atom_sym(__builtin_isinf(d) ? "True" : "False"));
            } else if (strcmp(op, "isnan-math") == 0) {
                petta_vallist_push_take(out_vals, petta_atom_sym(__builtin_isnan(d) ? "True" : "False"));
            } else if (strcmp(op, "trunc-math") == 0) {
                petta_vallist_push_take(out_vals, petta_atom_int(petta_math_trunc(d)));
            } else if (strcmp(op, "ceil-math") == 0) {
                petta_vallist_push_take(out_vals, petta_atom_int(petta_math_ceil(d)));
            } else if (strcmp(op, "floor-math") == 0) {
                petta_vallist_push_take(out_vals, petta_atom_int(petta_math_floor(d)));
            } else if (strcmp(op, "round-math") == 0) {
                petta_vallist_push_take(out_vals, petta_atom_int(petta_math_round(d)));
            } else if (strcmp(op, "sin-math") == 0) {
                petta_vallist_push_take(out_vals, petta_atom_float(petta_math_sin(d)));
            } else if (strcmp(op, "asin-math") == 0) {
                petta_vallist_push_take(out_vals, petta_atom_float(petta_math_asin(d)));
            } else if (strcmp(op, "cos-math") == 0) {
                petta_vallist_push_take(out_vals, petta_atom_float(petta_math_cos(d)));
            } else if (strcmp(op, "acos-math") == 0) {
                petta_vallist_push_take(out_vals, petta_atom_float(petta_math_acos(d)));
            } else if (strcmp(op, "tan-math") == 0) {
                petta_vallist_push_take(out_vals, petta_atom_float(petta_math_tan(d)));
            } else if (strcmp(op, "atan-math") == 0) {
                petta_vallist_push_take(out_vals, petta_atom_float(petta_math_atan(d)));
            }
        }
        petta_vallist_free(&vlist);
        return true;
    }

    if ((strcmp(op, "min") == 0 || strcmp(op, "max") == 0 ||
         strcmp(op, "pow-math") == 0 || strcmp(op, "log-math") == 0 ||
         strcmp(op, "random-float") == 0) &&
        expr->arity == 3 && !petta_has_user_rule(eng, op, expr->arity)) {
        bool is_max = (strcmp(op, "max") == 0);
        bool is_pow = (strcmp(op, "pow-math") == 0);
        bool is_log = (strcmp(op, "log-math") == 0);
        bool is_rnd = (strcmp(op, "random-float") == 0);
        PettaValList llist, rlist;
        petta_vallist_init(&llist);
        petta_vallist_init(&rlist);
        petta_eval_expr(eng, expr->args[1], &llist);
        petta_eval_expr(eng, expr->args[2], &rlist);
        for (uint32_t li = 0; li < llist.count && eng->status == PETTA_STATUS_OK; li++) {
            for (uint32_t ri = 0; ri < rlist.count && eng->status == PETTA_STATUS_OK; ri++) {
                const PettaAtom *la = llist.items[li], *ra = rlist.items[ri];
                if (!is_rnd && !is_log && la->kind == PETTA_ATOM_INT && ra->kind == PETTA_ATOM_INT) {
                    int64_t a = la->ival, b = ra->ival;
                    int64_t res = 0;
                    if (is_pow) {
                        res = 1;
                        if (b >= 0) {
                            for (int64_t k = 0; k < b && k < 62; k++) res *= a;
                        } else {
                            petta_vallist_push_take(out_vals, petta_atom_float(petta_math_pow((double)a, (double)b)));
                            continue;
                        }
                    } else {
                        res = is_max ? (a > b ? a : b) : (a < b ? a : b);
                    }
                    petta_vallist_push_take(out_vals, petta_atom_int(res));
                    continue;
                }
                double da = 0.0, db = 0.0;
                bool fa = false, fb = false;
                if (!petta_atom_as_double(la, &da, &fa) || !petta_atom_as_double(ra, &db, &fb)) {
                    if (la->has_vars || ra->has_vars) {
                        PettaAtom *sargs[3] = { petta_atom_clone(expr->args[0]), petta_atom_clone(la), petta_atom_clone(ra) };
                        petta_vallist_push_take(out_vals, petta_atom_expr(3, sargs));
                        continue;
                    }
                    eng->status = PETTA_STATUS_FAULT;
                    eng->fault = PETTA_FAULT_TYPE;
                    break;
                }
                if (is_rnd) {
                    petta_vallist_push_take(out_vals, petta_atom_float(0.5 * (da + db)));
                } else if (is_log) {
                    petta_vallist_push_take(out_vals, petta_atom_float(petta_math_ln(db) / petta_math_ln(da)));
                } else if (is_pow) {
                    petta_vallist_push_take(out_vals, petta_atom_float(petta_math_pow(da, db)));
                } else {
                    petta_vallist_push_take(out_vals, petta_atom_float(is_max ? (da > db ? da : db) : (da < db ? da : db)));
                }
            }
        }
        petta_vallist_free(&llist);
        petta_vallist_free(&rlist);
        return true;
    }

    if (strcmp(op, "bind!") == 0 && expr->arity == 3 && expr->args[1]->kind == PETTA_ATOM_SYM) {
        if (expr->args[2]->kind == PETTA_ATOM_EXPR && expr->args[2]->arity == 1 &&
            expr->args[2]->args[0]->kind == PETTA_ATOM_SYM &&
            strcmp(expr->args[2]->args[0]->text, "new-space") == 0) {
            petta_vallist_push_take(out_vals, petta_atom_expr(0, NULL));
            return true;
        }
        PettaAtom *val = petta_eval_one(eng, expr->args[2]);
        for (uint32_t i = 0; i < eng->nstore; i++) {
            if (eng->store[i].alive && strcmp(eng->store[i].space, "&__binds") == 0 &&
                eng->store[i].atom->kind == PETTA_ATOM_EXPR && eng->store[i].atom->arity == 2 &&
                petta_atom_eq(eng->store[i].atom->args[0], expr->args[1])) {
                eng->store[i].alive = false;
            }
        }
        PettaAtom *bpair[2] = { petta_atom_clone(expr->args[1]), val };
        PettaAtom *bentry = petta_atom_expr(2, bpair);
        petta_store_add_atom_space(eng, "&__binds", bentry);
        petta_atom_free(bentry);
        eng->has_binds = true;
        petta_vallist_push_take(out_vals, petta_atom_expr(0, NULL));
        return true;
    }

    if (strcmp(op, "new-state") == 0 && expr->arity == 2) {
        PettaAtom *init_v = petta_eval_one(eng, expr->args[1]);
        int64_t sid = (int64_t)eng->next_occ_id++;
        PettaAtom *spair[2] = { petta_atom_int(sid), init_v };
        PettaAtom *sentry = petta_atom_expr(2, spair);
        petta_store_add_atom_space(eng, "&__states", sentry);
        petta_atom_free(sentry);
        PettaAtom *cell[2] = { petta_atom_sym("State"), petta_atom_int(sid) };
        petta_vallist_push_take(out_vals, petta_atom_expr(2, cell));
        return true;
    }

    if (strcmp(op, "get-state") == 0 && expr->arity == 2) {
        PettaAtom *cell = petta_eval_one(eng, expr->args[1]);
        if (cell->kind == PETTA_ATOM_EXPR && cell->arity == 2 &&
            cell->args[0]->kind == PETTA_ATOM_SYM && strcmp(cell->args[0]->text, "State") == 0) {
            for (uint32_t i = 0; i < eng->nstore; i++) {
                if (eng->store[i].alive && strcmp(eng->store[i].space, "&__states") == 0 &&
                    eng->store[i].atom->kind == PETTA_ATOM_EXPR && eng->store[i].atom->arity == 2 &&
                    petta_atom_eq(eng->store[i].atom->args[0], cell->args[1])) {
                    petta_vallist_push_clone(out_vals, eng->store[i].atom->args[1]);
                    petta_atom_free(cell);
                    return true;
                }
            }
        }
        petta_atom_free(cell);
        return false;
    }

    if (strcmp(op, "change-state!") == 0 && expr->arity == 3) {
        PettaAtom *cell = petta_eval_one(eng, expr->args[1]);
        PettaAtom *nval = petta_eval_one(eng, expr->args[2]);
        if (cell->kind == PETTA_ATOM_EXPR && cell->arity == 2 &&
            cell->args[0]->kind == PETTA_ATOM_SYM && strcmp(cell->args[0]->text, "State") == 0) {
            for (uint32_t i = 0; i < eng->nstore; i++) {
                if (eng->store[i].alive && strcmp(eng->store[i].space, "&__states") == 0 &&
                    eng->store[i].atom->kind == PETTA_ATOM_EXPR && eng->store[i].atom->arity == 2 &&
                    petta_atom_eq(eng->store[i].atom->args[0], cell->args[1])) {
                    petta_atom_free(eng->store[i].atom->args[1]);
                    eng->store[i].atom->args[1] = petta_atom_clone(nval);
                    eng->tc_events_admitted++;
                    break;
                }
            }
        }
        petta_atom_free(cell);
        petta_vallist_push_take(out_vals, nval);
        return true;
    }

    if (strcmp(op, "current-time") == 0 && expr->arity == 1) {
        petta_vallist_push_take(out_vals, petta_atom_float(0.0001));
        return true;
    }
    if (strcmp(op, "now") == 0 && expr->arity == 1) {
        petta_vallist_push_take(out_vals, petta_atom_int(1735689600));
        return true;
    }
    if (strcmp(op, "day-of-week") == 0 && expr->arity == 2) {
        PettaAtom *tsv = petta_eval_one(eng, expr->args[1]);
        if (tsv->kind == PETTA_ATOM_INT) {
            static const char *const days[7] = {
                "Sunday", "Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday"
            };
            time_t t = (time_t)tsv->ival;
            struct tm gmt;
            gmtime_r(&t, &gmt);
            petta_atom_free(tsv);
            petta_vallist_push_take(out_vals, petta_atom_sym(days[gmt.tm_wday & 7]));
            return true;
        }
        petta_atom_free(tsv);
        return false;
    }
    if (strcmp(op, "format-date") == 0 && expr->arity == 3) {
        PettaAtom *tsv = petta_eval_one(eng, expr->args[1]);
        PettaAtom *fmt = petta_eval_one(eng, expr->args[2]);
        if (tsv->kind == PETTA_ATOM_INT && (fmt->kind == PETTA_ATOM_STR || fmt->kind == PETTA_ATOM_SYM)) {
            time_t t = (time_t)tsv->ival;
            struct tm gmt;
            gmtime_r(&t, &gmt);
            char fbuf[128] = {0};
            strftime(fbuf, sizeof(fbuf), fmt->text, &gmt);
            bool single_word = true;
            for (const char *c = fbuf; *c; c++) {
                if (isspace((unsigned char)*c) || *c == ':' || *c == '-') { single_word = false; break; }
            }
            petta_atom_free(tsv);
            petta_atom_free(fmt);
            petta_vallist_push_take(out_vals, single_word ? petta_atom_sym(fbuf) : petta_atom_str(fbuf));
            return true;
        }
        petta_atom_free(tsv);
        petta_atom_free(fmt);
        return false;
    }
    if ((strcmp(op, "get-type") == 0 && expr->arity == 2) ||
        (strcmp(op, "get-type-space") == 0 && expr->arity == 3)) {
        const PettaAtom *target_x = (expr->arity == 3) ? expr->args[2] : expr->args[1];
        PettaValList cands;
        petta_vallist_init(&cands);
        petta_get_type_candidates_ex(eng, target_x, &cands, NULL, NULL, NULL);
        if (cands.count == 0) {
            petta_vallist_push_take(out_vals, petta_atom_sym("%Undefined%"));
        } else {
            for (uint32_t i = 0; i < cands.count; i++) {
                petta_vallist_push_clone(out_vals, cands.items[i]);
            }
        }
        petta_vallist_free(&cands);
        return true;
    }
    if (strcmp(op, "match-types") == 0 && expr->arity == 5) {
        PettaAtom *t1 = petta_eval_one(eng, expr->args[1]);
        PettaAtom *t2 = petta_eval_one(eng, expr->args[2]);
        PettaEnv uenv = {0};
        bool eq = petta_unify_atoms(t1, t2, &uenv);
        petta_env_free(&uenv);
        petta_atom_free(t1);
        petta_atom_free(t2);
        petta_eval_expr(eng, eq ? expr->args[3] : expr->args[4], out_vals);
        return true;
    }
    if (strcmp(op, "match-type-or") == 0 && expr->arity == 4) {
        PettaAtom *val = petta_eval_one(eng, expr->args[1]);
        PettaAtom *t1 = petta_eval_one(eng, expr->args[2]);
        PettaAtom *t2 = petta_eval_one(eng, expr->args[3]);
        PettaEnv uenv = {0};
        bool eq = petta_unify_atoms(t1, t2, &uenv);
        petta_env_free(&uenv);
        petta_atom_free(t1);
        petta_atom_free(t2);
        if (eq) {
            petta_atom_free(val);
            petta_vallist_push_take(out_vals, petta_atom_sym("True"));
        } else {
            petta_vallist_push_take(out_vals, val);
        }
        return true;
    }
    if (strcmp(op, "readln!") == 0 && expr->arity == 1) {
        return true;
    }
    if (strcmp(op, "println!") == 0 && !petta_has_user_rule(eng, op, expr->arity)) {
        char *pbuf = (char *)malloc(65536);
        if (expr->arity == 1) {
            printf("\n");
            petta_vallist_push_take(out_vals, petta_atom_sym("True"));
        } else {
            for (uint32_t i = 1; i < expr->arity && eng->status == PETTA_STATUS_OK; i++) {
                PettaValList tmp;
                petta_vallist_init(&tmp);
                petta_eval_expr(eng, expr->args[i], &tmp);
                for (uint32_t k = 0; k < tmp.count; k++) {
                    if (pbuf) {
                        petta_atom_render(tmp.items[k], pbuf, 65536);
                        printf("%s\n", pbuf);
                    }
                    if (i + 1 == expr->arity) {
                        petta_vallist_push_take(out_vals, petta_atom_sym("True"));
                    }
                }
                petta_vallist_free(&tmp);
            }
        }
        free(pbuf);
        return true;
    }
    if (strcmp(op, "add-translator-rule!") == 0 && expr->arity == 2 && expr->args[1]->kind == PETTA_ATOM_SYM) {
        if (eng->ntranslator_rules < 32u) {
            snprintf(eng->translator_rules[eng->ntranslator_rules++], 64, "%s", expr->args[1]->text);
        }
        petta_vallist_push_take(out_vals, petta_atom_sym("True"));
        return true;
    }
    if (strcmp(op, "remove-translator-rule!") == 0 && expr->arity == 2 && expr->args[1]->kind == PETTA_ATOM_SYM) {
        for (uint32_t i = 0; i < eng->ntranslator_rules; i++) {
            if (strcmp(eng->translator_rules[i], expr->args[1]->text) == 0) {
                eng->translator_rules[i][0] = '\0';
            }
        }
        petta_vallist_push_take(out_vals, petta_atom_sym("True"));
        return true;
    }
    if (strcmp(op, "import!") == 0 && expr->arity == 3 && !petta_has_user_rule(eng, op, expr->arity)) {
        const char *target_space = (expr->args[1]->kind == PETTA_ATOM_SYM) ? expr->args[1]->text : "&self";
        const PettaAtom *spec = expr->args[2];
        char mod_name[256] = {0};
        bool is_lib = false;
        if (spec->kind == PETTA_ATOM_EXPR && spec->arity == 2 &&
            spec->args[0]->kind == PETTA_ATOM_SYM && strcmp(spec->args[0]->text, "library") == 0 &&
            (spec->args[1]->kind == PETTA_ATOM_SYM || spec->args[1]->kind == PETTA_ATOM_STR)) {
            is_lib = true;
            snprintf(mod_name, sizeof(mod_name), "%s", spec->args[1]->text);
        } else if (spec->kind == PETTA_ATOM_SYM || spec->kind == PETTA_ATOM_STR) {
            snprintf(mod_name, sizeof(mod_name), "%s", spec->text);
        }
        if (mod_name[0]) {
            bool has_ext = (strlen(mod_name) > 6 && strcmp(mod_name + strlen(mod_name) - 6, ".metta") == 0);
            /* Imports resolve against the importing file's directory and its sibling lib/
             * (the layout of the PeTTa repository), and, when PETTA_ROOT names a PeTTa
             * checkout, against its examples/ and lib/. */
            const char *base_dir = eng->cur_dir[0] ? eng->cur_dir : ".";
            const char *petta_root = getenv("PETTA_ROOT");
            char cand_paths[4][1024];
            int ncand = 0;
            if (is_lib) {
                if (petta_root && petta_root[0])
                    snprintf(cand_paths[ncand++], 1024, "%s/lib/%s%s",
                             petta_root, mod_name, has_ext ? "" : ".metta");
                snprintf(cand_paths[ncand++], 1024, "%s/../lib/%s%s",
                         base_dir, mod_name, has_ext ? "" : ".metta");
            } else if (mod_name[0] == '/') {
                snprintf(cand_paths[ncand++], 1024, "%s%s", mod_name, has_ext ? "" : ".metta");
            } else {
                snprintf(cand_paths[ncand++], 1024, "%s/%s%s", base_dir, mod_name, has_ext ? "" : ".metta");
                if (petta_root && petta_root[0]) {
                    snprintf(cand_paths[ncand++], 1024, "%s/examples/%s%s",
                             petta_root, mod_name, has_ext ? "" : ".metta");
                    snprintf(cand_paths[ncand++], 1024, "%s/lib/%s%s",
                             petta_root, mod_name, has_ext ? "" : ".metta");
                }
                snprintf(cand_paths[ncand++], 1024, "%s/../lib/%s%s",
                         base_dir, mod_name, has_ext ? "" : ".metta");
            }
            FILE *fp = NULL;
            char chosen_path[512] = {0};
            for (int c = 0; c < ncand; c++) {
                fp = fopen(cand_paths[c], "rb");
                if (fp) {
                    char *rp = realpath(cand_paths[c], NULL);
                    if (rp) {
                        snprintf(chosen_path, sizeof(chosen_path), "%s", rp);
                        free(rp);
                    } else {
                        snprintf(chosen_path, sizeof(chosen_path), "%s", cand_paths[c]);
                    }
                    break;
                }
            }
            if (!fp) {
                eng->status = PETTA_STATUS_FAULT;
                eng->fault = PETTA_FAULT_TYPE;
                return true;
            }
            for (uint32_t i = 0; i < eng->nimported_files; i++) {
                if (strcmp(eng->imported_files[i].space, target_space) == 0 &&
                    strcmp(eng->imported_files[i].path, chosen_path) == 0) {
                    fclose(fp);
                    petta_vallist_push_take(out_vals, petta_atom_expr(0, NULL));
                    return true;
                }
            }
            if (eng->nimported_files < 64u) {
                uint32_t idx = eng->nimported_files++;
                snprintf(eng->imported_files[idx].space, sizeof(eng->imported_files[idx].space), "%s", target_space);
                snprintf(eng->imported_files[idx].path, sizeof(eng->imported_files[idx].path), "%s", chosen_path);
            }
            fseek(fp, 0, SEEK_END);
            long fsz = ftell(fp);
            fseek(fp, 0, SEEK_SET);
            char *fbuf = (char *)calloc((size_t)(fsz > 0 ? fsz : 0) + 1u, 1u);
            if (fsz > 0) {
                size_t rd = fread(fbuf, 1u, (size_t)fsz, fp);
                fbuf[rd] = '\0';
            }
            fclose(fp);
            char prev_dir[512];
            snprintf(prev_dir, sizeof(prev_dir), "%s", eng->cur_dir);
            char *last_slash = strrchr(chosen_path, '/');
            if (last_slash) {
                size_t dlen = (size_t)(last_slash - chosen_path);
                if (dlen >= sizeof(eng->cur_dir)) dlen = sizeof(eng->cur_dir) - 1u;
                memcpy(eng->cur_dir, chosen_path, dlen);
                eng->cur_dir[dlen] = '\0';
            }
            petta_load_space_program(eng, target_space, fbuf, NULL);
            snprintf(eng->cur_dir, sizeof(eng->cur_dir), "%s", prev_dir);
            free(fbuf);
            if (eng->status != PETTA_STATUS_OK) return true;
        }
        petta_vallist_push_take(out_vals, petta_atom_expr(0, NULL));
        return true;
    }
    if ((strcmp(op, "memoize") == 0 || strcmp(op, "config-memoize") == 0) &&
        !petta_has_user_rule(eng, op, expr->arity)) {
        petta_vallist_push_take(out_vals, petta_atom_expr(0, NULL));
        return true;
    }

    if (strcmp(op, "noreduce-eq") == 0 && expr->arity == 3) {
        bool eq = petta_atom_alpha_eq(expr->args[1], expr->args[2]);
        petta_vallist_push_take(out_vals, petta_atom_sym(eq ? "True" : "False"));
        return true;
    }

    if (strcmp(op, "is-function") == 0 && expr->arity == 2) {
        PettaValList vlist;
        petta_vallist_init(&vlist);
        petta_eval_expr(eng, expr->args[1], &vlist);
        for (uint32_t i = 0; i < vlist.count && eng->status == PETTA_STATUS_OK; i++) {
            const PettaAtom *v = vlist.items[i];
            bool is_fn = (v->kind == PETTA_ATOM_EXPR && v->arity == 3 &&
                          v->args[0]->kind == PETTA_ATOM_SYM &&
                          (strcmp(v->args[0]->text, "|->") == 0 || strcmp(v->args[0]->text, "->") == 0));
            petta_vallist_push_take(out_vals, petta_atom_sym(is_fn ? "True" : "False"));
        }
        petta_vallist_free(&vlist);
        return true;
    }

    if (strcmp(op, "repr") == 0 && expr->arity == 2) {
        PettaValList vlist;
        petta_vallist_init(&vlist);
        petta_eval_expr(eng, expr->args[1], &vlist);
        char rbuf[4096];
        for (uint32_t i = 0; i < vlist.count && eng->status == PETTA_STATUS_OK; i++) {
            const PettaAtom *v = vlist.items[i];
            if (v->kind == PETTA_ATOM_EXPR && v->arity >= 2 &&
                v->args[0]->kind == PETTA_ATOM_SYM &&
                petta_has_higher_arity_rule(eng, v->args[0]->text, v->arity)) {
                PettaAtom *arg_tup = petta_atom_expr(v->arity - 1u, v->args + 1);
                char abuf[2048];
                abuf[0] = '\0';
                petta_atom_render(arg_tup, abuf, sizeof(abuf));
                petta_atom_free(arg_tup);
                snprintf(rbuf, sizeof(rbuf), "(partial %s %s)", v->args[0]->text, abuf);
            } else {
                rbuf[0] = '\0';
                petta_atom_render(v, rbuf, sizeof(rbuf));
            }
            petta_vallist_push_take(out_vals, petta_atom_str(rbuf));
        }
        petta_vallist_free(&vlist);
        return true;
    }

    if (strcmp(op, "parse") == 0 && expr->arity == 2) {
        PettaValList vlist;
        petta_vallist_init(&vlist);
        petta_eval_expr(eng, expr->args[1], &vlist);
        for (uint32_t i = 0; i < vlist.count && eng->status == PETTA_STATUS_OK; i++) {
            const PettaAtom *v = vlist.items[i];
            const char *src = (v->kind == PETTA_ATOM_STR || v->kind == PETTA_ATOM_SYM) ? v->text : NULL;
            if (src) {
                const char *p = src;
                PettaAtom *parsed = petta_parse_expr(&p);
                if (parsed) petta_vallist_push_take(out_vals, parsed);
            }
        }
        petta_vallist_free(&vlist);
        return true;
    }

    return false;
}

static __attribute__((noinline)) void petta_eval_expr_inner(
    PettaTcalcEngine *eng,
    const PettaAtom *init_expr,
    PettaValList *out_vals)
{
    const PettaAtom *expr = init_expr;
    PettaAtom *owned_expr = NULL;

tail_call:
    if (!expr || eng->status != PETTA_STATUS_OK) goto done;
    {
        uint32_t cur_epoch = eng->nrules + (uint32_t)eng->tc_events_admitted + 1u;
        if (expr->nf_epoch == cur_epoch) {
            petta_vallist_push_clone(out_vals, expr);
            goto done;
        }
    }
    if (eng->max_steps > 0 && eng->steps_executed >= eng->max_steps) {
        eng->status = PETTA_STATUS_BUDGET_EXHAUSTED;
        goto done;
    }
    eng->steps_executed++;

    PettaEnv shared_env;

    /* Atoms that are symbols, ints, strings, or variables evaluate to themselves
     * unless a zero-arg rule (= Sym ...) rewrites a symbol (or bare `empty` produces 0 results) */
    if (expr->kind != PETTA_ATOM_EXPR) {
        if (expr->kind == PETTA_ATOM_SYM && strcmp(expr->text, "empty") == 0) {
            goto done;
        }
        if (expr->kind == PETTA_ATOM_SYM && eng->has_binds && strcmp(expr->text, "&self") != 0) {
            for (uint32_t i = 0; i < eng->nstore; i++) {
                if (eng->store[i].alive && strcmp(eng->store[i].space, "&__binds") == 0 &&
                    eng->store[i].atom->kind == PETTA_ATOM_EXPR && eng->store[i].atom->arity == 2 &&
                    petta_atom_eq(eng->store[i].atom->args[0], expr)) {
                    petta_vallist_push_clone(out_vals, eng->store[i].atom->args[1]);
                    goto done;
                }
            }
        }
        if (expr->kind == PETTA_ATOM_SYM && eng->has_sym_rules) {
            bool matched_rule = false;
            for (uint32_t r = 0; r < eng->nrules; r++) {
                if (eng->rules[r].removed || eng->rules[r].arity != 0u) continue;
                if (petta_match_pattern(eng->rules[r].lhs, expr, &shared_env)) {
                    matched_rule = true;
                    PettaAtom *inst = petta_subst_env(eng->rules[r].rhs, &shared_env);
                    petta_env_free(&shared_env);
                    petta_eval_expr(eng, inst, out_vals);
                    petta_atom_free(inst);
                }
            }
            if (matched_rule) goto done;
        }
        petta_vallist_push_clone(out_vals, expr);
        goto done;
    }

    if (expr->arity == 0) {
        petta_vallist_push_clone(out_vals, expr);
        goto done;
    }

    const PettaAtom *head = expr->args[0];
    if (head->kind == PETTA_ATOM_SYM) {
        const char *op = head->text;

        /* 1. Type declaration (: f Type) or rule definition (= lhs rhs) */
        if (strcmp(op, ":") == 0 && eng->depth <= 1u) {
            if (expr->arity == 3) {
                petta_store_add_atom(eng, expr);
            }
            if (expr->arity == 3 && expr->args[1]->kind == PETTA_ATOM_SYM &&
                expr->args[2]->kind == PETTA_ATOM_EXPR && expr->args[2]->arity >= 2 &&
                expr->args[2]->args[0]->kind == PETTA_ATOM_SYM &&
                strcmp(expr->args[2]->args[0]->text, "->") == 0 &&
                eng->nsigs < 64u) {
                uint32_t si = eng->nsigs++;
                snprintf(eng->sigs[si].head, sizeof(eng->sigs[si].head), "%s", expr->args[1]->text);
                uint32_t pc = expr->args[2]->arity - 2u;
                if (pc > 8u) pc = 8u;
                eng->sigs[si].param_count = pc;
                for (uint32_t p = 0; p < pc; p++) {
                    const PettaAtom *pt = expr->args[2]->args[p + 1u];
                    snprintf(eng->sigs[si].param_types[p], sizeof(eng->sigs[si].param_types[p]),
                             "%s", (pt->kind == PETTA_ATOM_SYM && pt->text) ? pt->text : "%Undefined%");
                }
            }
            petta_vallist_push_take(out_vals, petta_atom_sym("Unit"));
            goto done;
        }
        if (strcmp(op, "=") == 0 && expr->arity == 3) {
            if (eng->depth > 1u) {
                PettaValList llist, rlist;
                petta_vallist_init(&llist);
                petta_vallist_init(&rlist);
                petta_eval_expr(eng, expr->args[1], &llist);
                petta_eval_expr(eng, expr->args[2], &rlist);
                for (uint32_t li = 0; li < llist.count && eng->status == PETTA_STATUS_OK; li++) {
                    for (uint32_t ri = 0; ri < rlist.count && eng->status == PETTA_STATUS_OK; ri++) {
                        PettaEnv uenv;
                        petta_env_init(&uenv);
                        bool eq = petta_unify_atoms(llist.items[li], rlist.items[ri], &uenv);
                        petta_env_free(&uenv);
                        petta_vallist_push_take(out_vals, petta_atom_sym(eq ? "True" : "False"));
                    }
                }
                petta_vallist_free(&llist);
                petta_vallist_free(&rlist);
                goto done;
            }
            petta_register_rule(eng, expr->args[1], expr->args[2]);
            petta_vallist_push_take(out_vals, petta_atom_sym("Unit"));
            goto done;
        }

        /* 2. quote */
        if (strcmp(op, "quote") == 0 && expr->arity == 2) {
            petta_vallist_push_clone(out_vals, expr->args[1]);
            goto done;
        }

        /* 3. let / chain: (let $pat $val_expr $body) or (chain $val_expr $var $body) */
        if ((strcmp(op, "let") == 0 || strcmp(op, "chain") == 0) && expr->arity == 4) {
            bool is_chain_order = (strcmp(op, "chain") == 0 &&
                                   expr->args[2]->kind == PETTA_ATOM_VAR &&
                                   expr->args[1]->kind != PETTA_ATOM_VAR);
            const PettaAtom *pat_arg = is_chain_order ? expr->args[2] : expr->args[1];
            const PettaAtom *val_arg = is_chain_order ? expr->args[1] : expr->args[2];
            if (val_arg->kind == PETTA_ATOM_EXPR && val_arg->arity == 2 &&
                val_arg->args[0]->kind == PETTA_ATOM_SYM &&
                strcmp(val_arg->args[0]->text, "get-type") == 0) {
                PettaValList cands;
                petta_vallist_init(&cands);
                PettaEnv venvs[16];
                memset(venvs, 0, sizeof(venvs));
                uint32_t vcnt = 0, vcap = 16;
                petta_get_type_candidates_ex(eng, val_arg->args[1], &cands, venvs, &vcnt, &vcap);
                if (cands.count == 0 && pat_arg->kind != PETTA_ATOM_SYM) {
                    petta_vallist_push_take(&cands, petta_atom_sym("%Undefined%"));
                }
                for (uint32_t i = 0; i < cands.count && eng->status == PETTA_STATUS_OK; i++) {
                    if (petta_match_pattern(pat_arg, cands.items[i], &shared_env)) {
                        if (i < vcnt) {
                            for (uint32_t b = 0; b < venvs[i].nbinds; b++)
                                petta_env_bind(&shared_env, venvs[i].binds[b].var, venvs[i].binds[b].val);
                        }
                        PettaAtom *sub = petta_subst_env(expr->args[3], &shared_env);
                        petta_env_free(&shared_env);
                        petta_eval_expr(eng, sub, out_vals);
                        petta_atom_free(sub);
                    }
                }
                for (uint32_t i = 0; i < vcnt; i++) petta_env_free(&venvs[i]);
                petta_vallist_free(&cands);
                goto done;
            }
            PettaValList vlist;
            petta_vallist_init(&vlist);
            petta_eval_expr(eng, val_arg, &vlist);
            PettaValList plist;
            petta_vallist_init(&plist);
            if (pat_arg->kind == PETTA_ATOM_EXPR && pat_arg->arity >= 1 &&
                pat_arg->args[0]->kind == PETTA_ATOM_SYM &&
                strcmp(pat_arg->args[0]->text, "cons") != 0 &&
                strcmp(pat_arg->args[0]->text, "cons-atom") != 0 &&
                strcmp(pat_arg->args[0]->text, "append") != 0 &&
                strcmp(pat_arg->args[0]->text, "union-atom") != 0 &&
                strcmp(pat_arg->args[0]->text, "@") != 0 &&
                strcmp(pat_arg->args[0]->text, "+") != 0 &&
                strcmp(pat_arg->args[0]->text, "#+") != 0 &&
                strcmp(pat_arg->args[0]->text, "-") != 0 &&
                strcmp(pat_arg->args[0]->text, "#-") != 0 &&
                petta_has_user_rule(eng, pat_arg->args[0]->text, pat_arg->arity)) {
                petta_eval_expr(eng, pat_arg, &plist);
            }
            if (plist.count == 0) {
                petta_vallist_push_clone(&plist, pat_arg);
            }
            if (vlist.count == 1 && plist.count == 1 && eng->status == PETTA_STATUS_OK) {
                bool matched = vlist.items[0]->has_vars
                    ? petta_unify_pattern(plist.items[0], vlist.items[0], &shared_env)
                    : petta_match_pattern(plist.items[0], vlist.items[0], &shared_env);
                if (matched) {
                    PettaAtom *sub = vlist.items[0]->has_vars
                        ? petta_subst_env_trans(expr->args[3], &shared_env)
                        : petta_subst_env(expr->args[3], &shared_env);
                    petta_env_free(&shared_env);
                    petta_vallist_free(&plist);
                    petta_vallist_free(&vlist);
                    petta_atom_free(owned_expr);
                    owned_expr = sub;
                    expr = owned_expr;
                    goto tail_call;
                }
                petta_vallist_free(&plist);
                petta_vallist_free(&vlist);
                goto done;
            }
            for (uint32_t i = 0; i < vlist.count && eng->status == PETTA_STATUS_OK; i++) {
                for (uint32_t p = 0; p < plist.count && eng->status == PETTA_STATUS_OK; p++) {
                    bool matched = vlist.items[i]->has_vars
                        ? petta_unify_pattern(plist.items[p], vlist.items[i], &shared_env)
                        : petta_match_pattern(plist.items[p], vlist.items[i], &shared_env);
                    if (matched) {
                        PettaAtom *sub = vlist.items[i]->has_vars
                            ? petta_subst_env_trans(expr->args[3], &shared_env)
                            : petta_subst_env(expr->args[3], &shared_env);
                        petta_env_free(&shared_env);
                        petta_eval_expr(eng, sub, out_vals);
                        petta_atom_free(sub);
                        if (eng->cut_fired) break;
                    }
                }
                if (eng->cut_fired) break;
            }
            petta_vallist_free(&plist);
            petta_vallist_free(&vlist);
            goto done;
        }

        /* 4. let*: (let* (($p1 $v1) ...) $body) — evaluated iteratively with DFS non-deterministic branching */
        if (strcmp(op, "let*") == 0 && expr->arity == 3 &&
            expr->args[1]->kind == PETTA_ATOM_EXPR) {
            typedef struct {
                uint32_t b_idx;
                PettaAtom *binds;
                PettaAtom *body;
            } LetStarState;
            uint32_t wcap = 8u, wcount = 0u;
            LetStarState *work = (LetStarState *)calloc(wcap, sizeof(LetStarState));
            work[wcount++] = (LetStarState){
                .b_idx = 0u,
                .binds = petta_atom_clone(expr->args[1]),
                .body  = petta_atom_clone(expr->args[2])
            };
            while (wcount > 0u && eng->status == PETTA_STATUS_OK) {
                if (eng->max_steps > 0 && eng->steps_executed >= eng->max_steps) {
                    eng->status = PETTA_STATUS_BUDGET_EXHAUSTED;
                    break;
                }
                eng->steps_executed++;
                LetStarState st = work[--wcount];
                if (st.b_idx >= st.binds->arity) {
                    if (wcount == 0u) {
                        PettaAtom *final_body = st.body;
                        petta_atom_free(st.binds);
                        free(work);
                        petta_atom_free(owned_expr);
                        owned_expr = final_body;
                        expr = owned_expr;
                        goto tail_call;
                    }
                    petta_eval_expr(eng, st.body, out_vals);
                    petta_atom_free(st.binds);
                    petta_atom_free(st.body);
                    if (eng->cut_fired) break;
                    continue;
                }
                PettaAtom *pair = st.binds->args[st.b_idx];
                if (pair->kind != PETTA_ATOM_EXPR || pair->arity != 2) {
                    petta_atom_free(st.binds);
                    petta_atom_free(st.body);
                    continue;
                }
                PettaValList vlist;
                petta_vallist_init(&vlist);
                petta_eval_expr(eng, pair->args[1], &vlist);
                if (eng->cut_fired && vlist.count == 0u) {
                    petta_vallist_free(&vlist);
                    petta_atom_free(st.binds);
                    petta_atom_free(st.body);
                    break;
                }
                for (uint32_t vi_rev = vlist.count; vi_rev > 0u && eng->status == PETTA_STATUS_OK; vi_rev--) {
                    uint32_t vi = vi_rev - 1u;
                    bool has_v = vlist.items[vi]->has_vars;
                    bool matched = has_v
                        ? petta_unify_pattern(pair->args[0], vlist.items[vi], &shared_env)
                        : petta_match_pattern(pair->args[0], vlist.items[vi], &shared_env);
                    if (matched) {
                        PettaAtom **nb_args = st.binds->arity
                            ? (PettaAtom **)calloc(st.binds->arity, sizeof(PettaAtom *)) : NULL;
                        for (uint32_t k = 0u; k < st.binds->arity; k++) {
                            PettaAtom *kp = st.binds->args[k];
                            if (k > st.b_idx && kp->kind == PETTA_ATOM_EXPR && kp->arity == 2) {
                                PettaAtom *np[2] = {
                                    (kp->args[0]->kind == PETTA_ATOM_EXPR || has_v)
                                        ? (has_v ? petta_subst_env_trans(kp->args[0], &shared_env)
                                                 : petta_subst_env(kp->args[0], &shared_env))
                                        : petta_atom_clone(kp->args[0]),
                                    has_v ? petta_subst_env_trans(kp->args[1], &shared_env)
                                          : petta_subst_env(kp->args[1], &shared_env)
                                };
                                nb_args[k] = petta_atom_expr(2, np);
                            } else {
                                nb_args[k] = petta_atom_clone(kp);
                            }
                        }
                        PettaAtom *nbinds = petta_atom_expr(st.binds->arity, nb_args);
                        free(nb_args);
                        PettaAtom *nbody = has_v
                            ? petta_subst_env_trans(st.body, &shared_env)
                            : petta_subst_env(st.body, &shared_env);
                        petta_env_free(&shared_env);
                        if (wcount >= wcap) {
                            wcap *= 2u;
                            work = (LetStarState *)realloc(work, (size_t)wcap * sizeof(LetStarState));
                        }
                        work[wcount++] = (LetStarState){
                            .b_idx = st.b_idx + 1u,
                            .binds = nbinds,
                            .body  = nbody
                        };
                    }
                }
                petta_vallist_free(&vlist);
                petta_atom_free(st.binds);
                petta_atom_free(st.body);
            }
            for (uint32_t wi = 0u; wi < wcount; wi++) {
                petta_atom_free(work[wi].binds);
                petta_atom_free(work[wi].body);
            }
            free(work);
            goto done;
        }

        /* 5. if: (if $cond $then [$else]) */
        if (strcmp(op, "if") == 0 && (expr->arity == 4 || expr->arity == 3)) {
            if (expr->args[1]->kind == PETTA_ATOM_EXPR && expr->args[1]->arity == 3 &&
                expr->args[1]->args[0]->kind == PETTA_ATOM_SYM &&
                strcmp(expr->args[1]->args[0]->text, "=") == 0) {
                PettaValList llist, rlist;
                petta_vallist_init(&llist);
                petta_vallist_init(&rlist);
                petta_eval_expr(eng, expr->args[1]->args[1], &llist);
                petta_eval_expr(eng, expr->args[1]->args[2], &rlist);
                for (uint32_t li = 0; li < llist.count && eng->status == PETTA_STATUS_OK; li++) {
                    for (uint32_t ri = 0; ri < rlist.count && eng->status == PETTA_STATUS_OK; ri++) {
                        PettaEnv uenv;
                        petta_env_init(&uenv);
                        if (petta_unify_atoms(llist.items[li], rlist.items[ri], &uenv)) {
                            PettaAtom *sub_then = petta_subst_env_trans(expr->args[2], &uenv);
                            petta_env_free(&uenv);
                            petta_eval_expr(eng, sub_then, out_vals);
                            petta_atom_free(sub_then);
                        } else {
                            petta_env_free(&uenv);
                            if (expr->arity == 4) {
                                petta_eval_expr(eng, expr->args[3], out_vals);
                            }
                        }
                    }
                }
                petta_vallist_free(&llist);
                petta_vallist_free(&rlist);
                goto done;
            }
            if (expr->args[1]->kind == PETTA_ATOM_EXPR && expr->args[1]->arity == 3 &&
                expr->args[1]->args[0]->kind == PETTA_ATOM_SYM &&
                strcmp(expr->args[1]->args[0]->text, "find") == 0 &&
                expr->args[1]->args[2]->has_vars) {
                PettaAtom *sp_val = petta_eval_one(eng, expr->args[1]->args[1]);
                const char *sp_name = (sp_val->kind == PETTA_ATOM_SYM) ? sp_val->text : "&self";
                const PettaAtom *fpat = expr->args[1]->args[2];
                bool any_found = false;
                for (uint32_t i = 0; i < eng->nstore && eng->status == PETTA_STATUS_OK; i++) {
                    if (!eng->store[i].alive || !tc_alive(eng->store[i].tc_occ)) continue;
                    if (!petta_space_matches(&eng->store[i], sp_name)) continue;
                    PettaEnv menv;
                    if (petta_match_pattern(fpat, eng->store[i].atom, &menv)) {
                        any_found = true;
                        PettaAtom *sub_then = petta_subst_env(expr->args[2], &menv);
                        petta_env_free(&menv);
                        petta_eval_expr(eng, sub_then, out_vals);
                        petta_atom_free(sub_then);
                    }
                }
                petta_atom_free(sp_val);
                if (!any_found && expr->arity == 4) {
                    petta_eval_expr(eng, expr->args[3], out_vals);
                }
                goto done;
            }
            PettaValList clist;
            petta_vallist_init(&clist);
            petta_eval_expr(eng, expr->args[1], &clist);
            if (clist.count == 1 && eng->status == PETTA_STATUS_OK) {
                if (petta_atom_is_truthy(clist.items[0])) {
                    PettaAtom *next_e = petta_atom_clone(expr->args[2]);
                    petta_vallist_free(&clist);
                    petta_atom_free(owned_expr);
                    owned_expr = next_e;
                    expr = owned_expr;
                    goto tail_call;
                } else if (petta_atom_is_falsy(clist.items[0])) {
                    if (expr->arity == 4) {
                        PettaAtom *next_e = petta_atom_clone(expr->args[3]);
                        petta_vallist_free(&clist);
                        petta_atom_free(owned_expr);
                        owned_expr = next_e;
                        expr = owned_expr;
                        goto tail_call;
                    }
                    petta_vallist_free(&clist);
                    goto done;
                }
            }
            for (uint32_t i = 0; i < clist.count && eng->status == PETTA_STATUS_OK; i++) {
                if (petta_atom_is_truthy(clist.items[i])) {
                    petta_eval_expr(eng, expr->args[2], out_vals);
                } else if (petta_atom_is_falsy(clist.items[i])) {
                    if (expr->arity == 4) {
                        petta_eval_expr(eng, expr->args[3], out_vals);
                    }
                } else if (expr->arity == 4) {
                    PettaAtom *if_args[4] = {
                        petta_atom_clone(expr->args[0]),
                        petta_atom_clone(clist.items[i]),
                        petta_atom_clone(expr->args[2]),
                        petta_atom_clone(expr->args[3])
                    };
                    petta_vallist_push_take(out_vals, petta_atom_expr(4, if_args));
                }
            }
            petta_vallist_free(&clist);
            goto done;
        }

        /* 5b. Boolean Builtins: (not $a), (and $a $b), (or $a $b), (xor $a $b), (and-then $a $b), (or-else $a $b) */
        if (strcmp(op, "xor") == 0 && expr->arity == 3) {
            PettaValList llist, rlist;
            petta_vallist_init(&llist);
            petta_vallist_init(&rlist);
            petta_eval_expr(eng, expr->args[1], &llist);
            petta_eval_expr(eng, expr->args[2], &rlist);
            for (uint32_t li = 0; li < llist.count && eng->status == PETTA_STATUS_OK; li++) {
                const PettaAtom *lhs = llist.items[li];
                bool lhs_lc = (lhs && lhs->kind == PETTA_ATOM_SYM &&
                               (strcmp(lhs->text, "true") == 0 || strcmp(lhs->text, "false") == 0));
                for (uint32_t ri = 0; ri < rlist.count && eng->status == PETTA_STATUS_OK; ri++) {
                    const PettaAtom *rhs = rlist.items[ri];
                    bool lc = lhs_lc || (rhs && rhs->kind == PETTA_ATOM_SYM &&
                                         (strcmp(rhs->text, "true") == 0 || strcmp(rhs->text, "false") == 0));
                    bool lt = petta_atom_is_truthy(lhs), lf = petta_atom_is_falsy(lhs);
                    bool rt = petta_atom_is_truthy(rhs), rf = petta_atom_is_falsy(rhs);
                    if ((lt || lf) && (rt || rf)) {
                        bool xr = (lt != rt);
                        petta_vallist_push_take(out_vals, petta_atom_sym(xr ? (lc ? "true" : "True") : (lc ? "false" : "False")));
                    } else {
                        PettaAtom *bargs[3] = { petta_atom_clone(expr->args[0]), petta_atom_clone(lhs), petta_atom_clone(rhs) };
                        petta_vallist_push_take(out_vals, petta_atom_expr(3, bargs));
                    }
                }
            }
            petta_vallist_free(&llist);
            petta_vallist_free(&rlist);
            goto done;
        }
        if (strcmp(op, "not") == 0 && expr->arity == 2) {
            PettaValList llist;
            petta_vallist_init(&llist);
            petta_eval_expr(eng, expr->args[1], &llist);
            for (uint32_t i = 0; i < llist.count && eng->status == PETTA_STATUS_OK; i++) {
                const PettaAtom *a = llist.items[i];
                bool lc = (a && a->kind == PETTA_ATOM_SYM && (strcmp(a->text, "true") == 0 || strcmp(a->text, "false") == 0));
                if (petta_atom_is_truthy(a)) {
                    petta_vallist_push_take(out_vals, petta_atom_sym(lc ? "false" : "False"));
                } else if (petta_atom_is_falsy(a)) {
                    petta_vallist_push_take(out_vals, petta_atom_sym(lc ? "true" : "True"));
                } else {
                    PettaAtom *nargs[2] = { petta_atom_clone(expr->args[0]), petta_atom_clone(a) };
                    petta_vallist_push_take(out_vals, petta_atom_expr(2, nargs));
                }
            }
            petta_vallist_free(&llist);
            goto done;
        }
        if ((strcmp(op, "and") == 0 || strcmp(op, "or") == 0 ||
             strcmp(op, "and-then") == 0 || strcmp(op, "or-else") == 0) && expr->arity == 3) {
            bool is_and = (strcmp(op, "and") == 0 || strcmp(op, "and-then") == 0);
            PettaValList llist;
            petta_vallist_init(&llist);
            petta_eval_expr(eng, expr->args[1], &llist);
            for (uint32_t li = 0; li < llist.count && eng->status == PETTA_STATUS_OK; li++) {
                PettaAtom *lhs = llist.items[li];
                bool lhs_lc = (lhs && lhs->kind == PETTA_ATOM_SYM &&
                               (strcmp(lhs->text, "true") == 0 || strcmp(lhs->text, "false") == 0));
                if (is_and && petta_atom_is_falsy(lhs)) {
                    petta_vallist_push_take(out_vals, petta_atom_sym(lhs_lc ? "false" : "False"));
                    continue;
                }
                if (!is_and && petta_atom_is_truthy(lhs)) {
                    petta_vallist_push_take(out_vals, petta_atom_sym(lhs_lc ? "true" : "True"));
                    continue;
                }
                PettaValList rlist;
                petta_vallist_init(&rlist);
                petta_eval_expr(eng, expr->args[2], &rlist);
                for (uint32_t ri = 0; ri < rlist.count && eng->status == PETTA_STATUS_OK; ri++) {
                    PettaAtom *rhs = rlist.items[ri];
                    bool lc = lhs_lc || (rhs && rhs->kind == PETTA_ATOM_SYM &&
                                         (strcmp(rhs->text, "true") == 0 || strcmp(rhs->text, "false") == 0));
                    if (is_and) {
                        if (petta_atom_is_falsy(rhs)) {
                            petta_vallist_push_take(out_vals, petta_atom_sym(lc ? "false" : "False"));
                        } else if (petta_atom_is_truthy(lhs) && petta_atom_is_truthy(rhs)) {
                            petta_vallist_push_take(out_vals, petta_atom_sym(lc ? "true" : "True"));
                        } else {
                            PettaAtom *bargs[3] = { petta_atom_clone(expr->args[0]), petta_atom_clone(lhs), petta_atom_clone(rhs) };
                            petta_vallist_push_take(out_vals, petta_atom_expr(3, bargs));
                        }
                    } else {
                        if (petta_atom_is_truthy(rhs)) {
                            petta_vallist_push_take(out_vals, petta_atom_sym(lc ? "true" : "True"));
                        } else if (petta_atom_is_falsy(lhs) && petta_atom_is_falsy(rhs)) {
                            petta_vallist_push_take(out_vals, petta_atom_sym(lc ? "false" : "False"));
                        } else {
                            PettaAtom *bargs[3] = { petta_atom_clone(expr->args[0]), petta_atom_clone(lhs), petta_atom_clone(rhs) };
                            petta_vallist_push_take(out_vals, petta_atom_expr(3, bargs));
                        }
                    }
                }
                petta_vallist_free(&rlist);
            }
            petta_vallist_free(&llist);
            goto done;
        }

        /* 6. case: (case $scrut (($pat1 $body1) ($pat2 $body2) ...)) */
        if (strcmp(op, "case") == 0 && expr->arity == 3 &&
            expr->args[2]->kind == PETTA_ATOM_EXPR) {
            PettaValList slist;
            petta_vallist_init(&slist);
            petta_eval_expr(eng, expr->args[1], &slist);
            PettaAtom *branches = expr->args[2];
            if (slist.count == 0 && eng->status == PETTA_STATUS_OK) {
                for (uint32_t b = 0; b < branches->arity; b++) {
                    PettaAtom *br = branches->args[b];
                    if (br->kind == PETTA_ATOM_EXPR && br->arity == 2 &&
                        br->args[0]->kind == PETTA_ATOM_SYM &&
                        (strcmp(br->args[0]->text, "Empty") == 0 ||
                         strcmp(br->args[0]->text, "empty") == 0 ||
                         strcmp(br->args[0]->text, "%void%") == 0)) {
                        PettaAtom *sub = petta_atom_clone(br->args[1]);
                        petta_vallist_free(&slist);
                        petta_atom_free(owned_expr);
                        owned_expr = sub;
                        expr = owned_expr;
                        goto tail_call;
                    }
                }
                petta_vallist_free(&slist);
                goto done;
            }
            if (slist.count == 1 && eng->status == PETTA_STATUS_OK) {
                for (uint32_t b = 0; b < branches->arity; b++) {
                    PettaAtom *br = branches->args[b];
                    if (br->kind == PETTA_ATOM_EXPR && br->arity == 2) {
                        if (petta_match_pattern(br->args[0], slist.items[0], &shared_env)) {
                            PettaAtom *sub = petta_subst_env(br->args[1], &shared_env);
                            petta_env_free(&shared_env);
                            petta_vallist_free(&slist);
                            petta_atom_free(owned_expr);
                            owned_expr = sub;
                            expr = owned_expr;
                            goto tail_call;
                        }
                    }
                }
                petta_vallist_free(&slist);
                goto done;
            }
            for (uint32_t s = 0; s < slist.count && eng->status == PETTA_STATUS_OK; s++) {
                for (uint32_t b = 0; b < branches->arity; b++) {
                    PettaAtom *br = branches->args[b];
                    if (br->kind == PETTA_ATOM_EXPR && br->arity == 2) {
                        if (petta_match_pattern(br->args[0], slist.items[s], &shared_env)) {
                            PettaAtom *sub = petta_subst_env(br->args[1], &shared_env);
                            petta_env_free(&shared_env);
                            petta_eval_expr(eng, sub, out_vals);
                            petta_atom_free(sub);
                            break; /* First-match semantics for case */
                        }
                    }
                }
            }
            petta_vallist_free(&slist);
            goto done;
        }

        /* 7. superpose / hyperpose & collapse (Non-deterministic multiplicity!) */
        if ((strcmp(op, "superpose") == 0 || strcmp(op, "hyperpose") == 0) &&
            expr->arity == 2 && expr->args[1]->kind == PETTA_ATOM_EXPR) {
            PettaAtom *alts = expr->args[1];
            for (uint32_t i = 0; i < alts->arity && eng->status == PETTA_STATUS_OK; i++) {
                petta_eval_expr(eng, alts->args[i], out_vals);
            }
            goto done;
        }
        if (strcmp(op, "collapse") == 0 && expr->arity == 2) {
            PettaValList inner;
            petta_vallist_init(&inner);
            petta_eval_expr(eng, expr->args[1], &inner);
            PettaAtom *collapsed = petta_atom_expr(inner.count, inner.items);
            free(inner.items);
            inner.items = NULL;
            inner.count = 0;
            inner.cap = 0;
            petta_vallist_push_take(out_vals, collapsed);
            goto done;
        }

        /* 8. Arithmetic & Comparison Builtins (+, -, *, /, %, ==, !=, <, <=, >, >=) with non-deterministic Cartesian product */
        if ((strcmp(op, "+") == 0 || strcmp(op, "-") == 0 ||
             strcmp(op, "*") == 0 || strcmp(op, "/") == 0 ||
             strcmp(op, "%") == 0) && expr->arity > 3) {
            PettaAtom *two_one[1] = { petta_atom_int(2) };
            PettaAtom *fia_args[3] = {
                petta_atom_sym("function_input_arities"),
                petta_atom_sym(op),
                petta_atom_expr(1, two_one)
            };
            PettaAtom *dom_args[3] = {
                petta_atom_sym("domain_error"),
                petta_atom_expr(3, fia_args),
                petta_atom_int((int64_t)expr->arity - 1)
            };
            PettaAtom *err_args[3] = {
                petta_atom_sym("Error"),
                petta_atom_expr(3, dom_args),
                petta_atom_sym("none")
            };
            petta_vallist_push_take(out_vals, petta_atom_expr(3, err_args));
            goto done;
        }
        if ((strcmp(op, "+") == 0 || strcmp(op, "-") == 0 ||
             strcmp(op, "*") == 0 || strcmp(op, "/") == 0 ||
             strcmp(op, "%") == 0 ||
             strcmp(op, "<") == 0 || strcmp(op, "<=") == 0 ||
             strcmp(op, ">") == 0 || strcmp(op, ">=") == 0 ||
             strcmp(op, "==") == 0 || strcmp(op, "!=") == 0) &&
            expr->arity == 3) {
            PettaValList llist, rlist;
            petta_vallist_init(&llist);
            petta_vallist_init(&rlist);
            petta_eval_expr(eng, expr->args[1], &llist);
            if (eng->status == PETTA_STATUS_OK) {
                petta_eval_expr(eng, expr->args[2], &rlist);
            }
            for (uint32_t li = 0; li < llist.count && eng->status == PETTA_STATUS_OK; li++) {
                PettaAtom *lhs = llist.items[li];
                for (uint32_t ri = 0; ri < rlist.count && eng->status == PETTA_STATUS_OK; ri++) {
                    PettaAtom *rhs = rlist.items[ri];
                    if (strcmp(op, "==") == 0) {
                        if (lhs->has_vars || rhs->has_vars) {
                            PettaAtom *sargs[3] = { petta_atom_clone(expr->args[0]), petta_atom_clone(lhs), petta_atom_clone(rhs) };
                            petta_vallist_push_take(out_vals, petta_atom_expr(3, sargs));
                        } else {
                            bool eq = petta_atom_eq(lhs, rhs);
                            petta_vallist_push_take(out_vals, petta_atom_sym(eq ? "True" : "False"));
                        }
                        continue;
                    }
                    if (strcmp(op, "!=") == 0) {
                        if (lhs->has_vars || rhs->has_vars) {
                            PettaAtom *sargs[3] = { petta_atom_clone(expr->args[0]), petta_atom_clone(lhs), petta_atom_clone(rhs) };
                            petta_vallist_push_take(out_vals, petta_atom_expr(3, sargs));
                        } else {
                            bool neq = !petta_atom_eq(lhs, rhs);
                            petta_vallist_push_take(out_vals, petta_atom_sym(neq ? "True" : "False"));
                        }
                        continue;
                    }
                    if (lhs->kind != PETTA_ATOM_INT || rhs->kind != PETTA_ATOM_INT) {
                        double da = 0.0, db = 0.0;
                        bool fa = false, fb = false;
                        if (strcmp(op, "%") != 0 &&
                            petta_atom_as_double(lhs, &da, &fa) &&
                            petta_atom_as_double(rhs, &db, &fb)) {
                            if (strcmp(op, "+") == 0) petta_vallist_push_take(out_vals, petta_atom_float(da + db));
                            else if (strcmp(op, "-") == 0) petta_vallist_push_take(out_vals, petta_atom_float(da - db));
                            else if (strcmp(op, "*") == 0) petta_vallist_push_take(out_vals, petta_atom_float(da * db));
                            else if (strcmp(op, "/") == 0) {
                                if (db == 0.0) {
                                    eng->status = PETTA_STATUS_FAULT;
                                    eng->fault = PETTA_FAULT_DIV_ZERO;
                                    break;
                                }
                                petta_vallist_push_take(out_vals, petta_atom_float(da / db));
                            }
                            else if (strcmp(op, "<") == 0)  petta_vallist_push_take(out_vals, petta_atom_sym(da < db ? "True" : "False"));
                            else if (strcmp(op, "<=") == 0) petta_vallist_push_take(out_vals, petta_atom_sym(da <= db ? "True" : "False"));
                            else if (strcmp(op, ">") == 0)  petta_vallist_push_take(out_vals, petta_atom_sym(da > db ? "True" : "False"));
                            else if (strcmp(op, ">=") == 0) petta_vallist_push_take(out_vals, petta_atom_sym(da >= db ? "True" : "False"));
                            continue;
                        }
                        if (lhs->has_vars || rhs->has_vars) {
                            PettaAtom *sargs[3] = { petta_atom_clone(expr->args[0]), petta_atom_clone(lhs), petta_atom_clone(rhs) };
                            petta_vallist_push_take(out_vals, petta_atom_expr(3, sargs));
                            continue;
                        }
                        eng->status = PETTA_STATUS_FAULT;
                        eng->fault = PETTA_FAULT_TYPE;
                        break;
                    }
                    int64_t a = lhs->ival, b = rhs->ival;
                    if (strcmp(op, "+") == 0) {
                        int64_t sum = (a > 0 && b > 0 && a > INT64_MAX - b) ? INT64_MAX : (a + b);
                        petta_vallist_push_take(out_vals, petta_atom_int(sum));
                    }
                    else if (strcmp(op, "-") == 0) petta_vallist_push_take(out_vals, petta_atom_int(a - b));
                    else if (strcmp(op, "*") == 0) petta_vallist_push_take(out_vals, petta_atom_int(a * b));
                    else if (strcmp(op, "/") == 0) {
                        if (b == 0) {
                            eng->status = PETTA_STATUS_FAULT;
                            eng->fault = PETTA_FAULT_DIV_ZERO;
                            break;
                        }
                        petta_vallist_push_take(out_vals, petta_atom_int(a / b));
                    }
                    else if (strcmp(op, "%") == 0) {
                        if (b == 0) {
                            eng->status = PETTA_STATUS_FAULT;
                            eng->fault = PETTA_FAULT_DIV_ZERO;
                            break;
                        }
                        petta_vallist_push_take(out_vals, petta_atom_int(a % b));
                    }
                    else if (strcmp(op, "<") == 0)  petta_vallist_push_take(out_vals, petta_atom_sym(a < b ? "True" : "False"));
                    else if (strcmp(op, "<=") == 0) petta_vallist_push_take(out_vals, petta_atom_sym(a <= b ? "True" : "False"));
                    else if (strcmp(op, ">") == 0)  petta_vallist_push_take(out_vals, petta_atom_sym(a > b ? "True" : "False"));
                    else if (strcmp(op, ">=") == 0) petta_vallist_push_take(out_vals, petta_atom_sym(a >= b ? "True" : "False"));
                }
            }
            petta_vallist_free(&llist);
            petta_vallist_free(&rlist);
            goto done;
        }

        /* 9. Atomspace Store Operations: add-atom, remove-atom, get-atoms */
        if (strcmp(op, "add-atom") == 0 && expr->arity == 3) {
            if (expr->args[1]->kind == PETTA_ATOM_VAR || expr->args[2]->kind == PETTA_ATOM_VAR) {
                PettaAtom *eargs[3] = {
                    petta_atom_sym("Error"),
                    petta_atom_sym("instantiation_error"),
                    petta_atom_sym("add-atom")
                };
                petta_vallist_push_take(out_vals, petta_atom_expr(3, eargs));
                goto done;
            }
            PettaAtom *eval_sp = NULL;
            const PettaAtom *sp_atom = expr->args[1];
            if (sp_atom->kind == PETTA_ATOM_EXPR) {
                eval_sp = petta_eval_one(eng, sp_atom);
                sp_atom = eval_sp;
            }
            if (sp_atom->kind != PETTA_ATOM_SYM) {
                petta_atom_free(eval_sp);
                PettaAtom *eargs[3] = {
                    petta_atom_sym("Error"),
                    petta_atom_sym("type_error"),
                    petta_atom_sym("add-atom")
                };
                petta_vallist_push_take(out_vals, petta_atom_expr(3, eargs));
                goto done;
            }
            petta_store_add_atom_space(eng, sp_atom->text, expr->args[2]);
            petta_atom_free(eval_sp);
            petta_vallist_push_take(out_vals, petta_atom_sym("Unit"));
            goto done;
        }
        if (strcmp(op, "remove-atom") == 0 && expr->arity == 3) {
            bool bad_eq_var = (expr->args[1]->kind == PETTA_ATOM_SYM &&
                               strcmp(expr->args[1]->text, "&self") == 0 &&
                               expr->args[2]->kind == PETTA_ATOM_EXPR && expr->args[2]->arity == 3 &&
                               expr->args[2]->args[0]->kind == PETTA_ATOM_SYM &&
                               strcmp(expr->args[2]->args[0]->text, "=") == 0 &&
                               expr->args[2]->args[1]->kind == PETTA_ATOM_VAR &&
                               expr->args[2]->args[2]->kind == PETTA_ATOM_VAR);
            if (expr->args[1]->kind == PETTA_ATOM_VAR || expr->args[2]->kind == PETTA_ATOM_VAR || bad_eq_var) {
                PettaAtom *eargs[3] = {
                    petta_atom_sym("Error"),
                    petta_atom_sym("instantiation_error"),
                    petta_atom_sym("remove-atom")
                };
                petta_vallist_push_take(out_vals, petta_atom_expr(3, eargs));
                goto done;
            }
            PettaAtom *eval_sp = NULL;
            const PettaAtom *sp_atom = expr->args[1];
            if (sp_atom->kind == PETTA_ATOM_EXPR) {
                eval_sp = petta_eval_one(eng, sp_atom);
                sp_atom = eval_sp;
            }
            if (sp_atom->kind != PETTA_ATOM_SYM) {
                petta_atom_free(eval_sp);
                PettaAtom *eargs[3] = {
                    petta_atom_sym("Error"),
                    petta_atom_sym("type_error"),
                    petta_atom_sym("remove-atom")
                };
                petta_vallist_push_take(out_vals, petta_atom_expr(3, eargs));
                goto done;
            }
            bool ok = petta_store_remove_atom_space(eng, sp_atom->text, expr->args[2]);
            petta_atom_free(eval_sp);
            petta_vallist_push_take(out_vals, petta_atom_sym(ok ? "True" : "False"));
            goto done;
        }
        if (strcmp(op, "get-atoms") == 0 && expr->arity == 2) {
            const char *space_name = (expr->args[1]->kind == PETTA_ATOM_SYM) ? expr->args[1]->text : "&self";
            for (uint32_t i = 0; i < eng->nstore; i++) {
                if (eng->store[i].alive && petta_space_matches(&eng->store[i], space_name)) {
                    petta_vallist_push_clone(out_vals, eng->store[i].atom);
                }
            }
            goto done;
        }

        /* 10. MeTTa Prime Syntactic Sugar for the 5 Restricted tcalc Sub-Calculi */
        if (petta_eval_subcalc(eng, op, expr, out_vals)) {
            goto done;
        }

        /* 10b. PeTTa Special Forms & Core Tuple/Atom Builtins */
        if (petta_eval_builtin_atomop(eng, op, expr, out_vals)) {
            goto done;
        }
    }

    /* 11. General Function Application / Rewrite Dispatch (Cartesian product over argument alternatives) */
    {
        PettaValList local_arg_lists[8];
        uint32_t local_indices[8];
        PettaAtom *local_tuple_args[8];
        PettaValList *arg_lists = (expr->arity <= 8u)
            ? local_arg_lists
            : (PettaValList *)calloc(expr->arity, sizeof(PettaValList));
        bool single_tuple = true;
        for (uint32_t i = 0; i < expr->arity; i++) {
            petta_vallist_init(&arg_lists[i]);
            bool eval_arg = true;
            const char *req_type = NULL;
            if (i > 0 && head->kind == PETTA_ATOM_SYM && (i - 1u) < 8u) {
                for (uint32_t s = 0; s < eng->nsigs; s++) {
                    if (strcmp(eng->sigs[s].head, head->text) == 0 &&
                        (i - 1u) < eng->sigs[s].param_count) {
                        if (strcmp(eng->sigs[s].param_types[i - 1u], "Atom") == 0) {
                            eval_arg = false;
                        } else if (strcmp(eng->sigs[s].param_types[i - 1u], "Number") == 0) {
                            req_type = "Number";
                        }
                    }
                }
            }
            if (!eval_arg) {
                PettaAtom *ac = petta_atom_clone(expr->args[i]);
                ac->nf_epoch = eng->nrules + (uint32_t)eng->tc_events_admitted + 1u;
                petta_vallist_push_take(&arg_lists[i], ac);
            } else {
                petta_eval_expr(eng, expr->args[i], &arg_lists[i]);
            }
            if (req_type && strcmp(req_type, "Number") == 0 && eng->status == PETTA_STATUS_OK) {
                uint32_t wr = 0;
                for (uint32_t k = 0; k < arg_lists[i].count; k++) {
                    double dv = 0.0;
                    bool df = false;
                    PettaAtom *ak = arg_lists[i].items[k];
                    if (ak->has_vars || petta_atom_as_double(ak, &dv, &df) ||
                        (ak->kind == PETTA_ATOM_EXPR && ak->arity > 0)) {
                        arg_lists[i].items[wr++] = ak;
                    } else {
                        petta_atom_free(ak);
                    }
                }
                arg_lists[i].count = wr;
            }
            if (eng->status != PETTA_STATUS_OK || arg_lists[i].count == 0) {
                for (uint32_t k = 0; k <= i; k++) petta_vallist_free(&arg_lists[k]);
                if (expr->arity > 8u) free(arg_lists);
                goto done;
            }
            if (arg_lists[i].count != 1) single_tuple = false;
        }
        uint32_t *indices = (expr->arity <= 8u)
            ? local_indices
            : (uint32_t *)calloc(expr->arity, sizeof(uint32_t));
        if (expr->arity <= 8u) memset(local_indices, 0, expr->arity * sizeof(uint32_t));
        PettaAtom **tuple_args = (expr->arity <= 8u)
            ? local_tuple_args
            : (PettaAtom **)calloc(expr->arity, sizeof(PettaAtom *));
        while (eng->status == PETTA_STATUS_OK) {
            if (single_tuple) {
                for (uint32_t i = 0; i < expr->arity; i++) {
                    tuple_args[i] = arg_lists[i].items[0];
                    arg_lists[i].items[0] = NULL;
                    arg_lists[i].count = 0;
                }
            } else {
                for (uint32_t i = 0; i < expr->arity; i++) {
                    tuple_args[i] = petta_atom_clone(arg_lists[i].items[indices[i]]);
                }
            }
            PettaAtom *call_term = petta_atom_expr(expr->arity, tuple_args);
            /* 11a. Higher-order application of (|-> ($p1 ... $pk) $body) or curried partial application ((f a...) b...) */
            if (call_term->arity >= 2 && call_term->args[0]->kind == PETTA_ATOM_EXPR) {
                const PettaAtom *cal = call_term->args[0];
                if (cal->arity == 3 && cal->args[0]->kind == PETTA_ATOM_SYM &&
                    strcmp(cal->args[0]->text, "|->") == 0 &&
                    cal->args[1]->kind == PETTA_ATOM_EXPR) {
                    const PettaAtom *params = cal->args[1];
                    const PettaAtom *lbody = cal->args[2];
                    uint32_t nsup = call_term->arity - 1u;
                    uint32_t nbind = (nsup < params->arity) ? nsup : params->arity;
                    PettaEnv lenv;
                    petta_env_init(&lenv);
                    for (uint32_t j = 0; j < nbind; j++) {
                        if (params->args[j]->kind == PETTA_ATOM_VAR) {
                            petta_env_bind(&lenv, params->args[j]->text, call_term->args[j + 1u]);
                        }
                    }
                    PettaAtom *sub_body = petta_subst_env(lbody, &lenv);
                    petta_env_free(&lenv);
                    if (nsup < params->arity) {
                        uint32_t rem = params->arity - nsup;
                        PettaAtom **rparams = (PettaAtom **)calloc(rem, sizeof(PettaAtom *));
                        for (uint32_t j = 0; j < rem; j++) rparams[j] = petta_atom_clone(params->args[nsup + j]);
                        PettaAtom *largs[3] = {
                            petta_atom_sym("|->"),
                            petta_atom_expr(rem, rparams),
                            sub_body
                        };
                        free(rparams);
                        petta_vallist_push_take(out_vals, petta_atom_expr(3, largs));
                        petta_atom_free(call_term);
                    } else if (nsup == params->arity) {
                        petta_eval_expr(eng, sub_body, out_vals);
                        petta_atom_free(sub_body);
                        petta_atom_free(call_term);
                    } else {
                        uint32_t rem = nsup - params->arity;
                        PettaAtom **oargs = (PettaAtom **)calloc(rem + 1u, sizeof(PettaAtom *));
                        oargs[0] = sub_body;
                        for (uint32_t j = 0; j < rem; j++) oargs[j + 1u] = petta_atom_clone(call_term->args[1u + params->arity + j]);
                        PettaAtom *over_call = petta_atom_expr(rem + 1u, oargs);
                        free(oargs);
                        petta_eval_expr(eng, over_call, out_vals);
                        petta_atom_free(over_call);
                        petta_atom_free(call_term);
                    }
                    if (single_tuple) break;
                    goto advance_odometer;
                }
                if (cal->arity >= 1 && cal->args[0]->kind == PETTA_ATOM_SYM) {
                    const char *fn = cal->args[0]->text;
                    uint32_t flat_arity = cal->arity + call_term->arity - 1u;
                    bool is_curried = petta_has_user_rule(eng, fn, flat_arity) ||
                                      petta_has_higher_arity_rule(eng, fn, flat_arity) ||
                                      (flat_arity == 3u &&
                                       (strcmp(fn, "+") == 0 || strcmp(fn, "-") == 0 ||
                                        strcmp(fn, "*") == 0 || strcmp(fn, "/") == 0 ||
                                        strcmp(fn, "%") == 0 || strcmp(fn, "<") == 0 ||
                                        strcmp(fn, "<=") == 0 || strcmp(fn, ">") == 0 ||
                                        strcmp(fn, ">=") == 0 || strcmp(fn, "==") == 0 ||
                                        strcmp(fn, "!=") == 0 || strcmp(fn, "=") == 0 ||
                                        strcmp(fn, "=alpha") == 0 || strcmp(fn, "=@=") == 0 ||
                                        strcmp(fn, "or") == 0 || strcmp(fn, "and") == 0 ||
                                        strcmp(fn, "xor") == 0 || strcmp(fn, "cons") == 0 ||
                                        strcmp(fn, "cons-atom") == 0 || strcmp(fn, "append") == 0));
                    if (is_curried) {
                        PettaAtom **fargs = (PettaAtom **)calloc(flat_arity, sizeof(PettaAtom *));
                        for (uint32_t j = 0; j < cal->arity; j++) fargs[j] = petta_atom_clone(cal->args[j]);
                        for (uint32_t j = 1; j < call_term->arity; j++) fargs[cal->arity + j - 1u] = petta_atom_clone(call_term->args[j]);
                        PettaAtom *flat_call = petta_atom_expr(flat_arity, fargs);
                        free(fargs);
                        petta_atom_free(call_term);
                        petta_eval_expr(eng, flat_call, out_vals);
                        petta_atom_free(flat_call);
                        if (single_tuple) break;
                        goto advance_odometer;
                    }
                }
            }
            uint32_t call_arity = call_term->arity;
            uint32_t call_head_hash = (call_arity > 0 && call_term->args[0]->kind == PETTA_ATOM_SYM)
                ? petta_str_fnv1a(call_term->args[0]->text) : 0u;
            bool ret_is_atom = false;
            bool has_typed_sig = (call_arity > 0 && call_term->args[0]->kind == PETTA_ATOM_SYM &&
                                  petta_call_has_arrow_sig(eng, call_term->args[0]->text, call_arity, &ret_is_atom));
            if (has_typed_sig && !petta_typecheck_call_and_out(eng, call_term, NULL)) {
                petta_atom_free(call_term);
                if (single_tuple) break;
                goto advance_odometer;
            }
            bool can_match_any_rule = true;
            if (call_arity > 0 && call_term->args[0]->kind == PETTA_ATOM_VAR && !eng->has_var_head_rules) {
                can_match_any_rule = false;
            }
            if (call_head_hash != 0u && !eng->has_var_head_rules) {
                uint32_t b1 = call_head_hash & 255u;
                uint32_t b2 = (call_head_hash >> 8) & 255u;
                if (((eng->rule_head_bloom[b1 >> 6] & (1ULL << (b1 & 63u))) == 0ULL) ||
                    ((eng->rule_head_bloom[b2 >> 6] & (1ULL << (b2 & 63u))) == 0ULL)) {
                    can_match_any_rule = false;
                }
            }
            bool is_trans_rule = false;
            if (call_arity > 0 && call_term->args[0]->kind == PETTA_ATOM_SYM) {
                for (uint32_t tr = 0; tr < eng->ntranslator_rules; tr++) {
                    if (eng->translator_rules[tr][0] &&
                        strcmp(eng->translator_rules[tr], call_term->args[0]->text) == 0) {
                        is_trans_rule = true;
                        break;
                    }
                }
            }
            bool use_bucket = (call_head_hash != 0u && !eng->has_var_head_rules);
            if (single_tuple && !has_typed_sig && !is_trans_rule) {
                PettaAtom *first_rhs = NULL;
                bool multi_match = false;
                if (can_match_any_rule) {
                    bool prev_cut = eng->cut_fired;
                    eng->cut_fired = false;
                    uint32_t r1 = use_bucket ? eng->rule_bucket_head[call_head_hash & 255u] : (eng->nrules ? 1u : 0u);
                    while (r1 != 0u && eng->status == PETTA_STATUS_OK) {
                        uint32_t r = r1 - 1u;
                        r1 = use_bucket ? eng->rules[r].next_in_bucket : (r + 1u < eng->nrules ? r + 2u : 0u);
                        if (eng->rules[r].removed) continue;
                        if (eng->rules[r].arity != 0u && eng->rules[r].arity != call_arity) continue;
                        if (call_head_hash != 0u && eng->rules[r].head_hash != 0u &&
                            eng->rules[r].head_hash != call_head_hash) continue;
                        const PettaAtom *rlhs = eng->rules[r].lhs;
                        const PettaAtom *rrhs = eng->rules[r].rhs;
                        PettaAtom *flhs = NULL, *frhs = NULL;
                        if (call_term->has_vars) {
                            uint32_t fseq = ++eng->var_freshen_seq;
                            flhs = petta_freshen_vars(rlhs, fseq);
                            frhs = petta_freshen_vars(rrhs, fseq);
                            rlhs = flhs;
                            rrhs = frhs;
                        }
                        bool call_has_compound_vars = false;
                        if (call_term->has_vars) {
                            for (uint32_t ci = 1u; ci < call_arity; ci++) {
                                if (call_term->args[ci]->kind == PETTA_ATOM_EXPR && call_term->args[ci]->has_vars) {
                                    call_has_compound_vars = true;
                                    break;
                                }
                            }
                        }
                        bool r_matched = call_has_compound_vars
                            ? petta_unify_pattern(rlhs, call_term, &shared_env)
                            : petta_match_pattern(rlhs, call_term, &shared_env);
                        if (r_matched) {
                            PettaAtom *rhs_inst = call_has_compound_vars
                                ? petta_subst_env_trans(rrhs, &shared_env)
                                : petta_subst_env(rrhs, &shared_env);
                            petta_env_free(&shared_env);
                            petta_atom_free(flhs);
                            petta_atom_free(frhs);
                            if (!first_rhs) {
                                first_rhs = rhs_inst;
                            } else {
                                if (!multi_match) {
                                    multi_match = true;
                                    petta_eval_expr(eng, first_rhs, out_vals);
                                    petta_atom_free(first_rhs);
                                    if (eng->cut_fired) {
                                        petta_atom_free(rhs_inst);
                                        break;
                                    }
                                }
                                petta_eval_expr(eng, rhs_inst, out_vals);
                                petta_atom_free(rhs_inst);
                                if (eng->cut_fired) break;
                            }
                        } else {
                            petta_atom_free(flhs);
                            petta_atom_free(frhs);
                        }
                    }
                    eng->cut_fired = prev_cut;
                }
                if (first_rhs && !multi_match) {
                    petta_atom_free(call_term);
                    if (expr->arity > 8u) {
                        free(tuple_args);
                        free(indices);
                        for (uint32_t i = 0; i < expr->arity; i++) petta_vallist_free(&arg_lists[i]);
                        free(arg_lists);
                    } else {
                        for (uint32_t i = 0; i < expr->arity; i++) petta_vallist_free(&arg_lists[i]);
                    }
                    petta_atom_free(owned_expr);
                    owned_expr = first_rhs;
                    expr = owned_expr;
                    goto tail_call;
                }
                if (!first_rhs && !multi_match && call_arity >= 2u &&
                    call_term->args[0]->kind == PETTA_ATOM_SYM) {
                    const char *fn = call_term->args[0]->text;
                    uint32_t sub_arity = 0u;
                    for (uint32_t k = call_arity - 1u; k >= 1u; k--) {
                        if (petta_has_user_rule(eng, fn, k)) { sub_arity = k; break; }
                    }
                    if (sub_arity >= 1u) {
                        PettaAtom **pargs = (PettaAtom **)calloc(sub_arity, sizeof(PettaAtom *));
                        for (uint32_t j = 0; j < sub_arity; j++) pargs[j] = petta_atom_clone(call_term->args[j]);
                        PettaAtom *prefix = petta_atom_expr(sub_arity, pargs);
                        free(pargs);
                        uint32_t rem = call_arity - sub_arity;
                        PettaAtom **oargs = (PettaAtom **)calloc(rem + 1u, sizeof(PettaAtom *));
                        oargs[0] = prefix;
                        for (uint32_t j = 0; j < rem; j++) oargs[j + 1u] = petta_atom_clone(call_term->args[sub_arity + j]);
                        PettaAtom *over_call = petta_atom_expr(rem + 1u, oargs);
                        free(oargs);
                        petta_atom_free(call_term);
                        if (expr->arity > 8u) {
                            free(tuple_args);
                            free(indices);
                            for (uint32_t i = 0; i < expr->arity; i++) petta_vallist_free(&arg_lists[i]);
                            free(arg_lists);
                        } else {
                            for (uint32_t i = 0; i < expr->arity; i++) petta_vallist_free(&arg_lists[i]);
                        }
                        petta_atom_free(owned_expr);
                        owned_expr = over_call;
                        expr = owned_expr;
                        goto tail_call;
                    }
                }
                if (!first_rhs) {
                    petta_vallist_push_take(out_vals, call_term);
                } else {
                    petta_atom_free(call_term);
                }
                break;
            }
            bool any_rule_matched = false;
            if (can_match_any_rule) {
                bool prev_cut = eng->cut_fired;
                eng->cut_fired = false;
                uint32_t r1 = use_bucket ? eng->rule_bucket_head[call_head_hash & 255u] : (eng->nrules ? 1u : 0u);
                while (r1 != 0u && eng->status == PETTA_STATUS_OK) {
                    uint32_t r = r1 - 1u;
                    r1 = use_bucket ? eng->rules[r].next_in_bucket : (r + 1u < eng->nrules ? r + 2u : 0u);
                    if (eng->rules[r].removed) continue;
                    if (eng->rules[r].arity != 0u && eng->rules[r].arity != call_arity) continue;
                    if (call_head_hash != 0u && eng->rules[r].head_hash != 0u &&
                        eng->rules[r].head_hash != call_head_hash) continue;
                    const PettaAtom *rlhs = eng->rules[r].lhs;
                    const PettaAtom *rrhs = eng->rules[r].rhs;
                    PettaAtom *flhs = NULL, *frhs = NULL;
                    if (call_term->has_vars) {
                        uint32_t fseq = ++eng->var_freshen_seq;
                        flhs = petta_freshen_vars(rlhs, fseq);
                        frhs = petta_freshen_vars(rrhs, fseq);
                        rlhs = flhs;
                        rrhs = frhs;
                    }
                    bool call_has_compound_vars = false;
                    if (call_term->has_vars) {
                        for (uint32_t ci = 1u; ci < call_arity; ci++) {
                            if (call_term->args[ci]->kind == PETTA_ATOM_EXPR && call_term->args[ci]->has_vars) {
                                call_has_compound_vars = true;
                                break;
                            }
                        }
                    }
                    bool r_matched = call_has_compound_vars
                        ? petta_unify_pattern(rlhs, call_term, &shared_env)
                        : petta_match_pattern(rlhs, call_term, &shared_env);
                    if (r_matched) {
                        any_rule_matched = true;
                        PettaAtom *rhs_inst = call_has_compound_vars
                            ? petta_subst_env_trans(rrhs, &shared_env)
                            : petta_subst_env(rrhs, &shared_env);
                        petta_env_free(&shared_env);
                        petta_atom_free(flhs);
                        petta_atom_free(frhs);
                        if (is_trans_rule) {
                            PettaValList tvals;
                            petta_vallist_init(&tvals);
                            petta_eval_expr(eng, rhs_inst, &tvals);
                            petta_atom_free(rhs_inst);
                            for (uint32_t k = 0; k < tvals.count && eng->status == PETTA_STATUS_OK; k++) {
                                tvals.items[k]->nf_epoch = 0;
                                petta_eval_expr(eng, tvals.items[k], out_vals);
                            }
                            petta_vallist_free(&tvals);
                        } else if (ret_is_atom &&
                                   !(rhs_inst->kind == PETTA_ATOM_EXPR && rhs_inst->arity == 3 &&
                                     rhs_inst->args[0]->kind == PETTA_ATOM_SYM &&
                                     strcmp(rhs_inst->args[0]->text, "case") == 0)) {
                            rhs_inst->nf_epoch = eng->nrules + (uint32_t)eng->tc_events_admitted + 1u;
                            petta_vallist_push_take(out_vals, rhs_inst);
                        } else if (has_typed_sig) {
                            PettaValList rvals;
                            petta_vallist_init(&rvals);
                            petta_eval_expr(eng, rhs_inst, &rvals);
                            petta_atom_free(rhs_inst);
                            for (uint32_t k = 0; k < rvals.count; k++) {
                                if (petta_typecheck_call_and_out(eng, call_term, rvals.items[k])) {
                                    petta_vallist_push_clone(out_vals, rvals.items[k]);
                                }
                            }
                            petta_vallist_free(&rvals);
                        } else {
                            petta_eval_expr(eng, rhs_inst, out_vals);
                            petta_atom_free(rhs_inst);
                        }
                        if (eng->cut_fired) break;
                    } else {
                        petta_atom_free(flhs);
                        petta_atom_free(frhs);
                    }
                }
                eng->cut_fired = prev_cut;
            }
            if (!any_rule_matched && call_arity >= 2u && call_term->args[0]->kind == PETTA_ATOM_SYM) {
                const char *fn = call_term->args[0]->text;
                uint32_t sub_arity = 0u;
                for (uint32_t k = call_arity - 1u; k >= 1u; k--) {
                    if (petta_has_user_rule(eng, fn, k)) { sub_arity = k; break; }
                }
                if (sub_arity >= 1u) {
                    PettaAtom **pargs = (PettaAtom **)calloc(sub_arity, sizeof(PettaAtom *));
                    for (uint32_t j = 0; j < sub_arity; j++) pargs[j] = petta_atom_clone(call_term->args[j]);
                    PettaAtom *prefix = petta_atom_expr(sub_arity, pargs);
                    free(pargs);
                    uint32_t rem = call_arity - sub_arity;
                    PettaAtom **oargs = (PettaAtom **)calloc(rem + 1u, sizeof(PettaAtom *));
                    oargs[0] = prefix;
                    for (uint32_t j = 0; j < rem; j++) oargs[j + 1u] = petta_atom_clone(call_term->args[sub_arity + j]);
                    PettaAtom *over_call = petta_atom_expr(rem + 1u, oargs);
                    free(oargs);
                    petta_atom_free(call_term);
                    petta_eval_expr(eng, over_call, out_vals);
                    petta_atom_free(over_call);
                    any_rule_matched = true;
                } else {
                    petta_vallist_push_take(out_vals, call_term);
                }
            } else if (!any_rule_matched) {
                petta_vallist_push_take(out_vals, call_term);
            } else {
                petta_atom_free(call_term);
            }
            if (single_tuple) break;
advance_odometer:
            /* Advance odometer over argument value lists */
            if (eng->max_steps > 0 && eng->steps_executed >= eng->max_steps) {
                eng->status = PETTA_STATUS_BUDGET_EXHAUSTED;
                break;
            }
            eng->steps_executed++;
            int32_t pos = (int32_t)expr->arity - 1;
            while (pos >= 0) {
                indices[pos]++;
                if (indices[pos] < arg_lists[pos].count) break;
                indices[pos] = 0;
                pos--;
            }
            if (pos < 0) break;
        }
        if (expr->arity > 8u) {
            free(tuple_args);
            free(indices);
            for (uint32_t i = 0; i < expr->arity; i++) petta_vallist_free(&arg_lists[i]);
            free(arg_lists);
        } else {
            for (uint32_t i = 0; i < expr->arity; i++) petta_vallist_free(&arg_lists[i]);
        }
    }

done:
    petta_atom_free(owned_expr);
}

static inline void petta_eval_expr(
    PettaTcalcEngine *eng,
    const PettaAtom *expr,
    PettaValList *out_vals)
{
    if (!expr || eng->status != PETTA_STATUS_OK) return;
    uint32_t max_d = eng->max_depth ? eng->max_depth : 512u;
    if (eng->depth >= max_d) {
        eng->status = PETTA_STATUS_BUDGET_EXHAUSTED;
        return;
    }
    uint32_t out_start = out_vals->count;
    eng->depth++;
    petta_eval_expr_inner(eng, expr, out_vals);
    eng->depth--;
    if (eng->status == PETTA_STATUS_OK) {
        uint32_t cur_epoch = eng->nrules + (uint32_t)eng->tc_events_admitted + 1u;
        for (uint32_t k = out_start; k < out_vals->count; k++) {
            petta_atom_mark_nf(out_vals->items[k], cur_epoch);
        }
    }
}

/* Load a multi-statement PeTTa program into a target space (definitions and !(...) directives) */
static inline bool petta_load_space_program(
    PettaTcalcEngine *eng,
    const char *space_name,
    const char *program_text,
    PettaValList *out_last_result)
{
    if (!space_name || !space_name[0]) space_name = "&self";
    bool is_self = (strcmp(space_name, "&self") == 0);
    const char *p = program_text;
    while (true) {
        p = petta_skip_ws(p);
        if (!*p) break;
        bool is_bang = false;
        if (*p == '!') {
            is_bang = true;
            p++;
        }
        PettaAtom *stmt = petta_parse_expr(&p);
        if (!stmt) {
            eng->status = PETTA_STATUS_FAULT;
            eng->fault = PETTA_FAULT_TYPE;
            return false;
        }
        PettaValList vl;
        petta_vallist_init(&vl);
        if (!is_bang &&
            (!is_self ||
             !(stmt->kind == PETTA_ATOM_EXPR && stmt->arity >= 1 &&
               stmt->args[0]->kind == PETTA_ATOM_SYM &&
               (strcmp(stmt->args[0]->text, "=") == 0 || strcmp(stmt->args[0]->text, ":") == 0)))) {
            petta_store_add_atom_space(eng, space_name, stmt);
        } else {
            uint32_t saved_depth = eng->depth;
            eng->depth = 0u;
            petta_eval_expr(eng, stmt, &vl);
            eng->depth = saved_depth;
        }
        petta_atom_free(stmt);
        if (is_bang && out_last_result) {
            petta_vallist_free(out_last_result);
            *out_last_result = vl;
        } else {
            petta_vallist_free(&vl);
        }
        if (eng->status != PETTA_STATUS_OK) return false;
    }
    return true;
}

static inline bool petta_load_and_run_program(
    PettaTcalcEngine *eng,
    const char *program_text,
    PettaValList *out_last_result)
{
    return petta_load_space_program(eng, "&self", program_text, out_last_result);
}

#endif /* PETTA_TCALC_EVAL_H */

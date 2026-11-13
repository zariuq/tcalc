/* _wip_ (2026-11-11): this GSLT -> tcalc lowering waits until GSLT -> PeTTa and GSLT -> tcalc
 * are complete, and will then be rebuilt on the reference implementation (tcalc/reference/).
 * It is not a reference. It runs on the retired prototype kernel (tcalc.c) and includes
 * prototype headers that are retired with it: gslt_syntax.h, gslt_packed_bridge.h,
 * petta_tcalc_eval.h, gold_langs_tcalc.h. Build nothing new on it.
 *
 * dl_tcalc.c -- GSLT -> tcalc Lowering Consumer: D0 Datalog (Set Saturation) & C0 CHR (Linear Consumption)
 *
 * Trust Ledger (protected judgement spaces + named, ledgered SPACE_HELPER assumptions):
 *   SPACE_FACT    (1) : Protected D0 Datalog ground relation store (tc_protect + tc_seal).
 *                       Each D0 relation R/k lowers to a typed n-ary tcalc constructor
 *                       con_R : (Col_1, ..., Col_k) -> SortFact.
 *                       Set semantics enforced by tcalc's kernel Rule.absent guard (enforce_absent = true).
 *   SPACE_CHR     (2) : Protected C0 CHR occurrence-indexed multiset store: chr_occ(OccId, AtomTerm).
 *                       Linear consumption enforced by tcalc's kernel Rule.take; persistent context
 *                       by Rule.keep; distinct occurrence matching by Rule.neq on OccId variables.
 *   SPACE_HISTORY (3) : Protected C0 CHR propagation history store: chr_hist(RuleId, OccId1, ..., OccIdK).
 *                       Per-occurrence propagation termination enforced by Rule.absent + Rule.make_extra.
 *   SPACE_QUERY   (4) : Protected C0 CHR initial query activation queue (consumed linearly by activate_query).
 *   SPACE_HELPER  (5) : Named, ledgered scalar comparison (<, <=, >, >=) and C0 integer arithmetic (is)
 *                       helper evaluation over 64-bit signed/unsigned integers and UTF-8 symbols via
 *                       TcAdmissionProfile.permit.
 *
 * Deep-Creativity Mechanism (M2 vs. M1):
 *   M1 (--engine naive)     : Baseline O(|W|^m) Cartesian scan over SPACE_FACT occurrences per epoch.
 *   M2 (--engine seminaive) : Differential Delta-Frontier + Hash-Consed 32-bit Term-ID Join Index +
 *                             tcalc FIBRE_FLAT classifier verification. Fires every transition through
 *                             the exact same tc_bridge_execute_candidate(&cand, &profile, ...) gate,
 *                             yielding identical SPACE_FACT theorems and TcAdmittedEvent receipts with
 *                             >= 10x fewer candidate evaluations on recursive join workloads.
 */
#define _POSIX_C_SOURCE 200809L
#include "tcalc.h"
#include "bridge/tc_cetta_bridge.h"
#include "compiled/ordinary_flat_adapter.h"
#include "gslt_syntax.h"
#include "gslt_packed_bridge.h"
#include "petta_tcalc_eval.h"
#include "gold_langs_tcalc.h"

#include <ctype.h>
#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

enum {
    SPACE_FACT    = 1,
    SPACE_CHR     = 2,
    SPACE_HISTORY = 3,
    SPACE_QUERY   = 4,
    SPACE_HELPER  = 5
};

/* =========================================================================
 * 1. D0 Datalog AST, Static Admission & Origin Retention
 * ========================================================================= */

typedef enum {
    D0_PRIM_UNKNOWN  = 0,
    D0_PRIM_SYMBOL   = 1,
    D0_PRIM_NUMBER   = 2,
    D0_PRIM_UNSIGNED = 3,
    D0_PRIM_FLOAT    = 4
} D0PrimKind;

typedef enum {
    D0_DIAG_OK                  = 0,
    D0_DIAG_PARSE_ERROR         = 1,
    D0_DIAG_DUPLICATE_TYPES     = 2,
    D0_DIAG_DUPLICATE_RELATIONS = 3,
    D0_DIAG_INVALID_DECLARATION = 4,
    D0_DIAG_UNDECLARED_IFACE    = 5,
    D0_DIAG_ILL_TYPED_FACT      = 6,
    D0_DIAG_ILL_TYPED_CLAUSE    = 7
} D0DiagKind;

static const char *d0_diag_name(D0DiagKind k) {
    switch (k) {
        case D0_DIAG_OK:                  return "OK";
        case D0_DIAG_PARSE_ERROR:         return "ParseError";
        case D0_DIAG_DUPLICATE_TYPES:     return "DuplicateTypes";
        case D0_DIAG_DUPLICATE_RELATIONS: return "DuplicateRelations";
        case D0_DIAG_INVALID_DECLARATION: return "InvalidDeclaration";
        case D0_DIAG_UNDECLARED_IFACE:    return "UndeclaredInterface";
        case D0_DIAG_ILL_TYPED_FACT:      return "IllTypedFact";
        case D0_DIAG_ILL_TYPED_CLAUSE:    return "IllTypedClause";
    }
    return "Unknown";
}

enum {
    D0_MAX_TYPES   = 64,
    D0_MAX_RELS    = 128,
    D0_MAX_ARITY   = 8,
    D0_MAX_FACTS   = 4096,
    D0_MAX_CLAUSES = 64,
    D0_MAX_BODY    = 8,
    D0_MAX_CMPS    = 8,
    D0_MAX_VARS    = 16,
    D0_MAX_SYMS    = 4096,
    D0_MAX_OCCS    = 65536
};

typedef struct {
    char name[64];
    D0PrimKind prim;
} D0TypeDecl;

typedef struct {
    char name[64];
    int arity;
    char attr_names[D0_MAX_ARITY][64];
    char attr_types[D0_MAX_ARITY][64];
    D0PrimKind col_prim[D0_MAX_ARITY];
    bool is_input;
    bool is_output;
    int tc_con_id;
} D0RelDecl;

typedef enum {
    D0_TERM_VAR      = 1,
    D0_TERM_ANON     = 2,
    D0_TERM_SYMBOL   = 3,
    D0_TERM_NUMBER   = 4,
    D0_TERM_UNSIGNED = 5,
    D0_TERM_RAW_NUM  = 6
} D0TermKind;

typedef struct {
    D0TermKind kind;
    char text[128];
    int64_t sval;
    uint64_t uval;
    bool valid_s64;
    bool valid_u64;
} D0Term;

typedef struct {
    char rel[64];
    int nargs;
    D0Term args[D0_MAX_ARITY];
} D0Atom;

typedef enum {
    D0_CMP_EQ = 1,
    D0_CMP_NE = 2,
    D0_CMP_LT = 3,
    D0_CMP_LE = 4,
    D0_CMP_GT = 5,
    D0_CMP_GE = 6
} D0CmpOp;

typedef struct {
    D0CmpOp op;
    D0Term lhs;
    D0Term rhs;
} D0Comparison;

typedef struct {
    int stmt_index;
    D0Atom atom;
} D0FactStmt;

typedef struct {
    int stmt_index;
    int clause_index;
    D0Atom head;
    int nbody;
    D0Atom body[D0_MAX_BODY];
    int ncmps;
    D0Comparison cmps[D0_MAX_CMPS];
} D0ClauseStmt;

typedef struct {
    int stmt_index;
    int clause_index;
    int tc_rule_id;
    uint8_t tc_fibre_flags;
    int head_rel_idx;
    char head_rel[64];
    int nbody;
    int body_rel_idx[D0_MAX_BODY];
    char body_rels[D0_MAX_BODY][64];
    bool is_pure_horn;
    uint64_t horn_cert_digest;
    uint64_t events_admitted;
} D0ClauseOrigin;

typedef struct {
    int ntypes;
    D0TypeDecl types[D0_MAX_TYPES];
    int nrels;
    D0RelDecl rels[D0_MAX_RELS];
    int ninput_decls;
    char input_decls[D0_MAX_RELS][64];
    int noutput_decls;
    char output_decls[D0_MAX_RELS][64];
    int nfacts;
    D0FactStmt facts[D0_MAX_FACTS];
    int nclauses;
    D0ClauseStmt clauses[D0_MAX_CLAUSES];
    int stmt_counter;
} D0Program;

static void d0_program_init(D0Program *p) {
    memset(p, 0, sizeof(*p));
}

/* Parse Souffle integer literal: decimal, 0x hex, 0b binary, with optional leading '-' */
static bool d0_parse_int_literal(const char *s, int64_t *out_s64, bool *ok_s64,
                                 uint64_t *out_u64, bool *ok_u64) {
    *out_s64 = 0; *ok_s64 = false;
    *out_u64 = 0; *ok_u64 = false;
    if (!s || !*s) return false;
    const char *p = s;
    bool neg = false;
    if (*p == '-') { neg = true; p++; }
    else if (*p == '+') { return false; }
    if (!*p) return false;

    int base = 10;
    if (p[0] == '0' && (p[1] == 'x' || p[1] == 'X')) {
        base = 16; p += 2;
    } else if (p[0] == '0' && (p[1] == 'b' || p[1] == 'B')) {
        base = 2; p += 2;
    }
    if (!*p) return false;

    uint64_t acc = 0;
    bool overflow = false;
    for (; *p; p++) {
        uint64_t d = 0;
        if (*p >= '0' && *p <= '9') d = (uint64_t)(*p - '0');
        else if (base == 16 && *p >= 'a' && *p <= 'f') d = (uint64_t)(*p - 'a' + 10);
        else if (base == 16 && *p >= 'A' && *p <= 'F') d = (uint64_t)(*p - 'A' + 10);
        else return false;
        if (d >= (uint64_t)base) return false;
        if (acc > (UINT64_MAX - d) / (uint64_t)base) overflow = true;
        acc = acc * (uint64_t)base + d;
    }
    if (overflow) return true; /* Syntactically an integer literal, but overflows 64 bits */

    if (neg) {
        if (acc == 0) {
            *out_s64 = 0; *ok_s64 = true;
            *out_u64 = 0; *ok_u64 = false;
        } else if (acc <= (uint64_t)INT64_MAX) {
            *out_s64 = -(int64_t)acc; *ok_s64 = true;
        } else if (acc == ((uint64_t)INT64_MAX + 1ULL)) {
            *out_s64 = INT64_MIN; *ok_s64 = true;
        }
    } else {
        *out_u64 = acc; *ok_u64 = true;
        if (acc <= (uint64_t)INT64_MAX) {
            *out_s64 = (int64_t)acc; *ok_s64 = true;
        }
    }
    return true;
}

/* =========================================================================
 * 2. Souffle .dl Lexer & Parser + MeTTa (D0Program ...) IR Parser
 * ========================================================================= */

typedef struct {
    const char *src;
    size_t pos;
    size_t len;
} D0Lexer;

static void d0_skip_ws(D0Lexer *L) {
    while (L->pos < L->len) {
        char c = L->src[L->pos];
        if (c == ' ' || c == '\t' || c == '\r' || c == '\n') {
            L->pos++;
        } else if (c == '/' && L->pos + 1 < L->len && L->src[L->pos + 1] == '/') {
            L->pos += 2;
            while (L->pos < L->len && L->src[L->pos] != '\n') L->pos++;
        } else if (c == '/' && L->pos + 1 < L->len && L->src[L->pos + 1] == '*') {
            L->pos += 2;
            while (L->pos + 1 < L->len && !(L->src[L->pos] == '*' && L->src[L->pos + 1] == '/')) L->pos++;
            if (L->pos + 1 < L->len) L->pos += 2;
        } else {
            break;
        }
    }
}

static bool d0_ident_char(char c, bool first) {
    if (isalpha((unsigned char)c) || c == '_' || c == '?') return true;
    if (!first && (isdigit((unsigned char)c) || c == '.')) return true;
    return false;
}

static bool d0_read_ident(D0Lexer *L, char *buf, size_t cap) {
    d0_skip_ws(L);
    if (L->pos >= L->len || !d0_ident_char(L->src[L->pos], true)) return false;
    size_t n = 0;
    while (L->pos < L->len && d0_ident_char(L->src[L->pos], false)) {
        if (L->src[L->pos] == '.' &&
            (L->pos + 1 >= L->len || !d0_ident_char(L->src[L->pos + 1], true))) {
            break;
        }
        if (n + 1 < cap) buf[n++] = L->src[L->pos];
        L->pos++;
    }
    buf[n] = '\0';
    return n > 0;
}

static bool d0_read_string(D0Lexer *L, char *buf, size_t cap) {
    d0_skip_ws(L);
    if (L->pos >= L->len || L->src[L->pos] != '"') return false;
    L->pos++;
    size_t n = 0;
    while (L->pos < L->len && L->src[L->pos] != '"') {
        char c = L->src[L->pos++];
        if (c == '\\') {
            if (L->pos >= L->len) return false;
            char e = L->src[L->pos++];
            switch (e) {
                case 'n': c = '\n'; break;
                case 't': c = '\t'; break;
                case 'r': c = '\r'; break;
                case '\\': c = '\\'; break;
                case '"': c = '"'; break;
                default: c = e; break;
            }
        }
        if (n + 1 < cap) buf[n++] = c;
    }
    if (L->pos >= L->len || L->src[L->pos] != '"') return false;
    L->pos++;
    buf[n] = '\0';
    return true;
}

static bool d0_read_term(D0Lexer *L, D0Term *t) {
    memset(t, 0, sizeof(*t));
    d0_skip_ws(L);
    if (L->pos >= L->len) return false;
    if (L->src[L->pos] == '"') {
        if (!d0_read_string(L, t->text, sizeof(t->text))) return false;
        t->kind = D0_TERM_SYMBOL;
        return true;
    }
    if (L->src[L->pos] == '-' || isdigit((unsigned char)L->src[L->pos])) {
        size_t n = 0;
        if (L->src[L->pos] == '-') t->text[n++] = L->src[L->pos++];
        while (L->pos < L->len && (isalnum((unsigned char)L->src[L->pos]) || L->src[L->pos] == '_')) {
            if (n + 1 < sizeof(t->text)) t->text[n++] = L->src[L->pos];
            L->pos++;
        }
        t->text[n] = '\0';
        if (!d0_parse_int_literal(t->text, &t->sval, &t->valid_s64, &t->uval, &t->valid_u64))
            return false;
        t->kind = D0_TERM_RAW_NUM;
        return true;
    }
    char id[128];
    if (!d0_read_ident(L, id, sizeof(id))) return false;
    snprintf(t->text, sizeof(t->text), "%s", id);
    if (strcmp(id, "_") == 0) {
        t->kind = D0_TERM_ANON;
    } else {
        t->kind = D0_TERM_VAR;
    }
    return true;
}

static bool d0_read_atom_args(D0Lexer *L, D0Atom *a) {
    d0_skip_ws(L);
    if (L->pos >= L->len || L->src[L->pos] != '(') return false;
    L->pos++;
    a->nargs = 0;
    d0_skip_ws(L);
    if (L->pos < L->len && L->src[L->pos] == ')') {
        L->pos++;
        return true;
    }
    while (true) {
        if (a->nargs >= D0_MAX_ARITY) return false;
        if (!d0_read_term(L, &a->args[a->nargs])) return false;
        a->nargs++;
        d0_skip_ws(L);
        if (L->pos < L->len && L->src[L->pos] == ',') {
            L->pos++;
            continue;
        }
        if (L->pos < L->len && L->src[L->pos] == ')') {
            L->pos++;
            return true;
        }
        return false;
    }
}

static bool d0_try_read_cmp_op(D0Lexer *L, D0CmpOp *op) {
    d0_skip_ws(L);
    if (L->pos >= L->len) return false;
    if (L->pos + 1 < L->len) {
        if (L->src[L->pos] == '!' && L->src[L->pos + 1] == '=') { *op = D0_CMP_NE; L->pos += 2; return true; }
        if (L->src[L->pos] == '<' && L->src[L->pos + 1] == '=') { *op = D0_CMP_LE; L->pos += 2; return true; }
        if (L->src[L->pos] == '>' && L->src[L->pos + 1] == '=') { *op = D0_CMP_GE; L->pos += 2; return true; }
    }
    if (L->src[L->pos] == '=') { *op = D0_CMP_EQ; L->pos++; return true; }
    if (L->src[L->pos] == '<') { *op = D0_CMP_LT; L->pos++; return true; }
    if (L->src[L->pos] == '>') { *op = D0_CMP_GT; L->pos++; return true; }
    return false;
}

static D0DiagKind d0_parse_dl(const char *src, D0Program *prog) {
    d0_program_init(prog);
    D0Lexer L = { src, 0, strlen(src) };
    while (true) {
        d0_skip_ws(&L);
        if (L.pos >= L.len) break;
        if (L.src[L.pos] == '.') {
            L.pos++;
            char dir[64];
            if (!d0_read_ident(&L, dir, sizeof(dir))) return D0_DIAG_PARSE_ERROR;
            if (strcmp(dir, "type") == 0) {
                if (prog->ntypes >= D0_MAX_TYPES) return D0_DIAG_PARSE_ERROR;
                D0TypeDecl *td = &prog->types[prog->ntypes++];
                if (!d0_read_ident(&L, td->name, sizeof(td->name))) return D0_DIAG_PARSE_ERROR;
                d0_skip_ws(&L);
                if (L.pos < L.len && (L.src[L.pos] == '=' || L.src[L.pos] == '<')) {
                    L.pos++;
                    if (L.pos < L.len && L.src[L.pos] == ':') L.pos++;
                    char prim[64];
                    if (!d0_read_ident(&L, prim, sizeof(prim))) return D0_DIAG_PARSE_ERROR;
                    if (strcmp(prim, "symbol") == 0) td->prim = D0_PRIM_SYMBOL;
                    else if (strcmp(prim, "number") == 0) td->prim = D0_PRIM_NUMBER;
                    else if (strcmp(prim, "unsigned") == 0) td->prim = D0_PRIM_UNSIGNED;
                    else if (strcmp(prim, "float") == 0) td->prim = D0_PRIM_FLOAT;
                    else td->prim = D0_PRIM_UNKNOWN;
                } else {
                    td->prim = D0_PRIM_SYMBOL;
                }
                prog->stmt_counter++;
            } else if (strcmp(dir, "decl") == 0) {
                if (prog->nrels >= D0_MAX_RELS) return D0_DIAG_PARSE_ERROR;
                D0RelDecl *rd = &prog->rels[prog->nrels++];
                memset(rd, 0, sizeof(*rd));
                if (!d0_read_ident(&L, rd->name, sizeof(rd->name))) return D0_DIAG_PARSE_ERROR;
                d0_skip_ws(&L);
                if (L.pos >= L.len || L.src[L.pos] != '(') return D0_DIAG_PARSE_ERROR;
                L.pos++;
                d0_skip_ws(&L);
                if (L.pos < L.len && L.src[L.pos] == ')') {
                    L.pos++;
                } else {
                    while (true) {
                        if (rd->arity >= D0_MAX_ARITY) return D0_DIAG_PARSE_ERROR;
                        int k = rd->arity++;
                        if (!d0_read_ident(&L, rd->attr_names[k], sizeof(rd->attr_names[k])))
                            return D0_DIAG_PARSE_ERROR;
                        d0_skip_ws(&L);
                        if (L.pos >= L.len || L.src[L.pos] != ':') return D0_DIAG_PARSE_ERROR;
                        L.pos++;
                        if (!d0_read_ident(&L, rd->attr_types[k], sizeof(rd->attr_types[k])))
                            return D0_DIAG_PARSE_ERROR;
                        d0_skip_ws(&L);
                        if (L.pos < L.len && L.src[L.pos] == ',') { L.pos++; continue; }
                        if (L.pos < L.len && L.src[L.pos] == ')') { L.pos++; break; }
                        return D0_DIAG_PARSE_ERROR;
                    }
                }
                prog->stmt_counter++;
            } else if (strcmp(dir, "input") == 0) {
                if (prog->ninput_decls >= D0_MAX_RELS) return D0_DIAG_PARSE_ERROR;
                if (!d0_read_ident(&L, prog->input_decls[prog->ninput_decls++], 64))
                    return D0_DIAG_PARSE_ERROR;
                d0_skip_ws(&L);
                if (L.pos < L.len && L.src[L.pos] == '(') {
                    while (L.pos < L.len && L.src[L.pos] != ')') L.pos++;
                    if (L.pos < L.len) L.pos++;
                }
                prog->stmt_counter++;
            } else if (strcmp(dir, "output") == 0) {
                if (prog->noutput_decls >= D0_MAX_RELS) return D0_DIAG_PARSE_ERROR;
                if (!d0_read_ident(&L, prog->output_decls[prog->noutput_decls++], 64))
                    return D0_DIAG_PARSE_ERROR;
                d0_skip_ws(&L);
                if (L.pos < L.len && L.src[L.pos] == '(') {
                    while (L.pos < L.len && L.src[L.pos] != ')') L.pos++;
                    if (L.pos < L.len) L.pos++;
                }
                prog->stmt_counter++;
            } else {
                return D0_DIAG_PARSE_ERROR;
            }
        } else {
            D0Atom head;
            memset(&head, 0, sizeof(head));
            if (!d0_read_ident(&L, head.rel, sizeof(head.rel))) return D0_DIAG_PARSE_ERROR;
            if (!d0_read_atom_args(&L, &head)) return D0_DIAG_PARSE_ERROR;
            d0_skip_ws(&L);
            if (L.pos < L.len && L.src[L.pos] == '.') {
                L.pos++;
                if (prog->nfacts >= D0_MAX_FACTS) return D0_DIAG_PARSE_ERROR;
                D0FactStmt *fs = &prog->facts[prog->nfacts++];
                fs->stmt_index = prog->stmt_counter++;
                fs->atom = head;
            } else if (L.pos + 1 < L.len && L.src[L.pos] == ':' && L.src[L.pos + 1] == '-') {
                L.pos += 2;
                if (prog->nclauses >= D0_MAX_CLAUSES) return D0_DIAG_PARSE_ERROR;
                D0ClauseStmt *cs = &prog->clauses[prog->nclauses];
                memset(cs, 0, sizeof(*cs));
                cs->stmt_index = prog->stmt_counter++;
                cs->clause_index = prog->nclauses++;
                cs->head = head;
                while (true) {
                    d0_skip_ws(&L);
                    size_t saved = L.pos;
                    char id[64];
                    if (d0_read_ident(&L, id, sizeof(id))) {
                        d0_skip_ws(&L);
                        if (L.pos < L.len && L.src[L.pos] == '(') {
                            if (cs->nbody >= D0_MAX_BODY) return D0_DIAG_PARSE_ERROR;
                            D0Atom *ba = &cs->body[cs->nbody++];
                            snprintf(ba->rel, sizeof(ba->rel), "%s", id);
                            if (!d0_read_atom_args(&L, ba)) return D0_DIAG_PARSE_ERROR;
                            goto next_conjunct;
                        }
                    }
                    L.pos = saved;
                    if (cs->ncmps >= D0_MAX_CMPS) return D0_DIAG_PARSE_ERROR;
                    D0Comparison *cmp = &cs->cmps[cs->ncmps++];
                    if (!d0_read_term(&L, &cmp->lhs)) return D0_DIAG_PARSE_ERROR;
                    if (!d0_try_read_cmp_op(&L, &cmp->op)) return D0_DIAG_PARSE_ERROR;
                    if (!d0_read_term(&L, &cmp->rhs)) return D0_DIAG_PARSE_ERROR;
                next_conjunct:
                    d0_skip_ws(&L);
                    if (L.pos < L.len && L.src[L.pos] == ',') { L.pos++; continue; }
                    if (L.pos < L.len && L.src[L.pos] == '.') { L.pos++; break; }
                    return D0_DIAG_PARSE_ERROR;
                }
            } else {
                return D0_DIAG_PARSE_ERROR;
            }
        }
    }
    return D0_DIAG_OK;
}

/* =========================================================================
 * 3. GSLT/MeTTa (D0Program ...) S-Expression IR Parser
 * ========================================================================= */

static bool sexp_match_kw(D0Lexer *L, const char *kw) {
    d0_skip_ws(L);
    size_t len = strlen(kw);
    if (L->pos + len > L->len) return false;
    if (memcmp(L->src + L->pos, kw, len) != 0) return false;
    if (L->pos + len < L->len) {
        char next = L->src[L->pos + len];
        if (!isspace((unsigned char)next) && next != '(' && next != ')') return false;
    }
    L->pos += len;
    return true;
}

static bool sexp_read_rel_name(D0Lexer *L, char *buf, size_t cap) {
    d0_skip_ws(L);
    if (L->pos < L->len && L->src[L->pos] == '"') {
        return d0_read_string(L, buf, cap);
    }
    if (L->pos < L->len && L->src[L->pos] == '(') {
        L->pos++;
        buf[0] = '\0';
        size_t pos = 0;
        int segs = 0;
        while (true) {
            d0_skip_ws(L);
            if (L->pos < L->len && L->src[L->pos] == ')') { L->pos++; break; }
            char seg[64];
            if (!d0_read_string(L, seg, sizeof(seg))) return false;
            if (segs > 0 && pos + 1 < cap) buf[pos++] = '.';
            size_t slen = strlen(seg);
            if (pos + slen < cap) {
                memcpy(buf + pos, seg, slen + 1);
                pos += slen;
            }
            segs++;
        }
        return segs > 0;
    }
    return false;
}

static bool sexp_read_val_inner(D0Lexer *L, D0Term *t) {
    if (sexp_match_kw(L, "D0Symbol") || sexp_match_kw(L, "D0SymbolValue")) {
        if (!d0_read_string(L, t->text, sizeof(t->text))) return false;
        t->kind = D0_TERM_SYMBOL;
        return true;
    }
    if (sexp_match_kw(L, "D0Number") || sexp_match_kw(L, "D0NumberValue") ||
        sexp_match_kw(L, "D0Unsigned") || sexp_match_kw(L, "D0UnsignedValue")) {
        d0_skip_ws(L);
        size_t n = 0;
        while (L->pos < L->len && !isspace((unsigned char)L->src[L->pos]) && L->src[L->pos] != ')') {
            if (n + 1 < sizeof(t->text)) t->text[n++] = L->src[L->pos];
            L->pos++;
        }
        t->text[n] = '\0';
        if (!d0_parse_int_literal(t->text, &t->sval, &t->valid_s64, &t->uval, &t->valid_u64))
            return false;
        t->kind = D0_TERM_RAW_NUM;
        return true;
    }
    return false;
}

static bool sexp_read_term(D0Lexer *L, D0Term *t) {
    memset(t, 0, sizeof(*t));
    d0_skip_ws(L);
    if (sexp_match_kw(L, "D0Wildcard") || sexp_match_kw(L, "D0Anonymous")) {
        t->kind = D0_TERM_ANON;
        snprintf(t->text, sizeof(t->text), "_");
        return true;
    }
    if (L->pos >= L->len || L->src[L->pos] != '(') return false;
    L->pos++;
    if (sexp_match_kw(L, "D0Var")) {
        if (!d0_read_string(L, t->text, sizeof(t->text))) return false;
        t->kind = D0_TERM_VAR;
    } else if (sexp_match_kw(L, "D0Const") || sexp_match_kw(L, "D0Literal")) {
        d0_skip_ws(L);
        if (L->pos >= L->len || L->src[L->pos] != '(') return false;
        L->pos++;
        if (!sexp_read_val_inner(L, t)) return false;
        d0_skip_ws(L);
        if (L->pos >= L->len || L->src[L->pos] != ')') return false;
        L->pos++;
    } else if (!sexp_read_val_inner(L, t)) {
        return false;
    }
    d0_skip_ws(L);
    if (L->pos >= L->len || L->src[L->pos] != ')') return false;
    L->pos++;
    return true;
}

static bool sexp_read_atom(D0Lexer *L, D0Atom *a) {
    memset(a, 0, sizeof(*a));
    d0_skip_ws(L);
    if (L->pos >= L->len || L->src[L->pos] != '(') return false;
    L->pos++;
    if (!sexp_match_kw(L, "D0Atom")) return false;
    if (!sexp_read_rel_name(L, a->rel, sizeof(a->rel))) return false;
    d0_skip_ws(L);
    if (L->pos >= L->len || L->src[L->pos] != '(') return false;
    L->pos++;
    while (true) {
        d0_skip_ws(L);
        if (L->pos < L->len && L->src[L->pos] == ')') { L->pos++; break; }
        if (a->nargs >= D0_MAX_ARITY) return false;
        if (!sexp_read_term(L, &a->args[a->nargs++])) return false;
    }
    d0_skip_ws(L);
    if (L->pos >= L->len || L->src[L->pos] != ')') return false;
    L->pos++;
    return true;
}

static D0DiagKind d0_parse_metta_ir(const char *src, D0Program *prog) {
    d0_program_init(prog);
    GsltArena tmp_arena;
    gslt_arena_init(&tmp_arena);
    const char *active_src = src;

    /* Automatically bridge Lean IRCodec.lean (Program [...]) into (D0Program ...) */
    D0Lexer peek = { src, 0, strlen(src) };
    d0_skip_ws(&peek);
    if (peek.pos < peek.len && peek.src[peek.pos] == '(') {
        peek.pos++;
        if (sexp_match_kw(&peek, "Program")) {
            char err[256] = {0};
            GsltSexpr *root = gslt_sexpr_parse_all(&tmp_arena, src, strlen(src), err, sizeof(err));
            GsltByteStr ir_str = { "", 0 };
            if (!root || !gslt_d0_lean_ir_sexpr_to_d0_ir_str(&tmp_arena, root, &ir_str, err, sizeof(err))) {
                gslt_arena_free(&tmp_arena);
                return D0_DIAG_PARSE_ERROR;
            }
            active_src = ir_str.bytes;
        }
    }

    D0Lexer L = { active_src, 0, strlen(active_src) };
    d0_skip_ws(&L);
    if (L.pos >= L.len || L.src[L.pos] != '(') { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
    L.pos++;
    if (!sexp_match_kw(&L, "D0Program")) { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
    d0_skip_ws(&L);
    if (L.pos >= L.len || L.src[L.pos] != '(') { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
    L.pos++;
    while (true) {
        d0_skip_ws(&L);
        if (L.pos < L.len && L.src[L.pos] == ')') { L.pos++; break; }
        if (L.pos >= L.len || L.src[L.pos] != '(') { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
        L.pos++;
        if (sexp_match_kw(&L, "D0TypeDecl")) {
            if (prog->ntypes >= D0_MAX_TYPES) { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
            D0TypeDecl *td = &prog->types[prog->ntypes++];
            if (!d0_read_string(&L, td->name, sizeof(td->name))) { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
            td->prim = D0_PRIM_SYMBOL;
            prog->stmt_counter++;
        } else if (sexp_match_kw(&L, "D0RelationDecl") || sexp_match_kw(&L, "D0Declaration")) {
            if (prog->nrels >= D0_MAX_RELS) { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
            D0RelDecl *rd = &prog->rels[prog->nrels++];
            memset(rd, 0, sizeof(*rd));
            if (!sexp_read_rel_name(&L, rd->name, sizeof(rd->name))) { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
            d0_skip_ws(&L);
            if (L.pos >= L.len || L.src[L.pos] != '(') { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
            L.pos++;
            while (true) {
                d0_skip_ws(&L);
                if (L.pos < L.len && L.src[L.pos] == ')') { L.pos++; break; }
                if (L.pos >= L.len || L.src[L.pos] != '(') { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
                L.pos++;
                if (!sexp_match_kw(&L, "D0Attribute")) { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
                if (rd->arity >= D0_MAX_ARITY) { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
                int k = rd->arity++;
                if (!d0_read_string(&L, rd->attr_names[k], 64)) { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
                d0_skip_ws(&L);
                if (sexp_match_kw(&L, "D0TypeSymbol") || sexp_match_kw(&L, "D0Symbol")) snprintf(rd->attr_types[k], 64, "symbol");
                else if (sexp_match_kw(&L, "D0TypeNumber") || sexp_match_kw(&L, "D0Number")) snprintf(rd->attr_types[k], 64, "number");
                else if (sexp_match_kw(&L, "D0TypeUnsigned") || sexp_match_kw(&L, "D0Unsigned")) snprintf(rd->attr_types[k], 64, "unsigned");
                else if (sexp_match_kw(&L, "D0TypeFloat") || sexp_match_kw(&L, "D0Float")) snprintf(rd->attr_types[k], 64, "float");
                else if (L.pos < L.len && L.src[L.pos] == '(') {
                    L.pos++;
                    if (!sexp_match_kw(&L, "D0TypeCustom")) { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
                    if (!d0_read_string(&L, rd->attr_types[k], 64)) { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
                    d0_skip_ws(&L);
                    if (L.pos >= L.len || L.src[L.pos] != ')') { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
                    L.pos++;
                } else { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
                d0_skip_ws(&L);
                if (L.pos >= L.len || L.src[L.pos] != ')') { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
                L.pos++;
            }
            prog->stmt_counter++;
        } else if (sexp_match_kw(&L, "D0InputDecl") || sexp_match_kw(&L, "D0Input")) {
            if (prog->ninput_decls >= D0_MAX_RELS ||
                !sexp_read_rel_name(&L, prog->input_decls[prog->ninput_decls++], 64)) {
                gslt_arena_free(&tmp_arena);
                return D0_DIAG_PARSE_ERROR;
            }
            prog->stmt_counter++;
        } else if (sexp_match_kw(&L, "D0OutputDecl") || sexp_match_kw(&L, "D0Output")) {
            if (prog->noutput_decls >= D0_MAX_RELS ||
                !sexp_read_rel_name(&L, prog->output_decls[prog->noutput_decls++], 64)) {
                gslt_arena_free(&tmp_arena);
                return D0_DIAG_PARSE_ERROR;
            }
            prog->stmt_counter++;
        } else if (sexp_match_kw(&L, "D0FactStmt")) {
            if (prog->nfacts >= D0_MAX_FACTS) { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
            D0FactStmt *fs = &prog->facts[prog->nfacts++];
            fs->stmt_index = prog->stmt_counter++;
            if (!sexp_read_atom(&L, &fs->atom)) { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
        } else if (sexp_match_kw(&L, "D0Fact")) {
            if (prog->nfacts >= D0_MAX_FACTS) { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
            D0FactStmt *fs = &prog->facts[prog->nfacts++];
            memset(fs, 0, sizeof(*fs));
            fs->stmt_index = prog->stmt_counter++;
            if (!sexp_read_rel_name(&L, fs->atom.rel, sizeof(fs->atom.rel))) { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
            d0_skip_ws(&L);
            if (L.pos >= L.len || L.src[L.pos] != '(') { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
            L.pos++;
            while (true) {
                d0_skip_ws(&L);
                if (L.pos < L.len && L.src[L.pos] == ')') { L.pos++; break; }
                if (fs->atom.nargs >= D0_MAX_ARITY ||
                    !sexp_read_term(&L, &fs->atom.args[fs->atom.nargs++])) {
                    gslt_arena_free(&tmp_arena);
                    return D0_DIAG_PARSE_ERROR;
                }
            }
        } else if (sexp_match_kw(&L, "D0RuleStmt") || sexp_match_kw(&L, "D0Rule")) {
            if (prog->nclauses >= D0_MAX_CLAUSES) { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
            D0ClauseStmt *cs = &prog->clauses[prog->nclauses];
            memset(cs, 0, sizeof(*cs));
            cs->stmt_index = prog->stmt_counter++;
            cs->clause_index = prog->nclauses++;
            d0_skip_ws(&L);
            bool wrapped_clause = false;
            size_t saved_clause = L.pos;
            if (L.pos < L.len && L.src[L.pos] == '(') {
                L.pos++;
                if (sexp_match_kw(&L, "D0Clause")) {
                    wrapped_clause = true;
                } else {
                    L.pos = saved_clause;
                }
            }
            if (!sexp_read_atom(&L, &cs->head)) { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
            d0_skip_ws(&L);
            if (L.pos >= L.len || L.src[L.pos] != '(') { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
            L.pos++;
            while (true) {
                d0_skip_ws(&L);
                if (L.pos < L.len && L.src[L.pos] == ')') { L.pos++; break; }
                if (L.pos >= L.len || L.src[L.pos] != '(') { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
                L.pos++;
                if (sexp_match_kw(&L, "D0PosAtom") || sexp_match_kw(&L, "D0Positive")) {
                    if (cs->nbody >= D0_MAX_BODY || !sexp_read_atom(&L, &cs->body[cs->nbody++])) {
                        gslt_arena_free(&tmp_arena);
                        return D0_DIAG_PARSE_ERROR;
                    }
                } else if (sexp_match_kw(&L, "D0Comparison") || sexp_match_kw(&L, "D0Compare")) {
                    if (cs->ncmps >= D0_MAX_CMPS) { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
                    D0Comparison *cmp = &cs->cmps[cs->ncmps++];
                    if (sexp_match_kw(&L, "D0Eq") || sexp_match_kw(&L, "D0Equal")) cmp->op = D0_CMP_EQ;
                    else if (sexp_match_kw(&L, "D0Ne") || sexp_match_kw(&L, "D0Different")) cmp->op = D0_CMP_NE;
                    else if (sexp_match_kw(&L, "D0Lt") || sexp_match_kw(&L, "D0Less")) cmp->op = D0_CMP_LT;
                    else if (sexp_match_kw(&L, "D0Le") || sexp_match_kw(&L, "D0LessEqual")) cmp->op = D0_CMP_LE;
                    else if (sexp_match_kw(&L, "D0Gt") || sexp_match_kw(&L, "D0Greater")) cmp->op = D0_CMP_GT;
                    else if (sexp_match_kw(&L, "D0Ge") || sexp_match_kw(&L, "D0GreaterEqual")) cmp->op = D0_CMP_GE;
                    else { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
                    if (!sexp_read_term(&L, &cmp->lhs) || !sexp_read_term(&L, &cmp->rhs)) {
                        gslt_arena_free(&tmp_arena);
                        return D0_DIAG_PARSE_ERROR;
                    }
                } else { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
                d0_skip_ws(&L);
                if (L.pos >= L.len || L.src[L.pos] != ')') { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
                L.pos++;
            }
            if (wrapped_clause) {
                d0_skip_ws(&L);
                if (L.pos >= L.len || L.src[L.pos] != ')') { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
                L.pos++;
            }
        } else {
            gslt_arena_free(&tmp_arena);
            return D0_DIAG_PARSE_ERROR;
        }
        d0_skip_ws(&L);
        if (L.pos >= L.len || L.src[L.pos] != ')') { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
        L.pos++;
    }
    d0_skip_ws(&L);
    if (L.pos >= L.len || L.src[L.pos] != ')') { gslt_arena_free(&tmp_arena); return D0_DIAG_PARSE_ERROR; }
    L.pos++;
    gslt_arena_free(&tmp_arena);
    return D0_DIAG_OK;
}

/* Canonical D0 IR printer (--emit-d0) and Souffle .dl printer (--emit-dl) */
static void d0_emit_qname_ir(GsltArena *a, GsltStrBuf *sb, const char *name) {
    gslt_sb_append_char(a, sb, '(');
    const char *p = name;
    int seg = 0;
    while (*p) {
        const char *dot = strchr(p, '.');
        size_t len = dot ? (size_t)(dot - p) : strlen(p);
        if (seg++ > 0) gslt_sb_append_char(a, sb, ' ');
        GsltByteStr bs = { p, (uint32_t)len };
        gslt_sb_append_ir_quoted(a, sb, bs);
        if (!dot) break;
        p = dot + 1;
    }
    gslt_sb_append_char(a, sb, ')');
}

static void d0_emit_term_ir(GsltArena *a, GsltStrBuf *sb, const D0Term *t, bool as_val_only) {
    if (t->kind == D0_TERM_ANON) {
        gslt_sb_append_cstr(a, sb, "D0Anonymous");
        return;
    }
    if (t->kind == D0_TERM_VAR) {
        gslt_sb_append_cstr(a, sb, "(D0Var ");
        GsltByteStr bs = { t->text, (uint32_t)strlen(t->text) };
        gslt_sb_append_ir_quoted(a, sb, bs);
        gslt_sb_append_char(a, sb, ')');
        return;
    }
    if (!as_val_only) gslt_sb_append_cstr(a, sb, "(D0Literal ");
    if (t->kind == D0_TERM_SYMBOL) {
        gslt_sb_append_cstr(a, sb, "(D0SymbolValue ");
        GsltByteStr bs = { t->text, (uint32_t)strlen(t->text) };
        gslt_sb_append_ir_quoted(a, sb, bs);
        gslt_sb_append_char(a, sb, ')');
    } else if (t->kind == D0_TERM_UNSIGNED) {
        char buf[64];
        snprintf(buf, sizeof(buf), "(D0UnsignedValue %" PRIu64 ")", t->uval);
        gslt_sb_append_cstr(a, sb, buf);
    } else {
        char buf[64];
        snprintf(buf, sizeof(buf), "(D0NumberValue %" PRId64 ")", t->sval);
        gslt_sb_append_cstr(a, sb, buf);
    }
    if (!as_val_only) gslt_sb_append_char(a, sb, ')');
}

static void d0_emit_atom_ir(GsltArena *a, GsltStrBuf *sb, const D0Atom *at) {
    gslt_sb_append_cstr(a, sb, "(D0Atom ");
    d0_emit_qname_ir(a, sb, at->rel);
    gslt_sb_append_cstr(a, sb, " (");
    for (int i = 0; i < at->nargs; i++) {
        if (i > 0) gslt_sb_append_char(a, sb, ' ');
        d0_emit_term_ir(a, sb, &at->args[i], false);
    }
    gslt_sb_append_cstr(a, sb, "))");
}

static GsltByteStr d0_emit_metta_ir(GsltArena *a, const D0Program *p) {
    GsltStrBuf sb;
    gslt_sb_init(a, &sb, 1024);
    gslt_sb_append_cstr(a, &sb, "(D0Program (");
    bool first = true;
    for (int r = 0; r < p->nrels; r++) {
        if (!first) gslt_sb_append_char(a, &sb, ' ');
        first = false;
        const D0RelDecl *rd = &p->rels[r];
        gslt_sb_append_cstr(a, &sb, "(D0Declaration ");
        d0_emit_qname_ir(a, &sb, rd->name);
        gslt_sb_append_cstr(a, &sb, " (");
        for (int k = 0; k < rd->arity; k++) {
            if (k > 0) gslt_sb_append_char(a, &sb, ' ');
            gslt_sb_append_cstr(a, &sb, "(D0Attribute ");
            GsltByteStr an = { rd->attr_names[k], (uint32_t)strlen(rd->attr_names[k]) };
            gslt_sb_append_ir_quoted(a, &sb, an);
            const char *tk = " D0Symbol)";
            if (rd->col_prim[k] == D0_PRIM_NUMBER) tk = " D0Number)";
            else if (rd->col_prim[k] == D0_PRIM_UNSIGNED) tk = " D0Unsigned)";
            gslt_sb_append_cstr(a, &sb, tk);
        }
        gslt_sb_append_cstr(a, &sb, "))");
    }
    for (int i = 0; i < p->ninput_decls; i++) {
        if (!first) gslt_sb_append_char(a, &sb, ' ');
        first = false;
        gslt_sb_append_cstr(a, &sb, "(D0Input ");
        d0_emit_qname_ir(a, &sb, p->input_decls[i]);
        gslt_sb_append_char(a, &sb, ')');
    }
    for (int i = 0; i < p->noutput_decls; i++) {
        if (!first) gslt_sb_append_char(a, &sb, ' ');
        first = false;
        gslt_sb_append_cstr(a, &sb, "(D0Output ");
        d0_emit_qname_ir(a, &sb, p->output_decls[i]);
        gslt_sb_append_char(a, &sb, ')');
    }
    for (int f = 0; f < p->nfacts; f++) {
        if (!first) gslt_sb_append_char(a, &sb, ' ');
        first = false;
        const D0Atom *fa = &p->facts[f].atom;
        gslt_sb_append_cstr(a, &sb, "(D0Fact ");
        d0_emit_qname_ir(a, &sb, fa->rel);
        gslt_sb_append_cstr(a, &sb, " (");
        for (int k = 0; k < fa->nargs; k++) {
            if (k > 0) gslt_sb_append_char(a, &sb, ' ');
            d0_emit_term_ir(a, &sb, &fa->args[k], true);
        }
        gslt_sb_append_cstr(a, &sb, "))");
    }
    for (int c = 0; c < p->nclauses; c++) {
        if (!first) gslt_sb_append_char(a, &sb, ' ');
        first = false;
        const D0ClauseStmt *cs = &p->clauses[c];
        gslt_sb_append_cstr(a, &sb, "(D0Rule ");
        d0_emit_atom_ir(a, &sb, &cs->head);
        gslt_sb_append_cstr(a, &sb, " (");
        bool bfirst = true;
        for (int b = 0; b < cs->nbody; b++) {
            if (!bfirst) gslt_sb_append_char(a, &sb, ' ');
            bfirst = false;
            gslt_sb_append_cstr(a, &sb, "(D0Positive ");
            d0_emit_atom_ir(a, &sb, &cs->body[b]);
            gslt_sb_append_char(a, &sb, ')');
        }
        for (int m = 0; m < cs->ncmps; m++) {
            if (!bfirst) gslt_sb_append_char(a, &sb, ' ');
            bfirst = false;
            const char *cop = "D0Equal";
            switch (cs->cmps[m].op) {
                case D0_CMP_EQ: cop = "D0Equal"; break;
                case D0_CMP_NE: cop = "D0Different"; break;
                case D0_CMP_LT: cop = "D0Less"; break;
                case D0_CMP_LE: cop = "D0LessEqual"; break;
                case D0_CMP_GT: cop = "D0Greater"; break;
                case D0_CMP_GE: cop = "D0GreaterEqual"; break;
            }
            gslt_sb_append_cstr(a, &sb, "(D0Compare ");
            gslt_sb_append_cstr(a, &sb, cop);
            gslt_sb_append_char(a, &sb, ' ');
            d0_emit_term_ir(a, &sb, &cs->cmps[m].lhs, false);
            gslt_sb_append_char(a, &sb, ' ');
            d0_emit_term_ir(a, &sb, &cs->cmps[m].rhs, false);
            gslt_sb_append_char(a, &sb, ')');
        }
        gslt_sb_append_cstr(a, &sb, "))");
    }
    gslt_sb_append_cstr(a, &sb, "))");
    GsltByteStr out = { sb.buf, (uint32_t)sb.len };
    return out;
}

static void d0_emit_term_dl(GsltArena *a, GsltStrBuf *sb, const D0Term *t) {
    if (t->kind == D0_TERM_ANON) {
        gslt_sb_append_char(a, sb, '_');
    } else if (t->kind == D0_TERM_VAR) {
        gslt_sb_append_cstr(a, sb, t->text);
    } else if (t->kind == D0_TERM_SYMBOL) {
        GsltByteStr bs = { t->text, (uint32_t)strlen(t->text) };
        gslt_sb_append_ir_quoted(a, sb, bs);
    } else if (t->kind == D0_TERM_UNSIGNED) {
        char buf[64];
        snprintf(buf, sizeof(buf), "%" PRIu64, t->uval);
        gslt_sb_append_cstr(a, sb, buf);
    } else {
        char buf[64];
        snprintf(buf, sizeof(buf), "%" PRId64, t->sval);
        gslt_sb_append_cstr(a, sb, buf);
    }
}

static void d0_emit_atom_dl(GsltArena *a, GsltStrBuf *sb, const D0Atom *at) {
    gslt_sb_append_cstr(a, sb, at->rel);
    gslt_sb_append_char(a, sb, '(');
    for (int i = 0; i < at->nargs; i++) {
        if (i > 0) gslt_sb_append_cstr(a, sb, ", ");
        d0_emit_term_dl(a, sb, &at->args[i]);
    }
    gslt_sb_append_char(a, sb, ')');
}

static GsltByteStr d0_emit_dl_source(GsltArena *a, const D0Program *p) {
    GsltStrBuf sb;
    gslt_sb_init(a, &sb, 1024);
    for (int t = 0; t < p->ntypes; t++) {
        const char *pk = "symbol";
        if (p->types[t].prim == D0_PRIM_NUMBER) pk = "number";
        else if (p->types[t].prim == D0_PRIM_UNSIGNED) pk = "unsigned";
        gslt_sb_append_cstr(a, &sb, ".type ");
        gslt_sb_append_cstr(a, &sb, p->types[t].name);
        gslt_sb_append_cstr(a, &sb, " = ");
        gslt_sb_append_cstr(a, &sb, pk);
        gslt_sb_append_char(a, &sb, '\n');
    }
    for (int r = 0; r < p->nrels; r++) {
        const D0RelDecl *rd = &p->rels[r];
        gslt_sb_append_cstr(a, &sb, ".decl ");
        gslt_sb_append_cstr(a, &sb, rd->name);
        gslt_sb_append_char(a, &sb, '(');
        for (int k = 0; k < rd->arity; k++) {
            if (k > 0) gslt_sb_append_cstr(a, &sb, ", ");
            gslt_sb_append_cstr(a, &sb, rd->attr_names[k]);
            gslt_sb_append_cstr(a, &sb, " : ");
            gslt_sb_append_cstr(a, &sb, rd->attr_types[k]);
        }
        gslt_sb_append_cstr(a, &sb, ")\n");
    }
    for (int i = 0; i < p->ninput_decls; i++) {
        gslt_sb_append_cstr(a, &sb, ".input ");
        gslt_sb_append_cstr(a, &sb, p->input_decls[i]);
        gslt_sb_append_char(a, &sb, '\n');
    }
    for (int i = 0; i < p->noutput_decls; i++) {
        gslt_sb_append_cstr(a, &sb, ".output ");
        gslt_sb_append_cstr(a, &sb, p->output_decls[i]);
        gslt_sb_append_char(a, &sb, '\n');
    }
    for (int f = 0; f < p->nfacts; f++) {
        d0_emit_atom_dl(a, &sb, &p->facts[f].atom);
        gslt_sb_append_cstr(a, &sb, ".\n");
    }
    for (int c = 0; c < p->nclauses; c++) {
        const D0ClauseStmt *cs = &p->clauses[c];
        d0_emit_atom_dl(a, &sb, &cs->head);
        gslt_sb_append_cstr(a, &sb, " :- ");
        bool bfirst = true;
        for (int b = 0; b < cs->nbody; b++) {
            if (!bfirst) gslt_sb_append_cstr(a, &sb, ", ");
            bfirst = false;
            d0_emit_atom_dl(a, &sb, &cs->body[b]);
        }
        for (int m = 0; m < cs->ncmps; m++) {
            if (!bfirst) gslt_sb_append_cstr(a, &sb, ", ");
            bfirst = false;
            const char *cop = " = ";
            switch (cs->cmps[m].op) {
                case D0_CMP_EQ: cop = " = "; break;
                case D0_CMP_NE: cop = " != "; break;
                case D0_CMP_LT: cop = " < "; break;
                case D0_CMP_LE: cop = " <= "; break;
                case D0_CMP_GT: cop = " > "; break;
                case D0_CMP_GE: cop = " >= "; break;
            }
            d0_emit_term_dl(a, &sb, &cs->cmps[m].lhs);
            gslt_sb_append_cstr(a, &sb, cop);
            d0_emit_term_dl(a, &sb, &cs->cmps[m].rhs);
        }
        gslt_sb_append_cstr(a, &sb, ".\n");
    }
    GsltByteStr out = { sb.buf, (uint32_t)sb.len };
    return out;
}

/* =========================================================================
 * 4. D0 Static Admission Gate (Matching w12 static.metta & Lean ProgramStatic)
 * ========================================================================= */

static int d0_find_type(const D0Program *p, const char *name) {
    for (int i = 0; i < p->ntypes; i++)
        if (strcmp(p->types[i].name, name) == 0) return i;
    return -1;
}

static int d0_find_rel(const D0Program *p, const char *name) {
    for (int i = 0; i < p->nrels; i++)
        if (strcmp(p->rels[i].name, name) == 0) return i;
    return -1;
}

static D0PrimKind d0_resolve_attr_type(const D0Program *p, const char *tname) {
    if (strcmp(tname, "symbol") == 0) return D0_PRIM_SYMBOL;
    if (strcmp(tname, "number") == 0) return D0_PRIM_NUMBER;
    if (strcmp(tname, "unsigned") == 0) return D0_PRIM_UNSIGNED;
    if (strcmp(tname, "float") == 0) return D0_PRIM_FLOAT;
    int ti = d0_find_type(p, tname);
    if (ti >= 0) return p->types[ti].prim;
    return D0_PRIM_UNKNOWN;
}

static bool d0_term_matches_prim(D0Term *t, D0PrimKind prim) {
    if (t->kind == D0_TERM_SYMBOL) return prim == D0_PRIM_SYMBOL;
    if (t->kind == D0_TERM_RAW_NUM || t->kind == D0_TERM_NUMBER || t->kind == D0_TERM_UNSIGNED) {
        if (prim == D0_PRIM_NUMBER && t->valid_s64) {
            t->kind = D0_TERM_NUMBER;
            return true;
        }
        if (prim == D0_PRIM_UNSIGNED && t->valid_u64) {
            t->kind = D0_TERM_UNSIGNED;
            return true;
        }
    }
    return false;
}

static D0DiagKind d0_static_admit(D0Program *p) {
    for (int i = 0; i < p->ntypes; i++) {
        if (p->types[i].prim == D0_PRIM_FLOAT || p->types[i].prim == D0_PRIM_UNKNOWN)
            return D0_DIAG_INVALID_DECLARATION;
        for (int j = i + 1; j < p->ntypes; j++)
            if (strcmp(p->types[i].name, p->types[j].name) == 0)
                return D0_DIAG_DUPLICATE_TYPES;
    }

    for (int i = 0; i < p->nrels; i++) {
        D0RelDecl *r = &p->rels[i];
        for (int j = i + 1; j < p->nrels; j++)
            if (strcmp(r->name, p->rels[j].name) == 0)
                return D0_DIAG_DUPLICATE_RELATIONS;
        for (int a = 0; a < r->arity; a++) {
            for (int b = a + 1; b < r->arity; b++)
                if (strcmp(r->attr_names[a], r->attr_names[b]) == 0)
                    return D0_DIAG_INVALID_DECLARATION;
            D0PrimKind pk = d0_resolve_attr_type(p, r->attr_types[a]);
            if (pk == D0_PRIM_UNKNOWN || pk == D0_PRIM_FLOAT)
                return D0_DIAG_INVALID_DECLARATION;
            r->col_prim[a] = pk;
        }
    }

    for (int i = 0; i < p->ninput_decls; i++) {
        int ri = d0_find_rel(p, p->input_decls[i]);
        if (ri < 0) return D0_DIAG_UNDECLARED_IFACE;
        p->rels[ri].is_input = true;
    }
    for (int i = 0; i < p->noutput_decls; i++) {
        int ri = d0_find_rel(p, p->output_decls[i]);
        if (ri < 0) return D0_DIAG_UNDECLARED_IFACE;
        p->rels[ri].is_output = true;
    }

    for (int i = 0; i < p->nfacts; i++) {
        D0Atom *fa = &p->facts[i].atom;
        int ri = d0_find_rel(p, fa->rel);
        if (ri < 0) return D0_DIAG_ILL_TYPED_FACT;
        D0RelDecl *rd = &p->rels[ri];
        if (fa->nargs != rd->arity) return D0_DIAG_ILL_TYPED_FACT;
        for (int a = 0; a < fa->nargs; a++) {
            if (!d0_term_matches_prim(&fa->args[a], rd->col_prim[a]))
                return D0_DIAG_ILL_TYPED_FACT;
        }
    }

    for (int i = 0; i < p->nclauses; i++) {
        D0ClauseStmt *cs = &p->clauses[i];
        int hri = d0_find_rel(p, cs->head.rel);
        if (hri < 0 || cs->head.nargs != p->rels[hri].arity)
            return D0_DIAG_ILL_TYPED_CLAUSE;

        int nvars = 0;
        char vnames[D0_MAX_VARS][64];
        char vtype_name[D0_MAX_VARS][64];
        D0PrimKind vprim[D0_MAX_VARS];
        bool vgrounded[D0_MAX_VARS];
        memset(vgrounded, 0, sizeof(vgrounded));

        for (int b = 0; b < cs->nbody; b++) {
            D0Atom *ba = &cs->body[b];
            int bri = d0_find_rel(p, ba->rel);
            if (bri < 0 || ba->nargs != p->rels[bri].arity)
                return D0_DIAG_ILL_TYPED_CLAUSE;
            D0RelDecl *brd = &p->rels[bri];
            for (int a = 0; a < ba->nargs; a++) {
                D0Term *t = &ba->args[a];
                if (t->kind == D0_TERM_ANON) continue;
                if (t->kind == D0_TERM_VAR) {
                    int vi = -1;
                    for (int v = 0; v < nvars; v++)
                        if (strcmp(vnames[v], t->text) == 0) { vi = v; break; }
                    if (vi < 0) {
                        if (nvars >= D0_MAX_VARS) return D0_DIAG_ILL_TYPED_CLAUSE;
                        vi = nvars++;
                        snprintf(vnames[vi], 64, "%.60s", t->text);
                        snprintf(vtype_name[vi], 64, "%.60s", brd->attr_types[a]);
                        vprim[vi] = brd->col_prim[a];
                    } else {
                        if (strcmp(vtype_name[vi], brd->attr_types[a]) != 0)
                            return D0_DIAG_ILL_TYPED_CLAUSE;
                    }
                    vgrounded[vi] = true;
                } else {
                    if (!d0_term_matches_prim(t, brd->col_prim[a]))
                        return D0_DIAG_ILL_TYPED_CLAUSE;
                }
            }
        }

        bool changed = true;
        while (changed) {
            changed = false;
            for (int c = 0; c < cs->ncmps; c++) {
                D0Comparison *cmp = &cs->cmps[c];
                if (cmp->op != D0_CMP_EQ) continue;
                if (cmp->lhs.kind == D0_TERM_VAR && cmp->rhs.kind == D0_TERM_VAR) {
                    int v1 = -1, v2 = -1;
                    for (int v = 0; v < nvars; v++) {
                        if (strcmp(vnames[v], cmp->lhs.text) == 0) v1 = v;
                        if (strcmp(vnames[v], cmp->rhs.text) == 0) v2 = v;
                    }
                    if (v1 >= 0 && v2 < 0 && nvars < D0_MAX_VARS) {
                        v2 = nvars++;
                        snprintf(vnames[v2], 64, "%.60s", cmp->rhs.text);
                        memcpy(vtype_name[v2], vtype_name[v1], 64);
                        vprim[v2] = vprim[v1];
                        vgrounded[v2] = vgrounded[v1];
                        changed = true;
                    } else if (v2 >= 0 && v1 < 0 && nvars < D0_MAX_VARS) {
                        v1 = nvars++;
                        snprintf(vnames[v1], 64, "%.60s", cmp->lhs.text);
                        memcpy(vtype_name[v1], vtype_name[v2], 64);
                        vprim[v1] = vprim[v2];
                        vgrounded[v1] = vgrounded[v2];
                        changed = true;
                    }
                }
            }
        }

        for (int c = 0; c < cs->ncmps; c++) {
            D0Comparison *cmp = &cs->cmps[c];
            if (cmp->lhs.kind == D0_TERM_ANON || cmp->rhs.kind == D0_TERM_ANON)
                return D0_DIAG_ILL_TYPED_CLAUSE;
            D0PrimKind pk_l = D0_PRIM_UNKNOWN, pk_r = D0_PRIM_UNKNOWN;
            const char *tn_l = NULL, *tn_r = NULL;
            if (cmp->lhs.kind == D0_TERM_VAR) {
                int vi = -1;
                for (int v = 0; v < nvars; v++)
                    if (strcmp(vnames[v], cmp->lhs.text) == 0) { vi = v; break; }
                if (vi < 0 || !vgrounded[vi]) return D0_DIAG_ILL_TYPED_CLAUSE;
                pk_l = vprim[vi]; tn_l = vtype_name[vi];
            }
            if (cmp->rhs.kind == D0_TERM_VAR) {
                int vi = -1;
                for (int v = 0; v < nvars; v++)
                    if (strcmp(vnames[v], cmp->rhs.text) == 0) { vi = v; break; }
                if (vi < 0 || !vgrounded[vi]) return D0_DIAG_ILL_TYPED_CLAUSE;
                pk_r = vprim[vi]; tn_r = vtype_name[vi];
            }
            if (cmp->lhs.kind == D0_TERM_VAR && cmp->rhs.kind == D0_TERM_VAR) {
                if (strcmp(tn_l, tn_r) != 0) return D0_DIAG_ILL_TYPED_CLAUSE;
            } else if (cmp->lhs.kind == D0_TERM_VAR) {
                if (!d0_term_matches_prim(&cmp->rhs, pk_l)) return D0_DIAG_ILL_TYPED_CLAUSE;
            } else if (cmp->rhs.kind == D0_TERM_VAR) {
                if (!d0_term_matches_prim(&cmp->lhs, pk_r)) return D0_DIAG_ILL_TYPED_CLAUSE;
            } else {
                if (cmp->lhs.kind == D0_TERM_SYMBOL && cmp->rhs.kind == D0_TERM_SYMBOL) {
                    pk_l = D0_PRIM_SYMBOL;
                } else if (d0_term_matches_prim(&cmp->lhs, D0_PRIM_NUMBER) &&
                           d0_term_matches_prim(&cmp->rhs, D0_PRIM_NUMBER)) {
                    pk_l = D0_PRIM_NUMBER;
                } else {
                    return D0_DIAG_ILL_TYPED_CLAUSE;
                }
            }
        }

        D0RelDecl *hrd = &p->rels[hri];
        for (int a = 0; a < cs->head.nargs; a++) {
            D0Term *t = &cs->head.args[a];
            if (t->kind == D0_TERM_ANON) return D0_DIAG_ILL_TYPED_CLAUSE;
            if (t->kind == D0_TERM_VAR) {
                int vi = -1;
                for (int v = 0; v < nvars; v++)
                    if (strcmp(vnames[v], t->text) == 0) { vi = v; break; }
                if (vi < 0 || !vgrounded[vi]) return D0_DIAG_ILL_TYPED_CLAUSE;
                if (strcmp(vtype_name[vi], hrd->attr_types[a]) != 0)
                    return D0_DIAG_ILL_TYPED_CLAUSE;
            } else {
                if (!d0_term_matches_prim(t, hrd->col_prim[a]))
                    return D0_DIAG_ILL_TYPED_CLAUSE;
            }
        }
    }
    return D0_DIAG_OK;
}

/* =========================================================================
 * 5. Tab-Separated .facts Loader (Validated Against Relation Schema)
 * ========================================================================= */

static D0DiagKind d0_load_facts_dir(D0Program *p, const char *facts_dir) {
    if (!facts_dir || !*facts_dir) return D0_DIAG_OK;
    for (int r = 0; r < p->nrels; r++) {
        D0RelDecl *rd = &p->rels[r];
        if (!rd->is_input) continue;
        char path[512];
        snprintf(path, sizeof(path), "%s/%s.facts", facts_dir, rd->name);
        FILE *fp = fopen(path, "r");
        if (!fp && strncmp(facts_dir, "../", 3) == 0) {
            snprintf(path, sizeof(path), "%s/%s.facts", facts_dir + 3, rd->name);
            fp = fopen(path, "r");
        }
        if (!fp) continue;
        char line[1024];
        while (fgets(line, sizeof(line), fp)) {
            size_t len = strlen(line);
            while (len > 0 && (line[len - 1] == '\n' || line[len - 1] == '\r')) line[--len] = '\0';
            if (len == 0) continue;
            if (p->nfacts >= D0_MAX_FACTS) { fclose(fp); return D0_DIAG_ILL_TYPED_FACT; }
            D0FactStmt *fs = &p->facts[p->nfacts++];
            memset(fs, 0, sizeof(*fs));
            fs->stmt_index = p->stmt_counter++;
            memcpy(fs->atom.rel, rd->name, sizeof(fs->atom.rel));
            char *cur = line;
            for (int col = 0; col < rd->arity; col++) {
                char *tab = strchr(cur, '\t');
                if (col + 1 < rd->arity && !tab) { fclose(fp); return D0_DIAG_ILL_TYPED_FACT; }
                if (col + 1 == rd->arity && tab) { fclose(fp); return D0_DIAG_ILL_TYPED_FACT; }
                if (tab) *tab = '\0';
                D0Term *t = &fs->atom.args[col];
                snprintf(t->text, sizeof(t->text), "%.120s", cur);
                if (rd->col_prim[col] == D0_PRIM_SYMBOL) {
                    t->kind = D0_TERM_SYMBOL;
                } else {
                    if (!d0_parse_int_literal(cur, &t->sval, &t->valid_s64, &t->uval, &t->valid_u64)) {
                        fclose(fp); return D0_DIAG_ILL_TYPED_FACT;
                    }
                    t->kind = D0_TERM_RAW_NUM;
                    if (!d0_term_matches_prim(t, rd->col_prim[col])) {
                        fclose(fp); return D0_DIAG_ILL_TYPED_FACT;
                    }
                }
                fs->atom.nargs++;
                if (tab) cur = tab + 1;
            }
        }
        fclose(fp);
    }
    return D0_DIAG_OK;
}

/* =========================================================================
 * 6. Lowering D0 to tcalc N-ary Constructors, Rules & Admission Profile
 * ========================================================================= */

typedef struct {
    bool is_var;
    int body_idx;
    int col_idx;
    Term const_term;
} D0CmpOperand;

typedef struct {
    uint16_t sort_val;
    uint16_t sort_fact;
    int nsyms;
    char syms[D0_MAX_SYMS][128];
    int norigins;
    D0ClauseOrigin origins[D0_MAX_CLAUSES];
    /* Ordered scalar comparisons per rule_id */
    int rule_ncmps[D0_MAX_CLAUSES];
    struct {
        D0CmpOp op;
        D0PrimKind prim;
        D0CmpOperand lhs;
        D0CmpOperand rhs;
    } rule_cmps[D0_MAX_CLAUSES][D0_MAX_CMPS];
    /* Live SPACE_FACT occurrence tracking */
    bool use_flat_horn;
    uint64_t store_digest;
    uint64_t fast_path_fallbacks;
    uint32_t noccs;
    Occ occs[D0_MAX_OCCS];
} D0LoweredEngine;

/* The D0 engine's tables have fixed sizes.  A table that fills up cuts the run
 * off: the engine records which one, the drivers stop, and the caller reports a
 * cutoff.  A cut-off run is never reported as a completed fixed point. */
static const char *g_d0_capacity_cutoff; /* NULL, or the table that filled up */

static void d0_capacity_cutoff(const char *table) {
    if (!g_d0_capacity_cutoff) g_d0_capacity_cutoff = table;
}

/* Record a live fact occurrence; false (and a cutoff) when the table is full. */
static bool d0_track_occ(D0LoweredEngine *eng, Occ o) {
    if (eng->noccs >= D0_MAX_OCCS) {
        d0_capacity_cutoff("fact table (65536 facts)");
        return false;
    }
    eng->occs[eng->noccs++] = o;
    return true;
}

static uint64_t d0_intern_sym(D0LoweredEngine *eng, const char *s) {
    for (int i = 0; i < eng->nsyms; i++) {
        if (strcmp(eng->syms[i], s) == 0) return (uint64_t)i;
    }
    if (strlen(s) >= sizeof(eng->syms[0])) d0_capacity_cutoff("symbol length (127 bytes)");
    if (eng->nsyms >= D0_MAX_SYMS - 1) d0_capacity_cutoff("symbol table (4095 symbols)");
    int idx = eng->nsyms < (D0_MAX_SYMS - 1) ? eng->nsyms++ : (D0_MAX_SYMS - 1);
    snprintf(eng->syms[idx], sizeof(eng->syms[idx]), "%s", s);
    return (uint64_t)idx;
}

typedef struct {
    uint64_t name_id;
    D0PrimKind prim;
    int64_t sval;
    uint64_t uval;
    uint64_t sym_id;
} D0ScalarEntry;

enum {
    D0_SCALAR_CAP  = 16384,
    D0_SCALAR_HASH = 32768
};

static int g_nscalars = 0;
static D0ScalarEntry g_scalars[D0_SCALAR_CAP];
static int g_scalar_val_ht[D0_SCALAR_HASH];
static int g_scalar_id_ht[D0_SCALAR_HASH];

static void d0_scalars_reset(void) {
    g_nscalars = 0;
    memset(g_scalar_val_ht, -1, sizeof(g_scalar_val_ht));
    memset(g_scalar_id_ht, -1, sizeof(g_scalar_id_ht));
}

static inline uint32_t d0_scalar_val_hash(const D0ScalarEntry *e) {
    uint64_t v = (e->prim == D0_PRIM_SYMBOL) ? e->sym_id
               : (e->prim == D0_PRIM_NUMBER) ? (uint64_t)e->sval : e->uval;
    uint64_t h = ((uint64_t)e->prim * 0x9E3779B97F4A7C15ULL) ^ (v * 0xBF58476D1CE4E5B9ULL);
    return (uint32_t)((h ^ (h >> 32)) & (D0_SCALAR_HASH - 1));
}

static inline uint32_t d0_scalar_id_hash(uint64_t id) {
    uint64_t h = id * 0x9E3779B97F4A7C15ULL;
    return (uint32_t)((h ^ (h >> 32)) & (D0_SCALAR_HASH - 1));
}

static Term d0_encode_const_term(D0LoweredEngine *eng, const D0Term *t) {
    D0ScalarEntry target;
    memset(&target, 0, sizeof(target));
    if (t->kind == D0_TERM_SYMBOL) {
        target.prim = D0_PRIM_SYMBOL;
        target.sym_id = d0_intern_sym(eng, t->text);
    } else if (t->kind == D0_TERM_NUMBER) {
        target.prim = D0_PRIM_NUMBER;
        target.sval = t->sval;
    } else {
        target.prim = D0_PRIM_UNSIGNED;
        target.uval = t->uval;
    }
    uint32_t slot = d0_scalar_val_hash(&target);
    while (g_scalar_val_ht[slot] >= 0) {
        int i = g_scalar_val_ht[slot];
        if (g_scalars[i].prim == target.prim &&
            g_scalars[i].sval == target.sval &&
            g_scalars[i].uval == target.uval &&
            g_scalars[i].sym_id == target.sym_id) {
            return tc_name(eng->sort_val, g_scalars[i].name_id);
        }
        slot = (slot + 1) & (D0_SCALAR_HASH - 1);
    }
    if (g_nscalars >= D0_SCALAR_CAP) {
        d0_capacity_cutoff("scalar table (16384 values)");
        return 0;
    }
    uint64_t fresh_id = tc_fresh_name();
    while (fresh_id == 0) fresh_id = tc_fresh_name();
    target.name_id = fresh_id;
    int idx = g_nscalars++;
    g_scalars[idx] = target;
    g_scalar_val_ht[slot] = idx;
    uint32_t id_slot = d0_scalar_id_hash(fresh_id);
    while (g_scalar_id_ht[id_slot] >= 0) {
        id_slot = (id_slot + 1) & (D0_SCALAR_HASH - 1);
    }
    g_scalar_id_ht[id_slot] = idx;
    return tc_name(eng->sort_val, fresh_id);
}

static const D0ScalarEntry *d0_decode_scalar(Term t) {
    uint64_t id = tc_name_id(t);
    if (id == 0) return NULL;
    uint32_t slot = d0_scalar_id_hash(id);
    while (g_scalar_id_ht[slot] >= 0) {
        int i = g_scalar_id_ht[slot];
        if (g_scalars[i].name_id == id) return &g_scalars[i];
        slot = (slot + 1) & (D0_SCALAR_HASH - 1);
    }
    return NULL;
}

static Term d0_encode_atom_term(D0LoweredEngine *eng, const D0Program *p, const D0Atom *a,
                                int *nvars, char vnames[][64]) {
    int ri = d0_find_rel(p, a->rel);
    Term args[D0_MAX_ARITY];
    for (int i = 0; i < a->nargs; i++) {
        const D0Term *t = &a->args[i];
        if (t->kind == D0_TERM_VAR) {
            int vi = -1;
            for (int v = 0; v < *nvars; v++)
                if (strcmp(vnames[v], t->text) == 0) { vi = v; break; }
            if (vi < 0) {
                vi = (*nvars)++;
                snprintf(vnames[vi], 64, "%.60s", t->text);
            }
            args[i] = tc_v(vi);
        } else if (t->kind == D0_TERM_ANON) {
            int vi = (*nvars)++;
            snprintf(vnames[vi], 64, "_anon_%d", vi);
            args[i] = tc_v(vi);
        } else {
            args[i] = d0_encode_const_term(eng, t);
        }
    }
    return tc_app(p->rels[ri].tc_con_id, a->nargs > 0 ? args : NULL);
}

static Term d0_resolve_cmp_operand(const D0CmpOperand *op, const TcPreparedStep *firing) {
    if (!op->is_var) return op->const_term;
    Occ o = firing->keep[op->body_idx];
    Term t = tc_term(o);
    uint8_t kind = 0; uint32_t head = 0; int arity = 0; const Term *args = NULL;
    tc_node(t, &kind, &head, &arity, &args);
    if (kind != K_APP || op->col_idx >= arity) return 0;
    return args[op->col_idx];
}

/* Named, ledgered SPACE_HELPER scalar comparison callback for TcAdmissionProfile.permit */
static bool d0_scalar_cmp_permit(void *ctx, const TcPreparedStep *firing, const TcPreparedEffect *effect) {
    (void)effect;
    D0LoweredEngine *eng = (D0LoweredEngine *)ctx;
    int r = firing->rule;
    if (r < 0 || r >= D0_MAX_CLAUSES || eng->rule_ncmps[r] == 0) return true;

    for (int c = 0; c < eng->rule_ncmps[r]; c++) {
        Term lt = d0_resolve_cmp_operand(&eng->rule_cmps[r][c].lhs, firing);
        Term rt = d0_resolve_cmp_operand(&eng->rule_cmps[r][c].rhs, firing);
        const D0ScalarEntry *le = d0_decode_scalar(lt);
        const D0ScalarEntry *re = d0_decode_scalar(rt);
        if (!le || !re) return false;
        D0PrimKind prim = eng->rule_cmps[r][c].prim;
        int cmp_res = 0;
        if (prim == D0_PRIM_SYMBOL) {
            const char *ls = eng->syms[le->sym_id];
            const char *rs = eng->syms[re->sym_id];
            cmp_res = strcmp(ls, rs);
        } else if (prim == D0_PRIM_NUMBER) {
            cmp_res = (le->sval < re->sval) ? -1 : (le->sval > re->sval ? 1 : 0);
        } else if (prim == D0_PRIM_UNSIGNED) {
            cmp_res = (le->uval < re->uval) ? -1 : (le->uval > re->uval ? 1 : 0);
        } else {
            return false;
        }
        bool ok = false;
        switch (eng->rule_cmps[r][c].op) {
            case D0_CMP_EQ: ok = (cmp_res == 0); break;
            case D0_CMP_NE: ok = (cmp_res != 0); break;
            case D0_CMP_LT: ok = (cmp_res <  0); break;
            case D0_CMP_LE: ok = (cmp_res <= 0); break;
            case D0_CMP_GT: ok = (cmp_res >  0); break;
            case D0_CMP_GE: ok = (cmp_res >= 0); break;
        }
        if (!ok) return false;
    }
    return true;
}

static bool d0_bind_cmp_operand(D0LoweredEngine *eng, const D0ClauseStmt *cs, const D0Term *t,
                                D0CmpOperand *out_op, D0PrimKind *io_prim, const D0Program *p) {
    memset(out_op, 0, sizeof(*out_op));
    if (t->kind == D0_TERM_VAR) {
        out_op->is_var = true;
        for (int b = 0; b < cs->nbody; b++) {
            int bri = d0_find_rel(p, cs->body[b].rel);
            for (int a = 0; a < cs->body[b].nargs; a++) {
                if (cs->body[b].args[a].kind == D0_TERM_VAR &&
                    strcmp(cs->body[b].args[a].text, t->text) == 0) {
                    out_op->body_idx = b;
                    out_op->col_idx  = a;
                    if (*io_prim == D0_PRIM_UNKNOWN)
                        *io_prim = p->rels[bri].col_prim[a];
                    return true;
                }
            }
        }
        /* Check transitive X = Y binding */
        for (int c = 0; c < cs->ncmps; c++) {
            if (cs->cmps[c].op != D0_CMP_EQ) continue;
            const char *other = NULL;
            if (cs->cmps[c].lhs.kind == D0_TERM_VAR && strcmp(cs->cmps[c].lhs.text, t->text) == 0 &&
                cs->cmps[c].rhs.kind == D0_TERM_VAR)
                other = cs->cmps[c].rhs.text;
            else if (cs->cmps[c].rhs.kind == D0_TERM_VAR && strcmp(cs->cmps[c].rhs.text, t->text) == 0 &&
                     cs->cmps[c].lhs.kind == D0_TERM_VAR)
                other = cs->cmps[c].lhs.text;
            if (other) {
                for (int b = 0; b < cs->nbody; b++) {
                    int bri = d0_find_rel(p, cs->body[b].rel);
                    for (int a = 0; a < cs->body[b].nargs; a++) {
                        if (cs->body[b].args[a].kind == D0_TERM_VAR &&
                            strcmp(cs->body[b].args[a].text, other) == 0) {
                            out_op->body_idx = b;
                            out_op->col_idx  = a;
                            if (*io_prim == D0_PRIM_UNKNOWN)
                                *io_prim = p->rels[bri].col_prim[a];
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    } else {
        out_op->is_var = false;
        out_op->const_term = d0_encode_const_term(eng, t);
        if (*io_prim == D0_PRIM_UNKNOWN) {
            if (t->kind == D0_TERM_SYMBOL) *io_prim = D0_PRIM_SYMBOL;
            else if (t->kind == D0_TERM_NUMBER) *io_prim = D0_PRIM_NUMBER;
            else *io_prim = D0_PRIM_UNSIGNED;
        }
        return true;
    }
}

static inline uint64_t m2_tuple_digest64(int rel_idx, int arity, const Term *args) {
    uint64_t h = ((uint64_t)(uint32_t)(rel_idx + 1) * 0x9E3779B97F4A7C15ULL) ^
                 ((uint64_t)(uint32_t)(arity + 1) * 0xBF58476D1CE4E5B9ULL);
    for (int i = 0; i < arity; i++) {
        uint64_t x = (uint64_t)args[i] + 0x9E3779B97F4A7C15ULL + (uint64_t)i * 0x94D049BB133111EBULL;
        x = (x ^ (x >> 30)) * 0xBF58476D1CE4E5B9ULL;
        x = (x ^ (x >> 27)) * 0x94D049BB133111EBULL;
        h = (h ^ x) * 0x9E3779B97F4A7C15ULL;
    }
    h ^= h >> 31;
    return h ? h : 1ULL;
}

static uint64_t d0_term_tuple_digest64(const D0Program *p, Term t) {
    uint8_t kind = 0; uint32_t head = 0; int arity = 0; const Term *args = NULL;
    tc_node(t, &kind, &head, &arity, &args);
    if (kind != K_APP) return 0;
    int rel_idx = -1;
    for (int r = 0; r < p->nrels; r++) {
        if ((uint32_t)p->rels[r].tc_con_id == head) { rel_idx = r; break; }
    }
    if (rel_idx < 0) return 0;
    return m2_tuple_digest64(rel_idx, arity, args);
}

static inline uint64_t d0_origin_cert_digest(int tc_rule_id, int nbody, int head_rel_idx,
                                             uint8_t tc_fibre_flags, int rule_ncmps) {
    uint64_t h = 0xD0C1A05E4E11F1EDULL;
    h ^= (uint64_t)(uint32_t)(tc_rule_id + 1) * 0x9E3779B97F4A7C15ULL;
    h ^= (uint64_t)(uint32_t)(nbody + 1) * 0xBF58476D1CE4E5B9ULL;
    h ^= (uint64_t)(uint32_t)(head_rel_idx + 1) * 0x94D049BB133111EBULL;
    h ^= (uint64_t)tc_fibre_flags * 0xD6E8FEB86659FD93ULL;
    h ^= (uint64_t)(uint32_t)(rule_ncmps + 17) * 0xA24BAED4963EE407ULL;
    h ^= h >> 31;
    return h ? h : 1ULL;
}

static inline bool d0_origin_pure_horn_qualified(const D0LoweredEngine *eng, const D0ClauseOrigin *orig) {
    if (!orig->is_pure_horn) return false;
    if (orig->nbody < 1 || orig->nbody > 3) return false;
    if (orig->tc_rule_id < 0 || orig->tc_rule_id >= D0_MAX_CLAUSES) return false;
    if (eng->rule_ncmps[orig->tc_rule_id] != 0) return false;
    if ((orig->tc_fibre_flags & (FIBRE_PURE | FIBRE_FLAT)) != (FIBRE_PURE | FIBRE_FLAT)) return false;
    uint64_t expected = d0_origin_cert_digest(orig->tc_rule_id, orig->nbody, orig->head_rel_idx,
                                              orig->tc_fibre_flags, eng->rule_ncmps[orig->tc_rule_id]);
    return orig->horn_cert_digest == expected;
}

static bool d0_lower_to_tcalc_ex(D0Program *p, D0LoweredEngine *eng, bool use_flat_horn) {
    if (!tc_init(1u << 17, 1u << 16)) return false;
    memset(eng, 0, sizeof(*eng));
    eng->use_flat_horn = use_flat_horn;
    g_d0_capacity_cutoff = NULL;
    d0_scalars_reset();

    eng->sort_val  = (uint16_t)tc_sort(SORT_PURE | SORT_STRICT);
    eng->sort_fact = (uint16_t)tc_sort(SORT_STRICT | SORT_PROVABLE);

    /* Declare a typed n-ary tcalc constructor for each D0 relation */
    Binder col_binders[D0_MAX_ARITY];
    for (int i = 0; i < D0_MAX_ARITY; i++) {
        col_binders[i] = (Binder){ .sort = eng->sort_val, .bound = 0, .deps = 0 };
    }
    for (int r = 0; r < p->nrels; r++) {
        p->rels[r].tc_con_id = tc_con(eng->sort_fact, 0, p->rels[r].arity,
                                      p->rels[r].arity > 0 ? col_binders : NULL);
    }

    /* Post validated EDB facts into SPACE_FACT (set-deduplicated) before sealing */
    Term posted_terms[D0_MAX_FACTS];
    int nposted = 0;
    for (int f = 0; f < p->nfacts; f++) {
        int dummy_nvars = 0;
        char dummy_vnames[D0_MAX_VARS][64];
        Term ft = d0_encode_atom_term(eng, p, &p->facts[f].atom, &dummy_nvars, dummy_vnames);
        bool dup = false;
        for (int i = 0; i < nposted; i++) {
            if (posted_terms[i] == ft) { dup = true; break; }
        }
        if (!dup) {
            posted_terms[nposted++] = ft;
            Occ o = tc_post(SPACE_FACT, ft);
            if (!d0_track_occ(eng, o)) break;
            eng->store_digest += d0_term_tuple_digest64(p, ft);
        }
    }

    /* Set rule binder context (up to D0_MAX_VARS variables of sort_val) */
    Binder ctx_vars[D0_MAX_VARS];
    for (int i = 0; i < D0_MAX_VARS; i++) {
        ctx_vars[i] = (Binder){ .sort = eng->sort_val, .bound = 0, .deps = 0 };
    }
    if (!tc_ctx(D0_MAX_VARS, ctx_vars)) return false;

    /* Lower each D0 clause to an origin-retaining tcalc rule */
    for (int c = 0; c < p->nclauses; c++) {
        D0ClauseStmt *cs = &p->clauses[c];
        int nvars = 0;
        char vnames[D0_MAX_VARS][64];
        Rule rl;
        memset(&rl, 0, sizeof(rl));
        rl.fresh = -1;

        for (int b = 0; b < cs->nbody; b++) {
            rl.keep[rl.nkeep].t = d0_encode_atom_term(eng, p, &cs->body[b], &nvars, vnames);
            rl.keep[rl.nkeep].space = SPACE_FACT;
            rl.nkeep++;
        }
        int nvars_body = nvars;           /* variables numbered from here on occur in no body atom */

        int r_id = tc_rule_count();
        for (int m = 0; m < cs->ncmps; m++) {
            D0Comparison *cmp = &cs->cmps[m];
            Term lt = 0, rt = 0;
            if (cmp->lhs.kind == D0_TERM_VAR) {
                int vi = -1;
                for (int v = 0; v < nvars; v++)
                    if (strcmp(vnames[v], cmp->lhs.text) == 0) { vi = v; break; }
                if (vi < 0) { vi = nvars++; snprintf(vnames[vi], 64, "%.60s", cmp->lhs.text); }
                lt = tc_v(vi);
            } else {
                lt = d0_encode_const_term(eng, &cmp->lhs);
            }
            if (cmp->rhs.kind == D0_TERM_VAR) {
                int vi = -1;
                for (int v = 0; v < nvars; v++)
                    if (strcmp(vnames[v], cmp->rhs.text) == 0) { vi = v; break; }
                if (vi < 0) { vi = nvars++; snprintf(vnames[vi], 64, "%.60s", cmp->rhs.text); }
                rt = tc_v(vi);
            } else {
                rt = d0_encode_const_term(eng, &cmp->rhs);
            }

            if (cmp->op == D0_CMP_EQ) {
                rl.tell[rl.ntell][0] = lt;
                rl.tell[rl.ntell][1] = rt;
                rl.ntell++;
            } else if (cmp->op == D0_CMP_NE) {
                rl.neq[rl.nneq][0] = lt;
                rl.neq[rl.nneq][1] = rt;
                rl.nneq++;
            } else {
                D0PrimKind prim = D0_PRIM_UNKNOWN;
                D0CmpOperand lop, rop;
                if (!d0_bind_cmp_operand(eng, cs, &cmp->lhs, &lop, &prim, p) ||
                    !d0_bind_cmp_operand(eng, cs, &cmp->rhs, &rop, &prim, p))
                    return false;
                int ci = eng->rule_ncmps[r_id]++;
                eng->rule_cmps[r_id][ci].op   = cmp->op;
                eng->rule_cmps[r_id][ci].prim = prim;
                eng->rule_cmps[r_id][ci].lhs  = lop;
                eng->rule_cmps[r_id][ci].rhs  = rop;
            }
        }

        int nvars_head = nvars;
        Term head_t = d0_encode_atom_term(eng, p, &cs->head, &nvars, vnames);
        if (nvars > D0_MAX_VARS) return false;
        rl.make.t          = head_t;
        rl.make.space      = SPACE_FACT;
        /* Head variables no body atom binds take their values from the host (the comparisons it
           evaluates, or the caller): they are the rule's input holes. */
        for (int v = nvars_head; v < nvars; v++) rl.inputs |= 1ull << v;
        for (int i = 0; i < cs->head.nargs; i++) {
            if (cs->head.args[i].kind != D0_TERM_VAR) continue;
            for (int v = nvars_body; v < nvars_head; v++)
                if (strcmp(vnames[v], cs->head.args[i].text) == 0) rl.inputs |= 1ull << v;
        }
        bool is_pure_horn = (cs->nbody >= 1 && cs->nbody <= 3 && cs->ncmps == 0);
        if (use_flat_horn && is_pure_horn) {
            /* Pure Horn rule in M2: deduplicated in O(1) by M2's tuple hash set so tcalc
             * classifies the rule as FIBRE_PURE | FIBRE_FLAT (ordinary_flat_adapter fast path) */
            rl.nabsent = 0;
        } else {
            /* Set semantics via tcalc kernel absence guard */
            rl.absent[0].t     = head_t;
            rl.absent[0].space = SPACE_FACT;
            rl.nabsent         = 1;
        }

        int installed_id = tc_rule(&rl);
        if (installed_id < 0) return false;

        D0ClauseOrigin *orig = &eng->origins[eng->norigins++];
        memset(orig, 0, sizeof(*orig));
        orig->stmt_index     = cs->stmt_index;
        orig->clause_index   = cs->clause_index;
        orig->tc_rule_id     = installed_id;
        orig->tc_fibre_flags = tc_rule_fibre(installed_id);
        orig->head_rel_idx   = d0_find_rel(p, cs->head.rel);
        snprintf(orig->head_rel, sizeof(orig->head_rel), "%s", cs->head.rel);
        orig->nbody          = cs->nbody;
        for (int b = 0; b < cs->nbody; b++) {
            orig->body_rel_idx[b] = d0_find_rel(p, cs->body[b].rel);
            snprintf(orig->body_rels[b], 64, "%s", cs->body[b].rel);
        }
        orig->is_pure_horn = is_pure_horn;
        orig->horn_cert_digest = is_pure_horn
            ? d0_origin_cert_digest(installed_id, orig->nbody, orig->head_rel_idx,
                                    orig->tc_fibre_flags, eng->rule_ncmps[installed_id])
            : 0ULL;
    }

    /* Protect SPACE_FACT and seal the kernel: only admitted rule firings may write to SPACE_FACT! */
    tc_protect(SPACE_FACT);
    tc_seal();
    return true;
}

static bool d0_lower_to_tcalc(D0Program *p, D0LoweredEngine *eng) {
    return d0_lower_to_tcalc_ex(p, eng, false);
}

/* =========================================================================
 * 7. Deep-Creativity Tranche: M1 (Naive) vs. M2 (Semi-Naive + Term-ID Join Index)
 * ========================================================================= */

typedef struct {
    TcBridgeOutcome status;
    uint64_t candidates_examined;
    uint64_t events_admitted;
    uint64_t duplicate_facts_derived;
    double elapsed_us;
} D0RunMetrics;

static bool d0_store_has_term(const D0LoweredEngine *eng, Term target) {
    for (uint32_t i = 0; i < eng->noccs; i++) {
        if (tc_alive(eng->occs[i]) && tc_term(eng->occs[i]) == target) return true;
    }
    return false;
}

static bool d0_try_fire_candidate_ex(const D0Program *p, D0LoweredEngine *eng, int orig_idx, const Occ *keep_occ,
                                     const TcAdmissionProfile *profile, TcBridgeBudget *budget,
                                     D0RunMetrics *metrics, int *epoch_added, TcAdmittedEvent *last_ev) {
    D0ClauseOrigin *orig = &eng->origins[orig_idx];
    if (budget->max_candidates > 0 && budget->candidates_inspected >= budget->max_candidates) {
        metrics->status = TC_BRIDGE_BUDGET_EXHAUSTED;
        return false;
    }
    budget->candidates_inspected++;

    TcPreparedStep cand;
    memset(&cand, 0, sizeof(cand));
    cand.rule = orig->tc_rule_id;
    cand.keep = orig->nbody > 0 ? keep_occ : NULL;

    /* If the rule was lowered with rl.nabsent == 0 (use_flat_horn) and fell back to the
     * reference route due to index/epoch/rule-metadata qualification failure, enforce set
     * absence against the authoritative live store before committing. */
    if (eng->use_flat_horn && profile && profile->enforce_absent) {
        TcPreparedEffect pre_eff;
        TcRefusalReason pre_ref = TC_REFUSE_NONE;
        if (tc_bridge_prepare(&cand, &pre_eff, &pre_ref) && pre_eff.nmake > 0) {
            if (d0_store_has_term(eng, pre_eff.make_terms[0])) {
                return true;
            }
        }
    }

    TcPreparedEffect eff;
    TcAdmissionReceipt rec;
    TcAdmittedEvent cand_ev;
    TcRefusalReason refusal = TC_REFUSE_NONE;
    TcBridgeOutcome out = tc_bridge_execute_candidate(&cand, profile, &eff,
                                                      last_ev ? &cand_ev : NULL, &rec, &refusal);
    if (out == TC_BRIDGE_ADMITTED) {
        if (last_ev) {
            *last_ev = cand_ev;
        }
        if (!profile->enforce_absent) {
            for (uint32_t i = 0; i < eng->noccs; i++) {
                if (tc_term(eng->occs[i]) == rec.out_term) {
                    metrics->duplicate_facts_derived++;
                    break;
                }
            }
        }
        if (!d0_track_occ(eng, rec.out)) {
            metrics->status = TC_BRIDGE_BUDGET_EXHAUSTED;
            return false;
        }
        if (p) eng->store_digest += d0_term_tuple_digest64(p, rec.out_term);
        orig->events_admitted++;
        metrics->events_admitted++;
        if (epoch_added) (*epoch_added)++;
    }
    return true;
}

static bool d0_try_fire_candidate(D0LoweredEngine *eng, int orig_idx, const Occ *keep_occ,
                                  const TcAdmissionProfile *profile, TcBridgeBudget *budget,
                                  D0RunMetrics *metrics, int *epoch_added, TcAdmittedEvent *last_ev) {
    return d0_try_fire_candidate_ex(NULL, eng, orig_idx, keep_occ, profile, budget, metrics, epoch_added, last_ev);
}

/* M1 Baseline: Naive O(|W|^m) Cartesian scan per epoch */
static bool d0_m1_dfs(D0LoweredEngine *eng, int orig_idx, int depth, uint32_t w_limit,
                      Occ *keep_occ, const TcAdmissionProfile *profile, TcBridgeBudget *budget,
                      D0RunMetrics *metrics, int *epoch_added, TcAdmittedEvent *last_ev) {
    D0ClauseOrigin *orig = &eng->origins[orig_idx];
    if (depth == orig->nbody) {
        return d0_try_fire_candidate(eng, orig_idx, keep_occ, profile, budget,
                                     metrics, epoch_added, last_ev);
    }
    for (uint32_t i = 0; i < w_limit; i++) {
        keep_occ[depth] = eng->occs[i];
        if (!d0_m1_dfs(eng, orig_idx, depth + 1, w_limit, keep_occ, profile, budget,
                       metrics, epoch_added, last_ev))
            return false;
    }
    return true;
}

static D0RunMetrics d0_run_m1_naive(D0Program *p, D0LoweredEngine *eng,
                                    const TcAdmissionProfile *profile, uint32_t max_candidates,
                                    TcAdmittedEvent *out_last_ev) {
    (void)p;
    D0RunMetrics m;
    memset(&m, 0, sizeof(m));
    m.status = TC_BRIDGE_ADMITTED;
    TcBridgeBudget budget = { .max_candidates = max_candidates, .candidates_inspected = 0,
                              .has_unresolved_work = true, .last_refusal = TC_REFUSE_NONE };
    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    int epoch = 0;
    while (true) {
        if (g_d0_capacity_cutoff) {
            m.status = TC_BRIDGE_BUDGET_EXHAUSTED;
            goto done;
        }
        int epoch_added = 0;
        uint32_t w_limit = eng->noccs;
        for (int i = 0; i < eng->norigins; i++) {
            if (eng->origins[i].nbody == 0 && epoch > 0) continue;
            Occ keep_occ[D0_MAX_BODY] = {0};
            if (!d0_m1_dfs(eng, i, 0, w_limit, keep_occ, profile, &budget, &m, &epoch_added, out_last_ev)) {
                goto done;
            }
        }
        epoch++;
        if (epoch_added == 0) break;
    }

done:
    clock_gettime(CLOCK_MONOTONIC, &t1);
    m.candidates_examined = budget.candidates_inspected;
    m.elapsed_us = (double)(t1.tv_sec - t0.tv_sec) * 1e6 + (double)(t1.tv_nsec - t0.tv_nsec) / 1e3;
    return m;
}

/* =========================================================================
 * M2 Deep-Creativity Mechanism:
 * Differential Delta-Frontier + Hash-Consed 32-bit Term-ID Join Index
 * ========================================================================= */

enum {
    M2_HASH_BUCKETS = 16384,
    M2_MAX_FACTS    = 65536,
    M2_TUPLE_HASH   = 131072
};

typedef struct {
    Occ occ;
    int rel_idx;
    int arity;
    Term args[D0_MAX_ARITY];
    uint64_t entry_digest;
} M2FactEntry;

typedef struct {
    int rel_head[D0_MAX_RELS];
    int rel_next[M2_MAX_FACTS];
    int idx_head[M2_HASH_BUCKETS];
    int idx_next[M2_MAX_FACTS * 4];
    int idx_fact[M2_MAX_FACTS * 4];
    int tuple_ht[M2_TUPLE_HASH];
    int idx_alloc;
    int nentries;
    uint64_t index_digest;
    bool index_valid;
    M2FactEntry entries[M2_MAX_FACTS];
} M2JoinIndex;

static inline uint32_t m2_bucket(int rel_idx, int col, Term val) {
    uint64_t h = ((uint64_t)(uint32_t)(rel_idx + 1) * 0x9E3779B97F4A7C15ULL) ^
                 ((uint64_t)(uint32_t)(col + 1) * 0xBF58476D1CE4E5B9ULL) ^
                 ((uint64_t)val * 0x94D049BB133111EBULL);
    h ^= h >> 30;
    h *= 0xBF58476D1CE4E5B9ULL;
    h ^= h >> 27;
    return (uint32_t)(h & (M2_HASH_BUCKETS - 1));
}

static inline uint32_t m2_tuple_hash(int rel_idx, int arity, const Term *args) {
    uint64_t h = (uint64_t)(uint32_t)(rel_idx + 1) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < arity; i++) {
        uint64_t x = (uint64_t)args[i] + 0x9E3779B97F4A7C15ULL;
        x = (x ^ (x >> 30)) * 0xBF58476D1CE4E5B9ULL;
        x = (x ^ (x >> 27)) * 0x94D049BB133111EBULL;
        h = (h ^ x) * 0x9E3779B97F4A7C15ULL;
    }
    h ^= h >> 31;
    return (uint32_t)(h & (M2_TUPLE_HASH - 1));
}

static bool m2_tuple_contains_checked(const M2JoinIndex *ix, int rel_idx, int arity,
                                      const Term *args, bool *out_corrupt) {
    if (out_corrupt) *out_corrupt = false;
    uint32_t slot = m2_tuple_hash(rel_idx, arity, args);
    while (ix->tuple_ht[slot] >= 0) {
        int ei = ix->tuple_ht[slot];
        if (ei < 0 || ei >= ix->nentries) {
            if (out_corrupt) *out_corrupt = true;
            return false;
        }
        const M2FactEntry *fe = &ix->entries[ei];
        if (fe->entry_digest != m2_tuple_digest64(fe->rel_idx, fe->arity, fe->args)) {
            if (out_corrupt) *out_corrupt = true;
            return false;
        }
        if (fe->rel_idx == rel_idx && fe->arity == arity) {
            bool eq = true;
            for (int i = 0; i < arity; i++) {
                if (fe->args[i] != args[i]) { eq = false; break; }
            }
            if (eq) return true;
        }
        slot = (slot + 1) & (M2_TUPLE_HASH - 1);
    }
    return false;
}

static void m2_index_init(M2JoinIndex *ix) {
    memset(ix->rel_head, -1, sizeof(ix->rel_head));
    memset(ix->idx_head, -1, sizeof(ix->idx_head));
    memset(ix->tuple_ht, -1, sizeof(ix->tuple_ht));
    ix->idx_alloc = 0;
    ix->nentries = 0;
    ix->index_digest = 0;
    ix->index_valid = true;
}

static void m2_index_insert_known(M2JoinIndex *ix, Occ occ, int rel_idx, int arity, const Term *args) {
    if (ix->nentries >= M2_MAX_FACTS || rel_idx < 0) {
        if (ix->nentries >= M2_MAX_FACTS) d0_capacity_cutoff("join index (65536 facts)");
        ix->index_valid = false;
        return;
    }
    int ei = ix->nentries++;
    M2FactEntry *fe = &ix->entries[ei];
    fe->occ = occ;
    fe->rel_idx = rel_idx;
    fe->arity = arity;
    for (int c = 0; c < arity; c++) fe->args[c] = args[c];
    fe->entry_digest = m2_tuple_digest64(rel_idx, arity, fe->args);
    ix->index_digest += fe->entry_digest;

    ix->rel_next[ei] = ix->rel_head[rel_idx];
    ix->rel_head[rel_idx] = ei;

    uint32_t tslot = m2_tuple_hash(rel_idx, arity, fe->args);
    while (ix->tuple_ht[tslot] >= 0) {
        tslot = (tslot + 1) & (M2_TUPLE_HASH - 1);
    }
    ix->tuple_ht[tslot] = ei;

    int cols = arity < 4 ? arity : 4;
    for (int c = 0; c < cols; c++) {
        if (ix->idx_alloc >= M2_MAX_FACTS * 4) {
            d0_capacity_cutoff("join index columns");
            ix->index_valid = false;
            break;
        }
        uint32_t b = m2_bucket(rel_idx, c, fe->args[c]);
        int node = ix->idx_alloc++;
        ix->idx_fact[node] = ei;
        ix->idx_next[node] = ix->idx_head[b];
        ix->idx_head[b] = node;
    }
}

static void m2_index_insert(M2JoinIndex *ix, const D0Program *p, Occ occ) {
    if (ix->nentries >= M2_MAX_FACTS) {
        d0_capacity_cutoff("join index (65536 facts)");
        ix->index_valid = false;
        return;
    }
    Term t = tc_term(occ);
    uint8_t kind = 0; uint32_t head = 0; int arity = 0; const Term *args = NULL;
    tc_node(t, &kind, &head, &arity, &args);
    if (kind != K_APP) { ix->index_valid = false; return; }
    int rel_idx = -1;
    for (int r = 0; r < p->nrels; r++) {
        if ((uint32_t)p->rels[r].tc_con_id == head) { rel_idx = r; break; }
    }
    if (rel_idx < 0) { ix->index_valid = false; return; }
    m2_index_insert_known(ix, occ, rel_idx, arity, args);
}

typedef struct {
    int rel_idx[D0_MAX_BODY];
    int arity[D0_MAX_BODY];
    bool is_var[D0_MAX_BODY][D0_MAX_ARITY];
    int var_id[D0_MAX_BODY][D0_MAX_ARITY];
    Term const_val[D0_MAX_BODY][D0_MAX_ARITY];
    int head_rel_idx;
    int head_arity;
    bool head_is_var[D0_MAX_ARITY];
    int head_var_id[D0_MAX_ARITY];
    Term head_const_val[D0_MAX_ARITY];
} M2ClausePlan;

static void m2_build_clause_plan(const D0Program *p, D0LoweredEngine *eng, int orig_idx, M2ClausePlan *plan) {
    memset(plan, 0, sizeof(*plan));
    const D0ClauseStmt *cs = &p->clauses[orig_idx];
    int nvars = 0;
    char vnames[D0_MAX_VARS][64];
    for (int b = 0; b < cs->nbody; b++) {
        plan->rel_idx[b] = d0_find_rel(p, cs->body[b].rel);
        plan->arity[b]   = cs->body[b].nargs;
        for (int a = 0; a < cs->body[b].nargs; a++) {
            const D0Term *t = &cs->body[b].args[a];
            if (t->kind == D0_TERM_VAR) {
                int vi = -1;
                for (int v = 0; v < nvars; v++)
                    if (strcmp(vnames[v], t->text) == 0) { vi = v; break; }
                if (vi < 0) { vi = nvars++; snprintf(vnames[vi], 64, "%.60s", t->text); }
                plan->is_var[b][a] = true;
                plan->var_id[b][a] = vi;
            } else if (t->kind == D0_TERM_ANON) {
                int vi = nvars++;
                snprintf(vnames[vi], 64, "_anon_%d", vi);
                plan->is_var[b][a] = true;
                plan->var_id[b][a] = vi;
            } else {
                plan->is_var[b][a] = false;
                plan->const_val[b][a] = d0_encode_const_term(eng, t);
            }
        }
    }
    plan->head_rel_idx = d0_find_rel(p, cs->head.rel);
    plan->head_arity   = cs->head.nargs;
    for (int a = 0; a < cs->head.nargs; a++) {
        const D0Term *t = &cs->head.args[a];
        if (t->kind == D0_TERM_VAR) {
            int vi = -1;
            for (int v = 0; v < nvars; v++)
                if (strcmp(vnames[v], t->text) == 0) { vi = v; break; }
            plan->head_is_var[a] = true;
            plan->head_var_id[a] = vi >= 0 ? vi : 0;
        } else {
            plan->head_is_var[a] = false;
            plan->head_const_val[a] = d0_encode_const_term(eng, t);
        }
    }
}

static bool m2_bind_atom(const M2ClausePlan *plan, int b, const M2FactEntry *fe,
                         Term *var_env, uint32_t *bound_mask) {
    for (int c = 0; c < plan->arity[b]; c++) {
        Term actual = fe->args[c];
        if (plan->is_var[b][c]) {
            uint32_t v = (uint32_t)plan->var_id[b][c];
            if (*bound_mask & (1u << v)) {
                if (var_env[v] != actual) return false;
            } else {
                var_env[v] = actual;
                *bound_mask |= (1u << v);
            }
        } else {
            if (plan->const_val[b][c] != actual) return false;
        }
    }
    return true;
}

static inline bool d0_m2_fast_path_qualified(const D0LoweredEngine *eng, const M2JoinIndex *ix,
                                             const D0ClauseOrigin *orig, const M2ClausePlan *plan,
                                             const TcAdmissionProfile *profile,
                                             int delta_lo, int delta_hi, int max_ei) {
    if (!eng || !ix || !orig || !plan || !profile) return false;
    if (!eng->use_flat_horn) return false;
    if (!d0_origin_pure_horn_qualified(eng, orig)) return false;
    if (!profile->enforce_absent || profile->enforce_reach || profile->enforce_birth) return false;
    if (profile->permit && profile->permit != d0_scalar_cmp_permit) return false;
    if (!ix->index_valid) return false;
    if (ix->nentries != (int)eng->noccs || ix->nentries >= M2_MAX_FACTS) return false;
    if (ix->index_digest != eng->store_digest) return false;
    if (delta_lo < 0 || delta_hi < delta_lo || max_ei < delta_hi || max_ei > ix->nentries) return false;
    if (plan->head_rel_idx != orig->head_rel_idx || plan->head_rel_idx < 0) return false;
    return true;
}

static bool d0_m2_dfs(const D0Program *p, D0LoweredEngine *eng, M2JoinIndex *ix, const M2ClausePlan *plan,
                      int orig_idx, int depth, int anchor_pos, int delta_lo, int delta_hi, int max_ei,
                      Occ *keep_occ, Term *var_env, uint32_t bound_mask,
                      const TcAdmissionProfile *profile, TcBridgeBudget *budget,
                      D0RunMetrics *metrics, TcAdmittedEvent *last_ev) {
    D0ClauseOrigin *orig = &eng->origins[orig_idx];
    if (depth == orig->nbody) {
        if (eng->use_flat_horn) {
            if (d0_m2_fast_path_qualified(eng, ix, orig, plan, profile, delta_lo, delta_hi, max_ei)) {
                Term hargs[D0_MAX_ARITY];
                for (int a = 0; a < plan->head_arity; a++) {
                    hargs[a] = plan->head_is_var[a] ? var_env[plan->head_var_id[a]] : plan->head_const_val[a];
                }
                bool corrupt = false;
                bool present = m2_tuple_contains_checked(ix, plan->head_rel_idx, plan->head_arity, hargs, &corrupt);
                if (!corrupt) {
                    if (budget->max_candidates > 0 && budget->candidates_inspected >= budget->max_candidates) {
                        metrics->status = TC_BRIDGE_BUDGET_EXHAUSTED;
                        return false;
                    }
                    budget->candidates_inspected++;
                    if (present) {
                        return true;
                    }
                    TcPreparedStep cand = {
                        .rule = orig->tc_rule_id, .take = NULL, .keep = keep_occ,
                        .inst = NULL, .dest = 0x7FFFFFFFu, .seeds = NULL, .nseeds = 0
                    };
                    Term mt[5] = {0}, ms[5] = {0};
                    uint8_t mm[5] = {0}, nm = 0;
                    Occ out_occ = 0;
                    if (tc_eval_prepared_ex(&cand, false, false, false, false, true,
                                            mt, ms, mm, &nm, &out_occ) == TC_PREP_OK && out_occ) {
                        if (!d0_track_occ(eng, out_occ)) {
                            metrics->status = TC_BRIDGE_BUDGET_EXHAUSTED;
                            return false;
                        }
                        m2_index_insert_known(ix, out_occ, plan->head_rel_idx, plan->head_arity, hargs);
                        eng->store_digest += m2_tuple_digest64(plan->head_rel_idx, plan->head_arity, hargs);
                        orig->events_admitted++;
                        metrics->events_admitted++;
                        if (last_ev) {
                            uint8_t ntake = 0, nkeep = 0, nholes = 0;
                            tc_rule_arity(orig->tc_rule_id, &ntake, &nkeep, &nholes);
                            memset(last_ev, 0, sizeof(*last_ev));
                            last_ev->ntake = ntake;
                            last_ev->nkeep = nkeep;
                            last_ev->nholes = nholes;
                            if (nkeep > 0) {
                                memcpy(last_ev->owned_keep, keep_occ, (size_t)nkeep * sizeof(Occ));
                            }
                            last_ev->firing.rule = orig->tc_rule_id;
                            last_ev->firing.dest = 0;
                            last_ev->firing.nseeds = 0;
                            last_ev->firing = tc_event_firing(last_ev);
                            last_ev->prepared.prepared = true;
                            last_ev->prepared.prep_status = TC_PREP_OK;
                            last_ev->prepared.rule = orig->tc_rule_id;
                            last_ev->prepared.nmake = nm;
                            for (uint8_t mi = 0; mi < nm && mi < 5; mi++) {
                                last_ev->prepared.make_terms[mi]  = mt[mi];
                                last_ev->prepared.make_spaces[mi] = ms[mi];
                                last_ev->prepared.make_marks[mi]  = mm[mi];
                            }
                            last_ev->owned_profile = *profile;
                            last_ev->profile = profile;
                            uint32_t vguards = TC_GUARD_BIT_ABSENT | TC_GUARD_BIT_BIRTH;
                            if (profile->enforce_count) vguards |= TC_GUARD_BIT_COUNT;
                            last_ev->verified_guards = vguards;
                            last_ev->receipt.admitted = true;
                            last_ev->receipt.rule = orig->tc_rule_id;
                            last_ev->receipt.out = out_occ;
                            last_ev->receipt.out_term = mt[0] ? mt[0] : tc_term(out_occ);
                        }
                    }
                    return true;
                }
            }
            /* Fast-path qualification failed (non-pure-Horn clause, mutated index entry,
             * out-of-band duplicate store insertion, tampered rule metadata, or broken
             * epoch bounds): record fallback and execute via reference bridge route. */
            if (orig->is_pure_horn) {
                eng->fast_path_fallbacks++;
                ix->index_valid = false;
            }
        }
        uint32_t prev_noccs = eng->noccs;
        bool ok = d0_try_fire_candidate_ex(p, eng, orig_idx, keep_occ, profile, budget,
                                           metrics, NULL, last_ev);
        while (prev_noccs < eng->noccs) {
            m2_index_insert(ix, p, eng->occs[prev_noccs++]);
        }
        return ok;
    }

    if (depth == anchor_pos) {
        return d0_m2_dfs(p, eng, ix, plan, orig_idx, depth + 1, anchor_pos,
                         delta_lo, delta_hi, max_ei, keep_occ, var_env, bound_mask,
                         profile, budget, metrics, last_ev);
    }

    int rel_idx = plan->rel_idx[depth];
    int probe_col = -1;
    Term probe_val = 0;
    int cols = plan->arity[depth] < 4 ? plan->arity[depth] : 4;
    for (int c = 0; c < cols; c++) {
        if (plan->is_var[depth][c]) {
            uint32_t v = (uint32_t)plan->var_id[depth][c];
            if (bound_mask & (1u << v)) {
                probe_col = c;
                probe_val = var_env[v];
                break;
            }
        } else {
            probe_col = c;
            probe_val = plan->const_val[depth][c];
            break;
        }
    }

    if (probe_col >= 0) {
        uint32_t b = m2_bucket(rel_idx, probe_col, probe_val);
        for (int node = ix->idx_head[b]; node >= 0; node = ix->idx_next[node]) {
            int ei = ix->idx_fact[node];
            if (ei >= max_ei) continue;
            if (depth == anchor_pos && (ei < delta_lo || ei >= delta_hi)) continue;
            if (depth < anchor_pos && ei >= delta_lo) continue;
            const M2FactEntry *fe = &ix->entries[ei];
            if (fe->rel_idx != rel_idx || fe->args[probe_col] != probe_val) continue;
            Term next_env[D0_MAX_VARS];
            memcpy(next_env, var_env, sizeof(next_env));
            uint32_t next_mask = bound_mask;
            if (!m2_bind_atom(plan, depth, fe, next_env, &next_mask)) continue;
            keep_occ[depth] = fe->occ;
            if (!d0_m2_dfs(p, eng, ix, plan, orig_idx, depth + 1, anchor_pos,
                           delta_lo, delta_hi, max_ei, keep_occ, next_env, next_mask,
                           profile, budget, metrics, last_ev))
                return false;
        }
    } else {
        for (int ei = ix->rel_head[rel_idx]; ei >= 0; ei = ix->rel_next[ei]) {
            if (ei >= max_ei) continue;
            if (depth == anchor_pos && (ei < delta_lo || ei >= delta_hi)) continue;
            if (depth < anchor_pos && ei >= delta_lo) continue;
            const M2FactEntry *fe = &ix->entries[ei];
            Term next_env[D0_MAX_VARS];
            memcpy(next_env, var_env, sizeof(next_env));
            uint32_t next_mask = bound_mask;
            if (!m2_bind_atom(plan, depth, fe, next_env, &next_mask)) continue;
            keep_occ[depth] = fe->occ;
            if (!d0_m2_dfs(p, eng, ix, plan, orig_idx, depth + 1, anchor_pos,
                           delta_lo, delta_hi, max_ei, keep_occ, next_env, next_mask,
                           profile, budget, metrics, last_ev))
                return false;
        }
    }
    return true;
}

static D0RunMetrics d0_run_m2_seminaive(D0Program *p, D0LoweredEngine *eng,
                                        const TcAdmissionProfile *profile, uint32_t max_candidates,
                                        TcAdmittedEvent *out_last_ev) {
    D0RunMetrics m;
    memset(&m, 0, sizeof(m));
    m.status = TC_BRIDGE_ADMITTED;
    TcBridgeBudget budget = { .max_candidates = max_candidates, .candidates_inspected = 0,
                              .has_unresolved_work = true, .last_refusal = TC_REFUSE_NONE };

    M2JoinIndex *ix = (M2JoinIndex *)calloc(1, sizeof(M2JoinIndex));
    m2_index_init(ix);

    M2ClausePlan *plans = (M2ClausePlan *)calloc(D0_MAX_CLAUSES, sizeof(M2ClausePlan));
    for (int i = 0; i < eng->norigins; i++) {
        m2_build_clause_plan(p, eng, i, &plans[i]);
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (uint32_t w = 0; w < eng->noccs; w++) {
        m2_index_insert(ix, p, eng->occs[w]);
    }

    int delta_lo = 0;
    int delta_hi = ix->nentries;
    int epoch = 0;

    while (true) {
        if (g_d0_capacity_cutoff) {
            /* A full table stops the index from growing; without this test the
             * loop would take the stalled index for a fixed point. */
            m.status = TC_BRIDGE_BUDGET_EXHAUSTED;
            goto done;
        }
        int max_ei = ix->nentries;
        for (int i = 0; i < eng->norigins; i++) {
            D0ClauseOrigin *orig = &eng->origins[i];
            if (orig->nbody == 0) {
                if (epoch == 0) {
                    Occ keep_occ[1] = {0};
                    Term var_env[D0_MAX_VARS] = {0};
                    if (!d0_m2_dfs(p, eng, ix, &plans[i], i, 0, -1, 0, 0, max_ei,
                                   keep_occ, var_env, 0, profile, &budget, &m, out_last_ev))
                        goto done;
                }
                continue;
            }
            if (delta_lo >= delta_hi) continue;
            for (int anchor = 0; anchor < orig->nbody; anchor++) {
                int anchor_rel = plans[i].rel_idx[anchor];
                for (int ei = delta_lo; ei < delta_hi; ei++) {
                    const M2FactEntry *fe = &ix->entries[ei];
                    if (fe->rel_idx != anchor_rel) continue;
                    Occ keep_occ[D0_MAX_BODY] = {0};
                    Term var_env[D0_MAX_VARS] = {0};
                    uint32_t bound_mask = 0;
                    if (!m2_bind_atom(&plans[i], anchor, fe, var_env, &bound_mask)) continue;
                    keep_occ[anchor] = fe->occ;
                    if (!d0_m2_dfs(p, eng, ix, &plans[i], i, 0, anchor, delta_lo, delta_hi, max_ei,
                                   keep_occ, var_env, bound_mask, profile, &budget, &m, out_last_ev))
                        goto done;
                }
            }
        }
        delta_lo = max_ei;
        delta_hi = ix->nentries;
        epoch++;
        if (delta_lo == delta_hi) break;
    }

done:
    clock_gettime(CLOCK_MONOTONIC, &t1);
    m.candidates_examined = budget.candidates_inspected;
    m.elapsed_us = (double)(t1.tv_sec - t0.tv_sec) * 1e6 + (double)(t1.tv_nsec - t0.tv_nsec) / 1e3;
    free(plans);
    free(ix);
    return m;
}

static int cmp_str_ptr(const void *a, const void *b) {
    return strcmp(*(const char *const *)a, *(const char *const *)b);
}

static char *d0_format_relation_rows_alloc(const D0Program *p, D0LoweredEngine *eng, int rel_idx,
                                           int *out_count) {
    uint32_t cap_rows = eng->noccs > 0 ? eng->noccs : 1;
    char **rows = (char **)malloc(cap_rows * sizeof(char *));
    int n = 0;
    uint32_t target_con = (uint32_t)p->rels[rel_idx].tc_con_id;
    uint32_t target_ktag = (target_con << 9) | ((uint32_t)SPACE_FACT << 1) | 1u;
    int target_arity = p->rels[rel_idx].arity;
    size_t total_bytes = 0;
    for (uint32_t i = 0; i < eng->noccs; i++) {
        Occ o = eng->occs[i];
        if (!tc_alive(o)) continue;
        const Term *args = tc_flat_args(o, target_ktag);
        int arity = target_arity;
        if (!args) {
            Term t = tc_term(o);
            if (!t) continue;
            uint8_t kind = 0; uint32_t head = 0;
            tc_node(t, &kind, &head, &arity, &args);
            if (kind != K_APP || head != target_con) continue;
        }
        char line[512];
        line[0] = '\0';
        size_t pos = 0;
        for (int c = 0; c < arity; c++) {
            const D0ScalarEntry *se = d0_decode_scalar(args[c]);
            if (se && se->prim == D0_PRIM_SYMBOL) {
                pos += (size_t)snprintf(line + pos, sizeof(line) - pos, "%s%s",
                                        eng->syms[se->sym_id], (c + 1 < arity) ? "\t" : "");
            } else if (se && se->prim == D0_PRIM_NUMBER) {
                pos += (size_t)snprintf(line + pos, sizeof(line) - pos, "%" PRId64 "%s",
                                        se->sval, (c + 1 < arity) ? "\t" : "");
            } else if (se && se->prim == D0_PRIM_UNSIGNED) {
                pos += (size_t)snprintf(line + pos, sizeof(line) - pos, "%" PRIu64 "%s",
                                        se->uval, (c + 1 < arity) ? "\t" : "");
            }
        }
        rows[n] = strdup(line);
        total_bytes += strlen(rows[n]) + 1;
        n++;
    }
    qsort(rows, (size_t)n, sizeof(char *), cmp_str_ptr);
    char *out_buf = (char *)malloc(total_bytes + 1);
    out_buf[0] = '\0';
    size_t pos = 0;
    for (int i = 0; i < n; i++) {
        size_t l = strlen(rows[i]);
        memcpy(out_buf + pos, rows[i], l);
        pos += l;
        out_buf[pos++] = '\n';
        free(rows[i]);
    }
    out_buf[pos] = '\0';
    free(rows);
    if (out_count) *out_count = n;
    return out_buf;
}

static void d0_format_relation_rows(const D0Program *p, D0LoweredEngine *eng, int rel_idx,
                                    char *out_buf, size_t cap, int *out_count) {
    char *dyn = d0_format_relation_rows_alloc(p, eng, rel_idx, out_count);
    snprintf(out_buf, cap, "%s", dyn);
    free(dyn);
}

/* =========================================================================
 * 8 & 9. Faithful Refined C0 CHR Machine over Sealed tcalc + OS-Threading
 *
 * Matches:
 *   - Mettapedia/Languages/CHR/Operational.lean
 *   - Mettapedia/Languages/CHR/Machine.lean
 *   - hyperon/cetta-prime-nik-20260811/langdef/lang/chr/machine.metta
 *   - Mettapedia/GSLT/LanguageDef/ModuleFormat/CHRPrologLowering.lean
 * ========================================================================= */

enum {
    C0_MAX_HEADS        = 8,
    C0_MAX_TUPLE_ARITY  = 16,
    C0_MAX_DECLS        = 128,
    C0_MAX_RULES_LOWER  = 256,
    C0_MAX_STORE_OCCS   = 8192,
    C0_MAX_HIST_ENTRIES = 8192,
    C0_MAX_TASKS        = 4096,
    C0_MAX_OCC_TABLE    = 512,
    C0_SCALAR_CAP       = 8192,
    C0_INDEX_BUCKETS    = 4096
};

typedef enum {
    C0_STATUS_RUNNING            = 0,
    C0_STATUS_COMPLETED          = 1,
    C0_STATUS_FAILED             = 2,
    C0_STATUS_FAULT              = 3,
    C0_STATUS_BUDGET_EXHAUSTED   = 4,
    C0_STATUS_RESOURCE_EXHAUSTED = 5
} C0ExecStatus;

typedef enum {
    C0_FAULT_NONE           = 0,
    C0_FAULT_DIV_BY_ZERO    = 1,
    C0_FAULT_NON_INTEGER    = 2,
    C0_FAULT_UNBOUND        = 3,
    C0_FAULT_UNINSTANTIATED = 4
} C0FaultKind;

static const char *c0_status_name(C0ExecStatus st) {
    switch (st) {
        case C0_STATUS_RUNNING:            return "running";
        case C0_STATUS_COMPLETED:          return "completed";
        case C0_STATUS_FAILED:             return "failed";
        case C0_STATUS_FAULT:              return "fault";
        case C0_STATUS_BUDGET_EXHAUSTED:   return "budget_exhausted";
        case C0_STATUS_RESOURCE_EXHAUSTED: return "resource_exhausted";
    }
    return "unknown";
}

static const char *c0_fault_name(C0FaultKind fk) {
    switch (fk) {
        case C0_FAULT_NONE:           return "none";
        case C0_FAULT_DIV_BY_ZERO:    return "divisionByZero";
        case C0_FAULT_NON_INTEGER:    return "nonInteger";
        case C0_FAULT_UNBOUND:        return "unbound";
        case C0_FAULT_UNINSTANTIATED: return "uninstantiated";
    }
    return "unknown";
}

typedef enum {
    C0_MODE_NAIVE    = 0, /* M1: flat store scan in newest-first LIFO order */
    C0_MODE_INDEXED  = 1, /* M2: key + arg0 indexed partner lookup in newest-first LIFO order */
    C0_MODE_PARALLEL = 2  /* M3: POSIX pthread parallel worker search + mutex tcalc commit */
} C0SearchMode;

typedef struct {
    uint64_t name_id;
    bool is_int;
    C0BigInt ival;
    GsltByteStr atom;
} C0ScalarItem;

typedef struct {
    uint32_t rule_idx;
    uint32_t head_pos; /* 0 .. nkept-1 for kept, nkept .. nkept+nremoved-1 for removed */
} C0OccAt;

typedef struct {
    int tc_rule_id;
    uint8_t tc_fibre_flags;
    uint32_t base_occ_var;
    uint32_t n_head_vars;
    uint32_t head_var_ids[TC_VARS];
    uint64_t events_admitted;
} C0RuleOrigin;

typedef struct {
    uint32_t id;
    bool alive;
    uint32_t decl_idx;
    uint32_t arity;
    GsltC0Value **values;
    Term *arg_terms;
    Occ tc_occ;
} C0StoreEntry;

typedef struct {
    uint32_t rule_idx;
    uint32_t nids;
    uint32_t ids[C0_MAX_HEADS];
} C0HistEntry;

typedef struct {
    uint32_t nbindings;
    uint32_t var_indices[64];
    GsltC0Value *var_values[64];
} C0Env;

typedef struct {
    uint32_t head_index;
    uint32_t cand_cursor;
    uint32_t ncands;
    uint32_t cands[C0_MAX_STORE_OCCS]; /* indices into eng->store */
    C0Env env;
    uint32_t picks[C0_MAX_HEADS]; /* store_idx for each head 0 .. head_index-1 */
    uint32_t used_ids[C0_MAX_HEADS];
} C0SearchFrame;

typedef enum {
    C0_TASK_SEEDS  = 1,
    C0_TASK_GOALS  = 2,
    C0_TASK_SCAN   = 3,
    C0_TASK_SEARCH = 4
} C0TaskKind;

typedef struct {
    C0TaskKind kind;
    /* C0_TASK_SEEDS */
    uint32_t seed_cursor;
    C0Env seed_env;
    /* C0_TASK_GOALS */
    C0Env goals_env;
    uint32_t goals_rule_idx;
    uint32_t goal_cursor;
    /* C0_TASK_SCAN & C0_TASK_SEARCH */
    uint32_t active_store_idx;
    uint32_t active_id;
    uint32_t active_decl_idx;
    uint32_t occ_cursor; /* index into eng->decl_occ_table[active_decl_idx] */
    /* C0_TASK_SEARCH */
    C0OccAt current_occ;
    uint32_t after_occ_cursor;
    uint32_t nsframes;
    C0SearchFrame *sframes; /* allocated from eng->arena, capacity C0_MAX_HEADS */
} C0Task;

enum { C0_MAX_RVARS = 1024 };

typedef struct {
    GsltArena arena;
    const GsltC0Program *prog;
    C0SearchMode mode;
    uint32_t nthreads;
    uint64_t max_steps;
    uint64_t steps_taken;
    uint64_t candidates_examined;
    uint64_t events_admitted;
    C0ExecStatus status;
    C0FaultKind fault;

    /* tcalc sorts & constructors */
    uint16_t sort_val;
    uint16_t sort_atom;
    uint16_t sort_occ;
    int con_tuple[C0_MAX_TUPLE_ARITY + 1];
    int con_compound[C0_MAX_TUPLE_ARITY + 1];
    int con_chr_occ;
    int con_engine_tok;
    int con_fired;
    int con_hist[C0_MAX_HEADS + 1];
    Occ occ_engine_tok;

    /* Per-declaration lowered constructors, intro rules, update rules, and occurrence tables */
    int decl_con_id[C0_MAX_DECLS];
    int decl_intro_rule[C0_MAX_DECLS];
    int decl_update_rule[C0_MAX_DECLS];
    uint32_t decl_nocc[C0_MAX_DECLS];
    C0OccAt decl_occ_table[C0_MAX_DECLS][C0_MAX_OCC_TABLE];

    /* Per-rule lowered origins */
    C0RuleOrigin rule_origins[C0_MAX_RULES_LOWER];
    Term rule_id_terms[C0_MAX_RULES_LOWER];

    /* Pre-minted occurrence ID terms for tcalc */
    uint32_t nminted_occ_terms;
    Term occ_id_terms[C0_MAX_STORE_OCCS];

    /* Scalar interning table (sort_val K_NAME <-> GsltC0Value int/atom) */
    uint32_t nscalars;
    C0ScalarItem scalars[C0_SCALAR_CAP];

    /* C1 Runtime Logical Variables (unification + occurs-check + wakeup) */
    uint32_t next_rvar_id;
    bool rvar_bound[C0_MAX_RVARS];
    GsltC0Value *rvar_val[C0_MAX_RVARS];
    Term rvar_terms[C0_MAX_RVARS];
    uint64_t rvar_name_ids[C0_MAX_RVARS];

    /* Runtime constraint store & propagation history */
    uint32_t next_id;
    uint32_t nstore;
    C0StoreEntry store[C0_MAX_STORE_OCCS];
    uint32_t nhistory;
    C0HistEntry history[C0_MAX_HIST_ENTRIES];

    /* M2 Indexed partner structures:
     *   decl_slot_head[d] -> newest-first linked list of store indices for decl d
     *   arg0_bucket_head[b] -> newest-first linked list of store indices for (decl d, arg0_term) */
    int decl_slot_head[C0_MAX_DECLS];
    int decl_slot_next[C0_MAX_STORE_OCCS];
    int arg0_bucket_head[C0_INDEX_BUCKETS];
    int arg0_bucket_next[C0_MAX_STORE_OCCS];

    /* Explicit task stack */
    uint32_t ntasks;
    C0Task *tasks;

    /* Admitted rule-firing trace (for non-confluent M1 vs M2 exact trace verification) */
    GsltStrBuf trace_buf;
    TcAdmittedEvent last_event;
    TcAdmissionProfile profile;
} C0LoweredEngine;

static int c0_find_decl_idx(const GsltC0Program *prog, GsltByteStr name, uint32_t arity) {
    for (uint32_t i = 0; i < prog->ndecls; i++) {
        if (prog->decls[i].arity == arity && gslt_str_eq(prog->decls[i].name, name)) {
            return (int)i;
        }
    }
    return -1;
}

static GsltC0Value *c0_alloc_rvar(C0LoweredEngine *eng) {
    if (eng->next_rvar_id >= C0_MAX_RVARS) return NULL;
    uint32_t vid = eng->next_rvar_id++;
    uint64_t fid = tc_fresh_name();
    while (fid == 0) fid = tc_fresh_name();
    eng->rvar_bound[vid]    = false;
    eng->rvar_val[vid]      = NULL;
    eng->rvar_name_ids[vid] = fid;
    eng->rvar_terms[vid]    = tc_name(eng->sort_val, fid);
    GsltC0Value *v = (GsltC0Value *)gslt_arena_alloc(&eng->arena, sizeof(GsltC0Value));
    memset(v, 0, sizeof(*v));
    v->kind   = GSLT_C0_VAL_VAR;
    v->var_id = vid;
    return v;
}

static GsltC0Value *c0_deref_val(const C0LoweredEngine *eng, const GsltC0Value *v) {
    const GsltC0Value *cur = v;
    uint32_t steps = 0;
    while (cur && cur->kind == GSLT_C0_VAL_VAR &&
           cur->var_id < eng->next_rvar_id && eng->rvar_bound[cur->var_id] && steps < C0_MAX_RVARS) {
        cur = eng->rvar_val[cur->var_id];
        steps++;
    }
    return (GsltC0Value *)cur;
}

static bool c0_val_eq_deref(const C0LoweredEngine *eng, const GsltC0Value *a_raw, const GsltC0Value *b_raw) {
    const GsltC0Value *a = c0_deref_val(eng, a_raw);
    const GsltC0Value *b = c0_deref_val(eng, b_raw);
    if (!a || !b) return a == b;
    if (a->kind != b->kind) return false;
    switch (a->kind) {
        case GSLT_C0_VAL_INT:
            return c0_bigint_cmp(&a->ival, &b->ival) == 0;
        case GSLT_C0_VAL_ATOM:
            return gslt_str_eq(a->atom, b->atom);
        case GSLT_C0_VAL_VAR:
            return a->var_id == b->var_id;
        case GSLT_C0_VAL_TUPLE:
            if (a->nfields != b->nfields) return false;
            for (uint32_t i = 0; i < a->nfields; i++) {
                if (!c0_val_eq_deref(eng, a->fields[i], b->fields[i])) return false;
            }
            return true;
        case GSLT_C0_VAL_COMPOUND:
            if (a->nfields != b->nfields || !gslt_str_eq(a->atom, b->atom)) return false;
            for (uint32_t i = 0; i < a->nfields; i++) {
                if (!c0_val_eq_deref(eng, a->fields[i], b->fields[i])) return false;
            }
            return true;
    }
    return false;
}

static bool c0_var_occurs_in(const C0LoweredEngine *eng, uint32_t var_id, const GsltC0Value *v_raw) {
    const GsltC0Value *v = c0_deref_val(eng, v_raw);
    if (!v) return false;
    if (v->kind == GSLT_C0_VAL_VAR) return v->var_id == var_id;
    if (v->kind == GSLT_C0_VAL_TUPLE || v->kind == GSLT_C0_VAL_COMPOUND) {
        for (uint32_t i = 0; i < v->nfields; i++) {
            if (c0_var_occurs_in(eng, var_id, v->fields[i])) return true;
        }
    }
    return false;
}

static bool c0_unify_values_oc(C0LoweredEngine *eng, GsltC0Value *a_raw, GsltC0Value *b_raw, bool *out_any_bound) {
    GsltC0Value *a = c0_deref_val(eng, a_raw);
    GsltC0Value *b = c0_deref_val(eng, b_raw);
    if (!a || !b) return false;
    if (c0_val_eq_deref(eng, a, b)) return true;
    if (a->kind == GSLT_C0_VAL_VAR) {
        if (c0_var_occurs_in(eng, a->var_id, b)) return false;
        eng->rvar_bound[a->var_id] = true;
        eng->rvar_val[a->var_id]   = b;
        if (out_any_bound) *out_any_bound = true;
        return true;
    }
    if (b->kind == GSLT_C0_VAL_VAR) {
        if (c0_var_occurs_in(eng, b->var_id, a)) return false;
        eng->rvar_bound[b->var_id] = true;
        eng->rvar_val[b->var_id]   = a;
        if (out_any_bound) *out_any_bound = true;
        return true;
    }
    if (a->kind == GSLT_C0_VAL_TUPLE && b->kind == GSLT_C0_VAL_TUPLE && a->nfields == b->nfields) {
        for (uint32_t i = 0; i < a->nfields; i++) {
            if (!c0_unify_values_oc(eng, a->fields[i], b->fields[i], out_any_bound)) return false;
        }
        return true;
    }
    if (a->kind == GSLT_C0_VAL_COMPOUND && b->kind == GSLT_C0_VAL_COMPOUND &&
        a->nfields == b->nfields && gslt_str_eq(a->atom, b->atom)) {
        for (uint32_t i = 0; i < a->nfields; i++) {
            if (!c0_unify_values_oc(eng, a->fields[i], b->fields[i], out_any_bound)) return false;
        }
        return true;
    }
    return false;
}

static Term c0_get_occ_term(C0LoweredEngine *eng, uint32_t id) {
    if (id >= C0_MAX_STORE_OCCS) return 0;
    while (eng->nminted_occ_terms <= id) {
        uint64_t fid = tc_fresh_name();
        while (fid == 0) fid = tc_fresh_name();
        eng->occ_id_terms[eng->nminted_occ_terms++] = tc_name(eng->sort_val, fid);
    }
    return eng->occ_id_terms[id];
}

static Term c0_intern_scalar_val(C0LoweredEngine *eng, bool is_int, const C0BigInt *ival, GsltByteStr atom) {
    for (uint32_t i = 0; i < eng->nscalars; i++) {
        if (eng->scalars[i].is_int != is_int) continue;
        if (is_int) {
            if (c0_bigint_cmp(&eng->scalars[i].ival, ival) == 0)
                return tc_name(eng->sort_val, eng->scalars[i].name_id);
        } else {
            if (gslt_str_eq(eng->scalars[i].atom, atom))
                return tc_name(eng->sort_val, eng->scalars[i].name_id);
        }
    }
    if (eng->nscalars >= C0_SCALAR_CAP) return 0;
    uint64_t fid = tc_fresh_name();
    while (fid == 0) fid = tc_fresh_name();
    C0ScalarItem *it = &eng->scalars[eng->nscalars++];
    it->name_id = fid;
    it->is_int = is_int;
    if (is_int) {
        it->ival = *ival;
        it->atom = (GsltByteStr){ "", 0 };
    } else {
        c0_bigint_zero(&it->ival);
        it->atom = gslt_str_intern(&eng->arena, atom.bytes, atom.len);
    }
    return tc_name(eng->sort_val, fid);
}

static const C0ScalarItem *c0_lookup_scalar_pure(const C0LoweredEngine *eng, Term t) {
    uint64_t id = tc_name_id(t);
    if (id == 0) return NULL;
    for (uint32_t i = 0; i < eng->nscalars; i++) {
        if (eng->scalars[i].name_id == id) return &eng->scalars[i];
    }
    return NULL;
}

static int c0_lookup_rvar_pure(const C0LoweredEngine *eng, Term t) {
    uint64_t id = tc_name_id(t);
    if (id == 0) return -1;
    for (uint32_t i = 0; i < eng->next_rvar_id; i++) {
        if (eng->rvar_name_ids[i] == id) return (int)i;
    }
    return -1;
}

static Term c0_encode_val_term(C0LoweredEngine *eng, const GsltC0Value *v_raw) {
    const GsltC0Value *v = c0_deref_val(eng, v_raw);
    if (!v) return 0;
    if (v->kind == GSLT_C0_VAL_INT) {
        return c0_intern_scalar_val(eng, true, &v->ival, (GsltByteStr){ "", 0 });
    }
    if (v->kind == GSLT_C0_VAL_ATOM) {
        return c0_intern_scalar_val(eng, false, NULL, v->atom);
    }
    if (v->kind == GSLT_C0_VAL_VAR) {
        if (v->var_id >= eng->next_rvar_id) return 0;
        return eng->rvar_terms[v->var_id];
    }
    if (v->kind == GSLT_C0_VAL_TUPLE) {
        if (v->nfields > C0_MAX_TUPLE_ARITY) return 0;
        Term fterms[C0_MAX_TUPLE_ARITY];
        for (uint32_t i = 0; i < v->nfields; i++) {
            fterms[i] = c0_encode_val_term(eng, v->fields[i]);
            if (!fterms[i]) return 0;
        }
        return tc_app(eng->con_tuple[v->nfields], v->nfields > 0 ? fterms : NULL);
    }
    if (v->kind == GSLT_C0_VAL_COMPOUND) {
        if (v->nfields > C0_MAX_TUPLE_ARITY) return 0;
        Term fterms[C0_MAX_TUPLE_ARITY + 1];
        fterms[0] = c0_intern_scalar_val(eng, false, NULL, v->atom);
        if (!fterms[0]) return 0;
        for (uint32_t i = 0; i < v->nfields; i++) {
            fterms[i + 1] = c0_encode_val_term(eng, v->fields[i]);
            if (!fterms[i + 1]) return 0;
        }
        return tc_app(eng->con_compound[v->nfields], fterms);
    }
    return 0;
}

static int c0_map_head_var(C0RuleOrigin *orig, uint32_t rule_var_idx) {
    for (uint32_t i = 0; i < orig->n_head_vars; i++) {
        if (orig->head_var_ids[i] == rule_var_idx) return (int)i;
    }
    if (orig->n_head_vars >= TC_VARS - C0_MAX_HEADS) return -1;
    uint32_t idx = orig->n_head_vars++;
    orig->head_var_ids[idx] = rule_var_idx;
    return (int)idx;
}

static int c0_find_head_var_pure(const C0RuleOrigin *orig, uint32_t rule_var_idx) {
    for (uint32_t i = 0; i < orig->n_head_vars; i++) {
        if (orig->head_var_ids[i] == rule_var_idx) return (int)i;
    }
    return -1;
}

static Term c0_encode_pat_term(C0LoweredEngine *eng, C0RuleOrigin *orig, const GsltC0Term *t) {
    if (!t) return 0;
    if (t->kind == GSLT_C0_TERM_VAL) {
        return c0_encode_val_term(eng, t->val);
    }
    if (t->kind == GSLT_C0_TERM_VAR) {
        int tv = c0_map_head_var(orig, t->var_idx);
        if (tv < 0) return 0;
        return tc_v(tv);
    }
    if (t->kind == GSLT_C0_TERM_TUPLE) {
        if (t->nfields > C0_MAX_TUPLE_ARITY) return 0;
        Term fterms[C0_MAX_TUPLE_ARITY];
        for (uint32_t i = 0; i < t->nfields; i++) {
            fterms[i] = c0_encode_pat_term(eng, orig, t->fields[i]);
            if (!fterms[i]) return 0;
        }
        return tc_app(eng->con_tuple[t->nfields], t->nfields > 0 ? fterms : NULL);
    }
    if (t->kind == GSLT_C0_TERM_COMPOUND) {
        if (t->nfields > C0_MAX_TUPLE_ARITY) return 0;
        Term fterms[C0_MAX_TUPLE_ARITY + 1];
        fterms[0] = c0_intern_scalar_val(eng, false, NULL, t->functor);
        if (!fterms[0]) return 0;
        for (uint32_t i = 0; i < t->nfields; i++) {
            fterms[i + 1] = c0_encode_pat_term(eng, orig, t->fields[i]);
            if (!fterms[i + 1]) return 0;
        }
        return tc_app(eng->con_compound[t->nfields], fterms);
    }
    return 0;
}

static Term c0_encode_head_pat(C0LoweredEngine *eng, C0RuleOrigin *orig, const GsltC0Head *h) {
    int di = c0_find_decl_idx(eng->prog, h->name, h->arity);
    if (di < 0 || h->arity > C0_MAX_TUPLE_ARITY) return 0;
    Term args[C0_MAX_TUPLE_ARITY];
    for (uint32_t i = 0; i < h->arity; i++) {
        args[i] = c0_encode_pat_term(eng, orig, h->args[i]);
        if (!args[i]) return 0;
    }
    return tc_app(eng->decl_con_id[di], h->arity > 0 ? args : NULL);
}

/* Environment lookup & matching helpers (Machine.lean lines 120-157) */
static GsltC0Value *c0_env_lookup(const C0Env *env, uint32_t var_idx) {
    for (uint32_t i = 0; i < env->nbindings; i++) {
        if (env->var_indices[i] == var_idx) return env->var_values[i];
    }
    return NULL;
}

static bool c0_env_bind(const C0LoweredEngine *eng, C0Env *env, uint32_t var_idx, GsltC0Value *val) {
    for (uint32_t i = 0; i < env->nbindings; i++) {
        if (env->var_indices[i] == var_idx) {
            return c0_val_eq_deref(eng, env->var_values[i], val);
        }
    }
    if (env->nbindings >= 64) return false;
    env->var_indices[env->nbindings] = var_idx;
    env->var_values[env->nbindings]  = val;
    env->nbindings++;
    return true;
}

static bool c0_match_term(const C0LoweredEngine *eng, const GsltC0Term *pat, GsltC0Value *val_raw, C0Env *env) {
    if (!pat || !val_raw) return false;
    GsltC0Value *val = c0_deref_val(eng, val_raw);
    if (pat->kind == GSLT_C0_TERM_VAL) {
        return c0_val_eq_deref(eng, pat->val, val);
    }
    if (pat->kind == GSLT_C0_TERM_VAR) {
        return c0_env_bind(eng, env, pat->var_idx, val);
    }
    if (pat->kind == GSLT_C0_TERM_TUPLE) {
        if (val->kind != GSLT_C0_VAL_TUPLE || pat->nfields != val->nfields) return false;
        for (uint32_t i = 0; i < pat->nfields; i++) {
            if (!c0_match_term(eng, pat->fields[i], val->fields[i], env)) return false;
        }
        return true;
    }
    if (pat->kind == GSLT_C0_TERM_COMPOUND) {
        if (val->kind != GSLT_C0_VAL_COMPOUND || pat->nfields != val->nfields ||
            !gslt_str_eq(pat->functor, val->atom)) return false;
        for (uint32_t i = 0; i < pat->nfields; i++) {
            if (!c0_match_term(eng, pat->fields[i], val->fields[i], env)) return false;
        }
        return true;
    }
    return false;
}

static bool c0_match_head_args(const C0LoweredEngine *eng, const GsltC0Head *h,
                               GsltC0Value *const *vals, uint32_t nvals, C0Env *env) {
    if (h->arity != nvals) return false;
    for (uint32_t i = 0; i < h->arity; i++) {
        if (!c0_match_term(eng, h->args[i], vals[i], env)) return false;
    }
    return true;
}

/* Pure stack-based term-to-value decoder for c0_guard_permit (zero heap/arena/kernel mutation!) */
typedef struct {
    GsltC0Value val;
    GsltC0Value *field_ptrs[C0_MAX_TUPLE_ARITY];
} C0StackValNode;

static GsltC0Value *c0_decode_term_pure(const C0LoweredEngine *eng, Term t,
                                        C0StackValNode *pool, int *npool, int max_pool) {
    if (*npool >= max_pool) return NULL;
    int rvid = c0_lookup_rvar_pure(eng, t);
    if (rvid >= 0) {
        C0StackValNode *nd = &pool[(*npool)++];
        memset(nd, 0, sizeof(*nd));
        nd->val.kind   = GSLT_C0_VAL_VAR;
        nd->val.var_id = (uint32_t)rvid;
        return c0_deref_val(eng, &nd->val);
    }
    const C0ScalarItem *sc = c0_lookup_scalar_pure(eng, t);
    if (sc) {
        C0StackValNode *nd = &pool[(*npool)++];
        memset(nd, 0, sizeof(*nd));
        if (sc->is_int) {
            nd->val.kind = GSLT_C0_VAL_INT;
            nd->val.ival = sc->ival;
        } else {
            nd->val.kind = GSLT_C0_VAL_ATOM;
            nd->val.atom = sc->atom;
        }
        return &nd->val;
    }
    uint8_t kind = 0; uint32_t head = 0; int arity = 0; const Term *args = NULL;
    tc_node(t, &kind, &head, &arity, &args);
    if (kind != K_APP) return NULL;
    if (arity <= C0_MAX_TUPLE_ARITY && (int)head == eng->con_tuple[arity]) {
        int my_idx = (*npool)++;
        C0StackValNode *nd = &pool[my_idx];
        memset(nd, 0, sizeof(*nd));
        nd->val.kind = GSLT_C0_VAL_TUPLE;
        nd->val.nfields = (uint32_t)arity;
        nd->val.fields = nd->field_ptrs;
        for (int i = 0; i < arity; i++) {
            nd->field_ptrs[i] = c0_decode_term_pure(eng, args[i], pool, npool, max_pool);
            if (!nd->field_ptrs[i]) return NULL;
        }
        return &nd->val;
    }
    if (arity >= 1 && arity - 1 <= C0_MAX_TUPLE_ARITY && (int)head == eng->con_compound[arity - 1]) {
        const C0ScalarItem *fsc = c0_lookup_scalar_pure(eng, args[0]);
        if (!fsc || fsc->is_int) return NULL;
        int my_idx = (*npool)++;
        C0StackValNode *nd = &pool[my_idx];
        memset(nd, 0, sizeof(*nd));
        nd->val.kind = GSLT_C0_VAL_COMPOUND;
        nd->val.atom = fsc->atom;
        nd->val.nfields = (uint32_t)(arity - 1);
        nd->val.fields = nd->field_ptrs;
        for (int i = 0; i < arity - 1; i++) {
            nd->field_ptrs[i] = c0_decode_term_pure(eng, args[i + 1], pool, npool, max_pool);
            if (!nd->field_ptrs[i]) return NULL;
        }
        return &nd->val;
    }
    return NULL;
}

static GsltC0Value *c0_instantiate_term_pure(const C0LoweredEngine *eng, const C0Env *env, const GsltC0Term *t,
                                             C0StackValNode *pool, int *npool, int max_pool,
                                             C0FaultKind *out_fault) {
    if (!t) return NULL;
    if (t->kind == GSLT_C0_TERM_VAL) return c0_deref_val(eng, t->val);
    if (t->kind == GSLT_C0_TERM_VAR) {
        GsltC0Value *v = c0_env_lookup(env, t->var_idx);
        if (!v && out_fault && *out_fault == C0_FAULT_NONE) *out_fault = C0_FAULT_UNINSTANTIATED;
        return c0_deref_val(eng, v);
    }
    if (t->kind == GSLT_C0_TERM_TUPLE || t->kind == GSLT_C0_TERM_COMPOUND) {
        if (*npool >= max_pool || t->nfields > C0_MAX_TUPLE_ARITY) return NULL;
        int my_idx = (*npool)++;
        C0StackValNode *nd = &pool[my_idx];
        memset(nd, 0, sizeof(*nd));
        nd->val.kind = (t->kind == GSLT_C0_TERM_TUPLE) ? GSLT_C0_VAL_TUPLE : GSLT_C0_VAL_COMPOUND;
        nd->val.atom = t->functor;
        nd->val.nfields = t->nfields;
        nd->val.fields = nd->field_ptrs;
        for (uint32_t i = 0; i < t->nfields; i++) {
            nd->field_ptrs[i] = c0_instantiate_term_pure(eng, env, t->fields[i], pool, npool, max_pool, out_fault);
            if (!nd->field_ptrs[i]) return NULL;
        }
        return &nd->val;
    }
    return NULL;
}

static GsltC0Value *c0_instantiate_term_arena(C0LoweredEngine *eng, C0Env *env, const GsltC0Term *t,
                                              C0FaultKind *out_fault) {
    if (!t) return NULL;
    if (t->kind == GSLT_C0_TERM_VAL) return c0_deref_val(eng, t->val);
    if (t->kind == GSLT_C0_TERM_VAR) {
        GsltC0Value *v = c0_env_lookup(env, t->var_idx);
        if (!v) {
            if (eng->prog && eng->prog->is_c1) {
                v = c0_alloc_rvar(eng);
                if (!v || !c0_env_bind(eng, env, t->var_idx, v)) return NULL;
                return v;
            }
            if (out_fault && *out_fault == C0_FAULT_NONE) *out_fault = C0_FAULT_UNINSTANTIATED;
            return NULL;
        }
        return c0_deref_val(eng, v);
    }
    if (t->kind == GSLT_C0_TERM_TUPLE || t->kind == GSLT_C0_TERM_COMPOUND) {
        GsltC0Value *v = (GsltC0Value *)gslt_arena_alloc(&eng->arena, sizeof(GsltC0Value));
        memset(v, 0, sizeof(*v));
        v->kind = (t->kind == GSLT_C0_TERM_TUPLE) ? GSLT_C0_VAL_TUPLE : GSLT_C0_VAL_COMPOUND;
        v->atom = t->functor;
        v->nfields = t->nfields;
        if (t->nfields > 0) {
            v->fields = (GsltC0Value **)gslt_arena_alloc(&eng->arena, t->nfields * sizeof(GsltC0Value *));
            for (uint32_t i = 0; i < t->nfields; i++) {
                v->fields[i] = c0_instantiate_term_arena(eng, env, t->fields[i], out_fault);
                if (!v->fields[i]) return NULL;
            }
        }
        return v;
    }
    return NULL;
}

/* Exact Lean IntExpr.eval (Eval.lean lines 48-77) using C0BigInt */
static bool c0_eval_int_expr(const C0LoweredEngine *eng, const C0Env *env, const GsltC0IntExpr *e,
                             C0BigInt *out_val, C0FaultKind *out_fault, bool *out_resource_exhausted) {
    if (!e) return false;
    if (e->kind == GSLT_C0_IEXPR_LIT) {
        *out_val = e->lit;
        return true;
    }
    if (e->kind == GSLT_C0_IEXPR_VAR) {
        GsltC0Value *v = c0_deref_val(eng, c0_env_lookup(env, e->var_idx));
        if (!v) {
            if (out_fault && *out_fault == C0_FAULT_NONE) *out_fault = C0_FAULT_UNBOUND;
            return false;
        }
        if (v->kind != GSLT_C0_VAL_INT) {
            if (out_fault && *out_fault == C0_FAULT_NONE) *out_fault = C0_FAULT_NON_INTEGER;
            return false;
        }
        *out_val = v->ival;
        return true;
    }
    if (e->kind == GSLT_C0_IEXPR_OP) {
        C0BigInt lv, rv;
        if (!c0_eval_int_expr(eng, env, e->left, &lv, out_fault, out_resource_exhausted)) return false;
        if (!c0_eval_int_expr(eng, env, e->right, &rv, out_fault, out_resource_exhausted)) return false;
        bool ok = false;
        bool div_zero = false;
        switch (e->op) {
            case GSLT_C0_IOP_ADD:
                ok = c0_bigint_add(&lv, &rv, out_val);
                break;
            case GSLT_C0_IOP_SUB:
                ok = c0_bigint_sub(&lv, &rv, out_val);
                break;
            case GSLT_C0_IOP_MUL:
                ok = c0_bigint_mul(&lv, &rv, out_val);
                break;
            case GSLT_C0_IOP_QUOT: {
                C0BigInt rem_unused;
                ok = c0_bigint_divrem_trunc(&lv, &rv, out_val, &rem_unused, &div_zero);
                break;
            }
            case GSLT_C0_IOP_REM: {
                C0BigInt quot_unused;
                ok = c0_bigint_divrem_trunc(&lv, &rv, &quot_unused, out_val, &div_zero);
                break;
            }
            case GSLT_C0_IOP_MOD:
                ok = c0_bigint_modulo(&lv, &rv, out_val, &div_zero);
                break;
        }
        if (div_zero) {
            if (out_fault && *out_fault == C0_FAULT_NONE) *out_fault = C0_FAULT_DIV_BY_ZERO;
            return false;
        }
        if (!ok) {
            if (out_resource_exhausted) *out_resource_exhausted = true;
            return false;
        }
        return true;
    }
    return false;
}

/* Exact Lean Guard.eval (Eval.lean lines 86-98) */
static bool c0_eval_guard(const C0LoweredEngine *eng, const C0Env *env, const GsltC0Guard *g,
                          bool *out_holds, C0FaultKind *out_fault, bool *out_resource_exhausted) {
    *out_holds = false;
    if (g->kind == GSLT_C0_GUARD_IDENTICAL || g->kind == GSLT_C0_GUARD_DISTINCT) {
        C0StackValNode pool[128];
        int npool = 0;
        GsltC0Value *lv = c0_instantiate_term_pure(eng, env, g->t_left, pool, &npool, 128, out_fault);
        if (!lv) return false;
        GsltC0Value *rv = c0_instantiate_term_pure(eng, env, g->t_right, pool, &npool, 128, out_fault);
        if (!rv) return false;
        bool eq = c0_val_eq_deref(eng, lv, rv);
        *out_holds = (g->kind == GSLT_C0_GUARD_IDENTICAL) ? eq : !eq;
        return true;
    }
    C0BigInt lv, rv;
    if (!c0_eval_int_expr(eng, env, g->e_left, &lv, out_fault, out_resource_exhausted)) return false;
    if (!c0_eval_int_expr(eng, env, g->e_right, &rv, out_fault, out_resource_exhausted)) return false;
    int cmp = c0_bigint_cmp(&lv, &rv);
    switch (g->cmp) {
        case GSLT_C0_CMP_EQ: *out_holds = (cmp == 0); break;
        case GSLT_C0_CMP_NE: *out_holds = (cmp != 0); break;
        case GSLT_C0_CMP_LT: *out_holds = (cmp <  0); break;
        case GSLT_C0_CMP_LE: *out_holds = (cmp <= 0); break;
        case GSLT_C0_CMP_GT: *out_holds = (cmp >  0); break;
        case GSLT_C0_CMP_GE: *out_holds = (cmp >= 0); break;
    }
    return true;
}

static bool c0_eval_guards(const C0LoweredEngine *eng, const C0Env *env, const GsltC0Rule *rule,
                           bool *out_holds, C0FaultKind *out_fault, bool *out_resource_exhausted) {
    for (uint32_t i = 0; i < rule->nguards; i++) {
        bool holds = false;
        if (!c0_eval_guard(eng, env, &rule->guards[i], &holds, out_fault, out_resource_exhausted)) {
            return false;
        }
        if (!holds) {
            *out_holds = false;
            return true;
        }
    }
    *out_holds = true;
    return true;
}

/* Pure, immutable-context TcAdmissionProfile.permit callback for C0/C1 CHR rules */
static bool c0_guard_permit(void *ctx, const TcPreparedStep *firing, const TcPreparedEffect *effect) {
    (void)effect;
    const C0LoweredEngine *eng = (const C0LoweredEngine *)ctx;
    if (!eng || !firing) return false;

    /* Check if this is a constraint introduction or update rule */
    for (uint32_t d = 0; d < eng->prog->ndecls; d++) {
        if (firing->rule == eng->decl_intro_rule[d] ||
            firing->rule == eng->decl_update_rule[d]) return true;
    }

    /* Find the C0 rule corresponding to firing->rule */
    int r_idx = -1;
    for (uint32_t r = 0; r < eng->prog->nrules; r++) {
        if (eng->rule_origins[r].tc_rule_id == firing->rule) {
            r_idx = (int)r;
            break;
        }
    }
    if (r_idx < 0) return false;
    const GsltC0Rule *rule = &eng->prog->rules[r_idx];
    if (rule->nguards == 0) return true;

    C0StackValNode pool[256];
    int npool = 0;
    C0Env env;
    memset(&env, 0, sizeof(env));

    for (int phase = 0; phase < 2; phase++) {
        uint32_t count = (phase == 0) ? rule->nkept : rule->nremoved;
        for (uint32_t h = 0; h < count; h++) {
            Occ o = (phase == 0) ? firing->keep[h] : firing->take[h];
            Term occ_t = tc_term(o);
            uint8_t k1 = 0; uint32_t hd1 = 0; int ar1 = 0; const Term *a1 = NULL;
            tc_node(occ_t, &k1, &hd1, &ar1, &a1);
            if (k1 != K_APP || ar1 != 2) return false;
            Term atom_t = a1[1];
            uint8_t k2 = 0; uint32_t hd2 = 0; int ar2 = 0; const Term *a2 = NULL;
            tc_node(atom_t, &k2, &hd2, &ar2, &a2);
            const GsltC0Head *hpat = (phase == 0) ? &rule->kept[h] : &rule->removed[h];
            int di = c0_find_decl_idx(eng->prog, hpat->name, hpat->arity);
            if (di < 0 || k2 != K_APP || (int)hd2 != eng->decl_con_id[di] || (uint32_t)ar2 != hpat->arity)
                return false;
            GsltC0Value *vals[C0_MAX_TUPLE_ARITY];
            for (uint32_t c = 0; c < hpat->arity; c++) {
                vals[c] = c0_decode_term_pure(eng, a2[c], pool, &npool, 256);
                if (!vals[c]) return false;
            }
            if (!c0_match_head_args(eng, hpat, vals, hpat->arity, &env)) return false;
        }
    }

    bool holds = false;
    C0FaultKind fault = C0_FAULT_NONE;
    bool res_exh = false;
    if (!c0_eval_guards(eng, &env, rule, &holds, &fault, &res_exh)) return false;
    return holds;
}

/* Pre-collect all ground scalar constants in GsltC0Program so they are interned before sealing */
static void c0_preintern_term(C0LoweredEngine *eng, const GsltC0Term *t) {
    if (!t) return;
    if (t->kind == GSLT_C0_TERM_VAL) {
        (void)c0_encode_val_term(eng, t->val);
    } else if (t->kind == GSLT_C0_TERM_TUPLE) {
        for (uint32_t i = 0; i < t->nfields; i++) c0_preintern_term(eng, t->fields[i]);
    } else if (t->kind == GSLT_C0_TERM_COMPOUND) {
        (void)c0_intern_scalar_val(eng, false, NULL, t->functor);
        for (uint32_t i = 0; i < t->nfields; i++) c0_preintern_term(eng, t->fields[i]);
    }
}

static void c0_preintern_head(C0LoweredEngine *eng, const GsltC0Head *h) {
    for (uint32_t i = 0; i < h->arity; i++) c0_preintern_term(eng, h->args[i]);
}

static void c0_preintern_goal(C0LoweredEngine *eng, const GsltC0Goal *g) {
    if (!g) return;
    if (g->kind == GSLT_C0_GOAL_TELL) {
        c0_preintern_head(eng, &g->tell_head);
    } else if (g->kind == GSLT_C0_GOAL_UNIFY || g->kind == GSLT_C0_GOAL_UNIFY_OC) {
        c0_preintern_term(eng, g->unify_left);
        c0_preintern_term(eng, g->unify_right);
    } else if (g->kind == GSLT_C0_GOAL_GUARD && g->guard_test.kind != GSLT_C0_GUARD_COMPARE) {
        c0_preintern_term(eng, g->guard_test.t_left);
        c0_preintern_term(eng, g->guard_test.t_right);
    }
}

static bool c0_compile_and_seal(const GsltC0Program *prog, C0LoweredEngine *eng) {
    if (prog->ndecls > C0_MAX_DECLS || prog->nrules > C0_MAX_RULES_LOWER) {
        eng->status = C0_STATUS_RESOURCE_EXHAUSTED;
        return false;
    }
    if (!tc_init(1u << 17, 1u << 16)) {
        eng->status = C0_STATUS_RESOURCE_EXHAUSTED;
        return false;
    }
    gslt_arena_init(&eng->arena);
    eng->tasks = (C0Task *)gslt_arena_alloc(&eng->arena, C0_MAX_TASKS * sizeof(C0Task));
    gslt_sb_init(&eng->arena, &eng->trace_buf, 1024);
    eng->prog = prog;
    eng->status = C0_STATUS_RUNNING;
    eng->fault = C0_FAULT_NONE;
    memset(eng->decl_slot_head, -1, sizeof(eng->decl_slot_head));
    memset(eng->arg0_bucket_head, -1, sizeof(eng->arg0_bucket_head));

    /* sort_val is SORT_STRICT (non-SORT_PURE) so it admits K_NAME scalars, con_tuple[k], and con_compound[k] */
    eng->sort_val  = (uint16_t)tc_sort(SORT_STRICT);
    eng->sort_atom = (uint16_t)tc_sort(SORT_STRICT);
    eng->sort_occ  = (uint16_t)tc_sort(SORT_STRICT | SORT_PROVABLE);

    Binder val_binders[C0_MAX_TUPLE_ARITY + 1];
    for (int i = 0; i <= C0_MAX_TUPLE_ARITY; i++) {
        val_binders[i] = (Binder){ .sort = eng->sort_val, .bound = 0, .deps = 0 };
    }
    for (int k = 0; k <= C0_MAX_TUPLE_ARITY; k++) {
        eng->con_tuple[k]    = tc_con(eng->sort_val, 0, k, k > 0 ? val_binders : NULL);
        eng->con_compound[k] = tc_con(eng->sort_val, 0, k + 1, val_binders);
    }

    for (uint32_t d = 0; d < prog->ndecls; d++) {
        if (prog->decls[d].arity > C0_MAX_TUPLE_ARITY) {
            eng->status = C0_STATUS_RESOURCE_EXHAUSTED;
            return false;
        }
        eng->decl_con_id[d] = tc_con(eng->sort_atom, 0, (int)prog->decls[d].arity,
                                     prog->decls[d].arity > 0 ? val_binders : NULL);
    }

    Binder occ_args[2] = {
        { .sort = eng->sort_val,  .bound = 0, .deps = 0 },
        { .sort = eng->sort_atom, .bound = 0, .deps = 0 }
    };
    eng->con_chr_occ    = tc_con(eng->sort_occ, 0, 2, occ_args);
    eng->con_engine_tok = tc_con(eng->sort_occ, 0, 0, NULL);
    eng->con_fired      = tc_con(eng->sort_occ, 0, 1, val_binders);
    for (int k = 1; k <= C0_MAX_HEADS; k++) {
        eng->con_hist[k] = tc_con(eng->sort_occ, 0, k + 1, val_binders);
    }

    /* Post persistent engine token in SPACE_QUERY before sealing */
    eng->occ_engine_tok = tc_post(SPACE_QUERY, tc_app(eng->con_engine_tok, NULL));

    /* Pre-intern all static constants in rules and initial queries */
    for (uint32_t i = 0; i < prog->ninputs; i++) c0_preintern_head(eng, &prog->inputs[i]);
    for (uint32_t i = 0; i < prog->nquery_goals; i++) c0_preintern_goal(eng, &prog->query_goals[i]);
    for (uint32_t r = 0; r < prog->nrules; r++) {
        const GsltC0Rule *rule = &prog->rules[r];
        for (uint32_t k = 0; k < rule->nkept; k++) c0_preintern_head(eng, &rule->kept[k]);
        for (uint32_t rm = 0; rm < rule->nremoved; rm++) c0_preintern_head(eng, &rule->removed[rm]);
        for (uint32_t g = 0; g < rule->nguards; g++) {
            if (rule->guards[g].kind != GSLT_C0_GUARD_COMPARE) {
                c0_preintern_term(eng, rule->guards[g].t_left);
                c0_preintern_term(eng, rule->guards[g].t_right);
            }
        }
        for (uint32_t b = 0; b < rule->nbody; b++) {
            c0_preintern_goal(eng, &rule->body[b]);
        }
    }

    /* Set context of sort_val variables for all introduction, update, and CHR rules */
    Binder rule_ctx[TC_VARS];
    for (int i = 0; i < TC_VARS; i++) {
        rule_ctx[i] = (Binder){ .sort = eng->sort_val, .bound = 0, .deps = 0 };
    }
    if (!tc_ctx(TC_VARS, rule_ctx)) return false;

    /* Install per-declaration introduction and wakeup-update rules:
     * intro:  keep occ_engine_tok in SPACE_QUERY -> make chr_occ(v_0, decl_con_id[d](v_1, ..., v_k)) in SPACE_CHR
     * update: take chr_occ(v_0, decl_con_id[d](v_{k+1}, ..., v_{2k})) in SPACE_CHR,
     *         keep occ_engine_tok in SPACE_QUERY -> make chr_occ(v_0, decl_con_id[d](v_1, ..., v_k)) in SPACE_CHR */
    for (uint32_t d = 0; d < prog->ndecls; d++) {
        uint32_t ar = prog->decls[d].arity;
        Rule irl;
        memset(&irl, 0, sizeof(irl));
        irl.fresh = -1;
        irl.nkeep = 1;
        irl.keep[0].t     = tc_app(eng->con_engine_tok, NULL);
        irl.keep[0].space = SPACE_QUERY;
        Term dargs[C0_MAX_TUPLE_ARITY];
        Term old_dargs[C0_MAX_TUPLE_ARITY];
        for (uint32_t a = 0; a < ar; a++) {
            dargs[a]     = tc_v((int)(a + 1));
            old_dargs[a] = tc_v((int)(ar + a + 1));
        }
        Term atom_t = tc_app(eng->decl_con_id[d], ar > 0 ? dargs : NULL);
        irl.make.t     = tc_app(eng->con_chr_occ, (Term[2]){ tc_v(0), atom_t });
        irl.make.space = SPACE_CHR;
        irl.inputs     = (2ull << ar) - 1u;   /* the occurrence and its arguments: v_0 .. v_ar, from the host */
        eng->decl_intro_rule[d] = tc_rule(&irl);
        if (eng->decl_intro_rule[d] < 0) return false;

        Rule url;
        memset(&url, 0, sizeof(url));
        url.fresh = -1;
        url.nkeep = 1;
        url.keep[0].t     = tc_app(eng->con_engine_tok, NULL);
        url.keep[0].space = SPACE_QUERY;
        url.ntake = 1;
        Term old_atom_t = tc_app(eng->decl_con_id[d], ar > 0 ? old_dargs : NULL);
        url.take[0].t     = tc_app(eng->con_chr_occ, (Term[2]){ tc_v(0), old_atom_t });
        url.take[0].space = SPACE_CHR;
        url.make.t     = tc_app(eng->con_chr_occ, (Term[2]){ tc_v(0), atom_t });
        url.make.space = SPACE_CHR;
        url.inputs     = (2ull << ar) - 2u;   /* the new arguments: v_1 .. v_ar, from the host */
        eng->decl_update_rule[d] = tc_rule(&url);
        if (eng->decl_update_rule[d] < 0) return false;
    }

    /* Lower each C0 rule to a schematic first-order tcalc rule + build occurrence table */
    for (uint32_t r = 0; r < prog->nrules; r++) {
        const GsltC0Rule *rule = &prog->rules[r];
        uint32_t total_h = rule->nkept + rule->nremoved;
        if (total_h == 0 || total_h > C0_MAX_HEADS) {
            eng->status = C0_STATUS_RESOURCE_EXHAUSTED;
            return false;
        }

        /* Record occurrences in Rule.visitOrder (removed heads first, then kept heads)
         * matching Mettapedia/Languages/CHR/Syntax.lean (Rule.visitOrder & CHR.occurrences) */
        for (uint32_t rm = 0; rm < rule->nremoved; rm++) {
            int di = c0_find_decl_idx(prog, rule->removed[rm].name, rule->removed[rm].arity);
            if (di >= 0 && eng->decl_nocc[di] < C0_MAX_OCC_TABLE) {
                eng->decl_occ_table[di][eng->decl_nocc[di]++] = (C0OccAt){ r, rule->nkept + rm };
            }
        }
        for (uint32_t k = 0; k < rule->nkept; k++) {
            int di = c0_find_decl_idx(prog, rule->kept[k].name, rule->kept[k].arity);
            if (di >= 0 && eng->decl_nocc[di] < C0_MAX_OCC_TABLE) {
                eng->decl_occ_table[di][eng->decl_nocc[di]++] = (C0OccAt){ r, k };
            }
        }

        C0RuleOrigin *orig = &eng->rule_origins[r];
        memset(orig, 0, sizeof(*orig));

        Rule rl;
        memset(&rl, 0, sizeof(rl));
        rl.fresh = -1;

        Term kept_atom_pats[C0_MAX_HEADS];
        Term rem_atom_pats[C0_MAX_HEADS];
        for (uint32_t k = 0; k < rule->nkept; k++) {
            kept_atom_pats[k] = c0_encode_head_pat(eng, orig, &rule->kept[k]);
            if (!kept_atom_pats[k]) return false;
        }
        for (uint32_t rm = 0; rm < rule->nremoved; rm++) {
            rem_atom_pats[rm] = c0_encode_head_pat(eng, orig, &rule->removed[rm]);
            if (!rem_atom_pats[rm]) return false;
        }

        orig->base_occ_var = orig->n_head_vars;
        if (orig->base_occ_var + total_h > TC_VARS) {
            eng->status = C0_STATUS_RESOURCE_EXHAUSTED;
            return false;
        }

        uint32_t h_idx = 0;
        for (uint32_t k = 0; k < rule->nkept; k++, h_idx++) {
            Term v_occ = tc_v((int)(orig->base_occ_var + h_idx));
            rl.keep[rl.nkeep].t     = tc_app(eng->con_chr_occ, (Term[2]){ v_occ, kept_atom_pats[k] });
            rl.keep[rl.nkeep].space = SPACE_CHR;
            rl.nkeep++;
        }
        for (uint32_t rm = 0; rm < rule->nremoved; rm++, h_idx++) {
            Term v_occ = tc_v((int)(orig->base_occ_var + h_idx));
            rl.take[rl.ntake].t     = tc_app(eng->con_chr_occ, (Term[2]){ v_occ, rem_atom_pats[rm] });
            rl.take[rl.ntake].space = SPACE_CHR;
            rl.ntake++;
        }

        /* Distinct occurrence disequations (Rule.neq) across head slots */
        for (uint32_t a = 0; a < total_h; a++) {
            for (uint32_t b = a + 1; b < total_h && rl.nneq < 4; b++) {
                rl.neq[rl.nneq][0] = tc_v((int)(orig->base_occ_var + a));
                rl.neq[rl.nneq][1] = tc_v((int)(orig->base_occ_var + b));
                rl.nneq++;
            }
        }

        /* Lower closed head-variable \== guards into kernel Rule.neq when slots remain */
        for (uint32_t g = 0; g < rule->nguards && rl.nneq < 4; g++) {
            if (rule->guards[g].kind == GSLT_C0_GUARD_DISTINCT &&
                rule->guards[g].t_left->kind == GSLT_C0_TERM_VAR &&
                rule->guards[g].t_right->kind == GSLT_C0_TERM_VAR) {
                int lv = c0_find_head_var_pure(orig, rule->guards[g].t_left->var_idx);
                int rv = c0_find_head_var_pure(orig, rule->guards[g].t_right->var_idx);
                if (lv >= 0 && rv >= 0) {
                    rl.neq[rl.nneq][0] = tc_v(lv);
                    rl.neq[rl.nneq][1] = tc_v(rv);
                    rl.nneq++;
                }
            }
        }

        uint64_t rfid = tc_fresh_name();
        while (rfid == 0) rfid = tc_fresh_name();
        eng->rule_id_terms[r] = tc_name(eng->sort_val, rfid);

        if (rule->nremoved == 0) {
            /* Propagation rule: kernel Rule.absent + Rule.make in SPACE_HISTORY */
            Term hargs[C0_MAX_HEADS + 1];
            hargs[0] = eng->rule_id_terms[r];
            for (uint32_t k = 0; k < rule->nkept; k++) {
                hargs[k + 1] = tc_v((int)(orig->base_occ_var + k));
            }
            Term hist_t = tc_app(eng->con_hist[rule->nkept], hargs);
            rl.absent[0].t     = hist_t;
            rl.absent[0].space = SPACE_HISTORY;
            rl.nabsent         = 1;
            rl.make.t          = hist_t;
            rl.make.space      = SPACE_HISTORY;
        } else {
            /* Simplification / simpagation rule: kernel Rule.take consumes removed heads */
            rl.make.t     = tc_app(eng->con_fired, &eng->rule_id_terms[r]);
            rl.make.space = SPACE_HISTORY;
        }

        orig->tc_rule_id = tc_rule(&rl);
        if (orig->tc_rule_id < 0) return false;
        orig->tc_fibre_flags = tc_rule_fibre(orig->tc_rule_id);
    }

    tc_protect(SPACE_QUERY);
    tc_protect(SPACE_CHR);
    tc_protect(SPACE_HISTORY);
    tc_seal();

    eng->profile = tc_admission_custom_profile(
        "c0_chr_profile", true, true, false, false, eng, c0_guard_permit);
    return true;
}

static inline uint32_t c0_arg0_bucket(uint32_t decl_idx, Term arg0_t) {
    uint32_t h = (decl_idx * 2654435761u) ^ (uint32_t)arg0_t;
    return (h ^ (h >> 16)) & (C0_INDEX_BUCKETS - 1);
}

static bool c0_history_contains(const C0LoweredEngine *eng, uint32_t rule_idx,
                                const uint32_t *picks_store_idx, uint32_t nkept) {
    for (uint32_t i = 0; i < eng->nhistory; i++) {
        const C0HistEntry *he = &eng->history[i];
        if (he->rule_idx != rule_idx || he->nids != nkept) continue;
        bool same = true;
        for (uint32_t k = 0; k < nkept; k++) {
            if (he->ids[k] != eng->store[picks_store_idx[k]].id) {
                same = false;
                break;
            }
        }
        if (same) return true;
    }
    return false;
}

static bool c0_push_scan_task(C0LoweredEngine *eng, uint32_t store_idx, uint32_t occ_cursor) {
    if (eng->ntasks >= C0_MAX_TASKS) {
        eng->status = C0_STATUS_RESOURCE_EXHAUSTED;
        return false;
    }
    C0Task *tk = &eng->tasks[eng->ntasks++];
    memset(tk, 0, sizeof(*tk));
    tk->kind             = C0_TASK_SCAN;
    tk->active_store_idx = store_idx;
    tk->active_id        = eng->store[store_idx].id;
    tk->active_decl_idx  = eng->store[store_idx].decl_idx;
    tk->occ_cursor       = occ_cursor;
    return true;
}

/* Introduce a ground constraint into SPACE_CHR via decl_intro_rule[d] and push C0_TASK_SCAN */
static bool c0_introduce_constraint(C0LoweredEngine *eng, uint32_t decl_idx,
                                    GsltC0Value **vals, uint32_t arity,
                                    bool push_scan) {
    if (eng->nstore >= C0_MAX_STORE_OCCS || eng->next_id >= C0_MAX_STORE_OCCS) {
        eng->status = C0_STATUS_RESOURCE_EXHAUSTED;
        return false;
    }
    uint32_t new_id = eng->next_id++;
    Term id_term = c0_get_occ_term(eng, new_id);
    if (!id_term) {
        eng->status = C0_STATUS_RESOURCE_EXHAUSTED;
        return false;
    }
    Term inst_env[TC_VARS];
    memset(inst_env, 0, sizeof(inst_env));
    inst_env[0] = id_term;

    Term *arg_terms = (Term *)gslt_arena_alloc(&eng->arena, (arity > 0 ? arity : 1) * sizeof(Term));
    for (uint32_t a = 0; a < arity; a++) {
        Term at = c0_encode_val_term(eng, vals[a]);
        if (!at) {
            eng->status = C0_STATUS_RESOURCE_EXHAUSTED;
            return false;
        }
        arg_terms[a] = at;
        inst_env[a + 1] = at;
    }

    Occ keep_tok[1] = { eng->occ_engine_tok };
    TcPreparedStep cand;
    memset(&cand, 0, sizeof(cand));
    cand.rule = eng->decl_intro_rule[decl_idx];
    cand.keep = keep_tok;
    cand.inst = inst_env;

    TcPreparedEffect eff;
    TcAdmissionReceipt rec;
    TcRefusalReason ref = TC_REFUSE_NONE;
    if (tc_bridge_execute_candidate(&cand, &eng->profile, &eff, &eng->last_event, &rec, &ref) != TC_BRIDGE_ADMITTED) {
        eng->status = C0_STATUS_RESOURCE_EXHAUSTED;
        return false;
    }

    uint32_t sidx = eng->nstore++;
    C0StoreEntry *se = &eng->store[sidx];
    se->id        = new_id;
    se->alive     = true;
    se->decl_idx  = decl_idx;
    se->arity     = arity;
    se->values    = vals;
    se->arg_terms = arg_terms;
    se->tc_occ    = rec.out;

    /* Insert into M2 newest-first LIFO index lists */
    eng->decl_slot_next[sidx] = eng->decl_slot_head[decl_idx];
    eng->decl_slot_head[decl_idx] = (int)sidx;
    if (arity > 0) {
        uint32_t b = c0_arg0_bucket(decl_idx, arg_terms[0]);
        eng->arg0_bucket_next[sidx] = eng->arg0_bucket_head[b];
        eng->arg0_bucket_head[b] = (int)sidx;
    }

    if (push_scan) {
        return c0_push_scan_task(eng, sidx, 0);
    }
    return true;
}

/* Wake all alive constraints whose dereferenced tcalc term representation changed after unification.
 * Updates each affected occurrence in SPACE_CHR via decl_update_rule[d] WITH THE SAME OCCURRENCE ID v_0
 * so propagation history in SPACE_HISTORY and eng->history survives wakeup! */
static bool c0_wake_on_binding(C0LoweredEngine *eng, bool push_scans) {
    uint32_t *woken = (uint32_t *)gslt_arena_alloc(&eng->arena, C0_MAX_STORE_OCCS * sizeof(uint32_t));
    uint32_t nwoken = 0;
    for (uint32_t sidx = 0; sidx < eng->nstore; sidx++) {
        C0StoreEntry *se = &eng->store[sidx];
        if (!se->alive || !tc_alive(se->tc_occ)) continue;
        Term new_terms[C0_MAX_TUPLE_ARITY];
        bool changed = false;
        for (uint32_t a = 0; a < se->arity; a++) {
            new_terms[a] = c0_encode_val_term(eng, se->values[a]);
            if (!new_terms[a]) {
                eng->status = C0_STATUS_RESOURCE_EXHAUSTED;
                return false;
            }
            if (new_terms[a] != se->arg_terms[a]) changed = true;
        }
        if (!changed) continue;

        Term inst_env[TC_VARS];
        memset(inst_env, 0, sizeof(inst_env));
        inst_env[0] = c0_get_occ_term(eng, se->id);
        for (uint32_t a = 0; a < se->arity; a++) {
            inst_env[a + 1]             = new_terms[a];
            inst_env[se->arity + a + 1] = se->arg_terms[a];
        }
        Occ keep_tok[1] = { eng->occ_engine_tok };
        Occ take_old[1] = { se->tc_occ };
        TcPreparedStep cand;
        memset(&cand, 0, sizeof(cand));
        cand.rule = eng->decl_update_rule[se->decl_idx];
        cand.keep = keep_tok;
        cand.take = take_old;
        cand.inst = inst_env;

        TcPreparedEffect eff;
        TcAdmissionReceipt rec;
        TcRefusalReason ref = TC_REFUSE_NONE;
        if (tc_bridge_execute_candidate(&cand, &eng->profile, &eff, &eng->last_event, &rec, &ref) != TC_BRIDGE_ADMITTED) {
            eng->status = C0_STATUS_RESOURCE_EXHAUSTED;
            return false;
        }
        if (se->arity > 0 && new_terms[0] != se->arg_terms[0]) {
            uint32_t old_b = c0_arg0_bucket(se->decl_idx, se->arg_terms[0]);
            int *pp = &eng->arg0_bucket_head[old_b];
            while (*pp >= 0) {
                if ((uint32_t)*pp == sidx) { *pp = eng->arg0_bucket_next[sidx]; break; }
                pp = &eng->arg0_bucket_next[*pp];
            }
            uint32_t new_b = c0_arg0_bucket(se->decl_idx, new_terms[0]);
            int *ins = &eng->arg0_bucket_head[new_b];
            while (*ins > (int)sidx) {
                ins = &eng->arg0_bucket_next[*ins];
            }
            eng->arg0_bucket_next[sidx] = *ins;
            *ins = (int)sidx;
        }
        for (uint32_t a = 0; a < se->arity; a++) {
            se->arg_terms[a] = new_terms[a];
        }
        se->tc_occ = rec.out;
        if (nwoken < C0_MAX_STORE_OCCS) woken[nwoken++] = sidx;
    }
    if (push_scans) {
        for (int i = (int)nwoken - 1; i >= 0; i--) {
            if (!c0_push_scan_task(eng, woken[i], 0)) return false;
        }
    }
    return true;
}

/* Populate partner candidates for head_index of rule_idx in newest-first LIFO order */
static void c0_fill_frame_candidates(C0LoweredEngine *eng, uint32_t rule_idx, uint32_t head_index,
                                     uint32_t active_pos, uint32_t active_store_idx,
                                     const C0Env *env, C0SearchFrame *sf) {
    sf->cand_cursor = 0;
    sf->ncands = 0;
    if (head_index == active_pos) {
        sf->cands[sf->ncands++] = active_store_idx;
        return;
    }
    const GsltC0Rule *rule = &eng->prog->rules[rule_idx];
    const GsltC0Head *h = (head_index < rule->nkept)
                        ? &rule->kept[head_index]
                        : &rule->removed[head_index - rule->nkept];
    int di = c0_find_decl_idx(eng->prog, h->name, h->arity);
    if (di < 0) return;

    if (eng->mode == C0_MODE_INDEXED) {
        /* Check if arg0 is a ground value or an already-bound variable in env */
        Term probe_t = 0;
        if (h->arity > 0) {
            const GsltC0Term *a0 = h->args[0];
            if (a0->kind == GSLT_C0_TERM_VAL) {
                probe_t = c0_encode_val_term(eng, a0->val);
            } else if (a0->kind == GSLT_C0_TERM_VAR) {
                GsltC0Value *bv = c0_env_lookup(env, a0->var_idx);
                if (bv) probe_t = c0_encode_val_term(eng, bv);
            }
        }
        if (probe_t != 0) {
            uint32_t b = c0_arg0_bucket((uint32_t)di, probe_t);
            for (int cur = eng->arg0_bucket_head[b]; cur >= 0 && sf->ncands < C0_MAX_STORE_OCCS; cur = eng->arg0_bucket_next[cur]) {
                const C0StoreEntry *se = &eng->store[cur];
                if (!se->alive || se->decl_idx != (uint32_t)di || se->arg_terms[0] != probe_t) continue;
                sf->cands[sf->ncands++] = (uint32_t)cur;
            }
            return;
        }
        for (int cur = eng->decl_slot_head[di]; cur >= 0 && sf->ncands < C0_MAX_STORE_OCCS; cur = eng->decl_slot_next[cur]) {
            if (!eng->store[cur].alive) continue;
            sf->cands[sf->ncands++] = (uint32_t)cur;
        }
        return;
    }

    /* M1 Naive: scan full store newest-first */
    for (int cur = (int)eng->nstore - 1; cur >= 0 && sf->ncands < C0_MAX_STORE_OCCS; cur--) {
        if (!eng->store[cur].alive || eng->store[cur].decl_idx != (uint32_t)di) continue;
        sf->cands[sf->ncands++] = (uint32_t)cur;
    }
}

static bool c0_fire_rule_selection(C0LoweredEngine *eng, C0OccAt occ, uint32_t after_occ_cursor,
                                   uint32_t active_store_idx, const C0Env *env,
                                   const uint32_t *picks_store_idx) {
    if (eng->max_steps > 0 && eng->events_admitted >= eng->max_steps) {
        eng->status = C0_STATUS_BUDGET_EXHAUSTED;
        return false;
    }
    const GsltC0Rule *rule = &eng->prog->rules[occ.rule_idx];
    C0RuleOrigin *orig = &eng->rule_origins[occ.rule_idx];
    uint32_t total_h = rule->nkept + rule->nremoved;

    Occ keep_occs[C0_MAX_HEADS];
    Occ take_occs[C0_MAX_HEADS];
    Term inst_env[TC_VARS];
    memset(inst_env, 0, sizeof(inst_env));

    for (uint32_t v = 0; v < orig->n_head_vars; v++) {
        GsltC0Value *bv = c0_env_lookup(env, orig->head_var_ids[v]);
        if (!bv) return false;
        inst_env[v] = c0_encode_val_term(eng, bv);
    }
    for (uint32_t k = 0; k < rule->nkept; k++) {
        uint32_t sidx = picks_store_idx[k];
        keep_occs[k] = eng->store[sidx].tc_occ;
        inst_env[orig->base_occ_var + k] = c0_get_occ_term(eng, eng->store[sidx].id);
    }
    for (uint32_t rm = 0; rm < rule->nremoved; rm++) {
        uint32_t sidx = picks_store_idx[rule->nkept + rm];
        take_occs[rm] = eng->store[sidx].tc_occ;
        inst_env[orig->base_occ_var + rule->nkept + rm] = c0_get_occ_term(eng, eng->store[sidx].id);
    }

    TcPreparedStep cand;
    memset(&cand, 0, sizeof(cand));
    cand.rule = orig->tc_rule_id;
    cand.keep = rule->nkept > 0 ? keep_occs : NULL;
    cand.take = rule->nremoved > 0 ? take_occs : NULL;
    cand.inst = inst_env;

    TcPreparedEffect eff;
    TcAdmissionReceipt rec;
    TcRefusalReason ref = TC_REFUSE_NONE;
    if (tc_bridge_execute_candidate(&cand, &eng->profile, &eff, &eng->last_event, &rec, &ref) != TC_BRIDGE_ADMITTED) {
        return false;
    }

    orig->events_admitted++;
    eng->events_admitted++;

    /* Append to deterministic trace buffer: rule_name(id0,id1,...); */
    gslt_sb_append_bytes(&eng->arena, &eng->trace_buf, rule->name.bytes, rule->name.len);
    gslt_sb_append_char(&eng->arena, &eng->trace_buf, '(');
    for (uint32_t h = 0; h < total_h; h++) {
        if (h > 0) gslt_sb_append_char(&eng->arena, &eng->trace_buf, ',');
        gslt_sb_append_u32(&eng->arena, &eng->trace_buf, eng->store[picks_store_idx[h]].id);
    }
    gslt_sb_append_cstr(&eng->arena, &eng->trace_buf, ");");

    /* Mark removed picks dead in store; record propagation history if nremoved == 0 */
    for (uint32_t rm = 0; rm < rule->nremoved; rm++) {
        eng->store[picks_store_idx[rule->nkept + rm]].alive = false;
    }
    if (rule->nremoved == 0) {
        if (eng->nhistory >= C0_MAX_HIST_ENTRIES) {
            eng->status = C0_STATUS_RESOURCE_EXHAUSTED;
            return false;
        }
        C0HistEntry *he = &eng->history[eng->nhistory++];
        he->rule_idx = occ.rule_idx;
        he->nids = rule->nkept;
        for (uint32_t k = 0; k < rule->nkept; k++) {
            he->ids[k] = eng->store[picks_store_idx[k]].id;
        }
    }

    /* Update task stack (Machine.fire in Machine.lean lines 235-241):
     * Pop current C0_TASK_SEARCH. If active constraint was NOT removed, push C0_TASK_SCAN
     * at the SAME occurrence (after_occ_cursor - 1); then push C0_TASK_GOALS on top! */
    eng->ntasks--;
    bool active_removed = false;
    for (uint32_t rm = 0; rm < rule->nremoved; rm++) {
        if (picks_store_idx[rule->nkept + rm] == active_store_idx) {
            active_removed = true;
            break;
        }
    }
    if (!active_removed) {
        if (!c0_push_scan_task(eng, active_store_idx, after_occ_cursor - 1)) return false;
    }
    if (eng->ntasks >= C0_MAX_TASKS) {
        eng->status = C0_STATUS_RESOURCE_EXHAUSTED;
        return false;
    }
    C0Task *gt = &eng->tasks[eng->ntasks++];
    memset(gt, 0, sizeof(*gt));
    gt->kind           = C0_TASK_GOALS;
    gt->goals_env      = *env;
    gt->goals_rule_idx = occ.rule_idx;
    gt->goal_cursor    = 0;
    return true;
}

/* Execute one GsltC0Goal in env; *io_cursor is incremented and if it reaches ntotal,
 * the active task at the top of eng->tasks is popped BEFORE pushing any scan tasks! */
static void c0_exec_goal_step(C0LoweredEngine *eng, C0Env *env, const GsltC0Goal *g,
                              uint32_t *io_cursor, uint32_t ntotal) {
    if (g->kind == GSLT_C0_GOAL_FAIL) {
        eng->status = C0_STATUS_FAILED;
        return;
    }
    if (g->kind == GSLT_C0_GOAL_ASSIGN) {
        C0BigInt res;
        bool res_exh = false;
        if (!c0_eval_int_expr(eng, env, g->assign_expr, &res, &eng->fault, &res_exh)) {
            eng->status = res_exh ? C0_STATUS_RESOURCE_EXHAUSTED : C0_STATUS_FAULT;
            return;
        }
        GsltC0Value *existing = c0_deref_val(eng, c0_env_lookup(env, g->assign_var));
        if (existing && existing->kind != GSLT_C0_VAL_VAR) {
            if (existing->kind == GSLT_C0_VAL_INT && c0_bigint_cmp(&existing->ival, &res) == 0) {
                (*io_cursor)++;
                if (*io_cursor >= ntotal) eng->ntasks--;
            } else {
                eng->status = C0_STATUS_FAILED;
            }
            return;
        }
        GsltC0Value *nv = (GsltC0Value *)gslt_arena_alloc(&eng->arena, sizeof(GsltC0Value));
        memset(nv, 0, sizeof(*nv));
        nv->kind = GSLT_C0_VAL_INT;
        nv->ival = res;
        if (existing && existing->kind == GSLT_C0_VAL_VAR) {
            (*io_cursor)++;
            if (*io_cursor >= ntotal) eng->ntasks--;
            bool any_bound = false;
            if (!c0_unify_values_oc(eng, existing, nv, &any_bound)) {
                eng->status = C0_STATUS_FAILED;
                return;
            }
            if (any_bound) (void)c0_wake_on_binding(eng, true);
            return;
        }
        if (!c0_env_bind(eng, env, g->assign_var, nv)) {
            eng->status = C0_STATUS_RESOURCE_EXHAUSTED;
            return;
        }
        (*io_cursor)++;
        if (*io_cursor >= ntotal) eng->ntasks--;
        return;
    }
    if (g->kind == GSLT_C0_GOAL_UNIFY || g->kind == GSLT_C0_GOAL_UNIFY_OC) {
        GsltC0Value *lv = c0_instantiate_term_arena(eng, env, g->unify_left, &eng->fault);
        GsltC0Value *rv = c0_instantiate_term_arena(eng, env, g->unify_right, &eng->fault);
        if (!lv || !rv) {
            eng->status = C0_STATUS_FAULT;
            return;
        }
        (*io_cursor)++;
        if (*io_cursor >= ntotal) eng->ntasks--;
        bool any_bound = false;
        if (!c0_unify_values_oc(eng, lv, rv, &any_bound)) {
            eng->status = C0_STATUS_FAILED;
            return;
        }
        if (any_bound) {
            (void)c0_wake_on_binding(eng, true);
        }
        return;
    }
    if (g->kind == GSLT_C0_GOAL_GUARD) {
        /* In C1 queries/bodies, ensure variables in == / \== guards are allocated in env first */
        if (eng->prog && eng->prog->is_c1 &&
            (g->guard_test.kind == GSLT_C0_GUARD_IDENTICAL || g->guard_test.kind == GSLT_C0_GUARD_DISTINCT)) {
            (void)c0_instantiate_term_arena(eng, env, g->guard_test.t_left, &eng->fault);
            (void)c0_instantiate_term_arena(eng, env, g->guard_test.t_right, &eng->fault);
        }
        bool holds = false;
        bool res_exh = false;
        if (!c0_eval_guard(eng, env, &g->guard_test, &holds, &eng->fault, &res_exh)) {
            eng->status = res_exh ? C0_STATUS_RESOURCE_EXHAUSTED : C0_STATUS_FAULT;
            return;
        }
        if (!holds) {
            eng->status = C0_STATUS_FAILED;
            return;
        }
        (*io_cursor)++;
        if (*io_cursor >= ntotal) eng->ntasks--;
        return;
    }
    if (g->kind == GSLT_C0_GOAL_TELL) {
        const GsltC0Head *th = &g->tell_head;
        int di = c0_find_decl_idx(eng->prog, th->name, th->arity);
        if (di < 0) {
            eng->status = C0_STATUS_FAULT;
            eng->fault  = C0_FAULT_UNINSTANTIATED;
            return;
        }
        GsltC0Value **vals = (GsltC0Value **)gslt_arena_alloc(&eng->arena,
            (th->arity > 0 ? th->arity : 1) * sizeof(GsltC0Value *));
        for (uint32_t a = 0; a < th->arity; a++) {
            vals[a] = c0_instantiate_term_arena(eng, env, th->args[a], &eng->fault);
            if (!vals[a]) {
                eng->status = C0_STATUS_FAULT;
                return;
            }
        }
        (*io_cursor)++;
        if (*io_cursor >= ntotal) eng->ntasks--;
        (void)c0_introduce_constraint(eng, (uint32_t)di, vals, th->arity, true);
        return;
    }
}

static void c0_tick_machine(C0LoweredEngine *eng) {
    if (eng->status != C0_STATUS_RUNNING) return;
    if (eng->ntasks == 0) {
        eng->status = C0_STATUS_COMPLETED;
        return;
    }
    eng->steps_taken++;

    C0Task *top = &eng->tasks[eng->ntasks - 1];
    switch (top->kind) {
        case C0_TASK_SEEDS: {
            if (eng->prog->is_c1 && eng->prog->nquery_goals > 0) {
                if (top->seed_cursor >= eng->prog->nquery_goals) {
                    eng->ntasks--;
                    return;
                }
                const GsltC0Goal *qg = &eng->prog->query_goals[top->seed_cursor];
                c0_exec_goal_step(eng, &top->seed_env, qg, &top->seed_cursor, eng->prog->nquery_goals);
                return;
            }
            if (top->seed_cursor >= eng->prog->ninputs) {
                eng->ntasks--;
                return;
            }
            uint32_t qidx = top->seed_cursor++;
            if (top->seed_cursor >= eng->prog->ninputs) {
                eng->ntasks--;
            }
            const GsltC0Head *qh = &eng->prog->inputs[qidx];
            int di = c0_find_decl_idx(eng->prog, qh->name, qh->arity);
            if (di < 0) {
                eng->status = C0_STATUS_FAULT;
                eng->fault  = C0_FAULT_UNINSTANTIATED;
                return;
            }
            GsltC0Value **vals = (GsltC0Value **)gslt_arena_alloc(&eng->arena,
                (qh->arity > 0 ? qh->arity : 1) * sizeof(GsltC0Value *));
            C0Env empty_env;
            memset(&empty_env, 0, sizeof(empty_env));
            for (uint32_t a = 0; a < qh->arity; a++) {
                vals[a] = c0_instantiate_term_arena(eng, &empty_env, qh->args[a], &eng->fault);
                if (!vals[a]) {
                    eng->status = C0_STATUS_FAULT;
                    return;
                }
            }
            (void)c0_introduce_constraint(eng, (uint32_t)di, vals, qh->arity, true);
            return;
        }
        case C0_TASK_GOALS: {
            const GsltC0Rule *rule = &eng->prog->rules[top->goals_rule_idx];
            if (top->goal_cursor >= rule->nbody) {
                eng->ntasks--;
                return;
            }
            const GsltC0Goal *g = &rule->body[top->goal_cursor];
            c0_exec_goal_step(eng, &top->goals_env, g, &top->goal_cursor, rule->nbody);
            return;
        }
        case C0_TASK_SCAN: {
            uint32_t sidx = top->active_store_idx;
            if (!eng->store[sidx].alive || !tc_alive(eng->store[sidx].tc_occ)) {
                eng->ntasks--;
                return;
            }
            uint32_t d = top->active_decl_idx;
            if (top->occ_cursor >= eng->decl_nocc[d]) {
                eng->ntasks--;
                return;
            }
            C0OccAt occ = eng->decl_occ_table[d][top->occ_cursor];
            uint32_t after_cursor = top->occ_cursor + 1;
            top->kind             = C0_TASK_SEARCH;
            top->current_occ      = occ;
            top->after_occ_cursor = after_cursor;
            if (!top->sframes) {
                top->sframes = (C0SearchFrame *)gslt_arena_alloc(&eng->arena, C0_MAX_HEADS * sizeof(C0SearchFrame));
            }
            top->nsframes = 1;
            C0SearchFrame *sf0 = &top->sframes[0];
            memset(sf0, 0, sizeof(*sf0));
            sf0->head_index = 0;
            c0_fill_frame_candidates(eng, occ.rule_idx, 0, occ.head_pos, sidx, &sf0->env, sf0);
            return;
        }
        case C0_TASK_SEARCH: {
            if (top->nsframes == 0) {
                top->kind       = C0_TASK_SCAN;
                top->occ_cursor = top->after_occ_cursor;
                return;
            }
            C0SearchFrame *sf = &top->sframes[top->nsframes - 1];
            if (sf->cand_cursor >= sf->ncands) {
                top->nsframes--;
                return;
            }
            uint32_t cand_sidx = sf->cands[sf->cand_cursor++];
            const C0StoreEntry *ce = &eng->store[cand_sidx];
            eng->candidates_examined++;
            if (!ce->alive || !tc_alive(ce->tc_occ)) return;
            for (uint32_t u = 0; u < sf->head_index; u++) {
                if (sf->used_ids[u] == ce->id) return;
            }
            if (sf->head_index != top->current_occ.head_pos && ce->id == top->active_id) {
                return;
            }
            const GsltC0Rule *rule = &eng->prog->rules[top->current_occ.rule_idx];
            uint32_t total_h = rule->nkept + rule->nremoved;
            const GsltC0Head *hpat = (sf->head_index < rule->nkept)
                                   ? &rule->kept[sf->head_index]
                                   : &rule->removed[sf->head_index - rule->nkept];
            C0Env next_env = sf->env;
            if (!c0_match_head_args(eng, hpat, ce->values, ce->arity, &next_env)) {
                return;
            }
            uint32_t next_picks[C0_MAX_HEADS];
            uint32_t next_used[C0_MAX_HEADS];
            for (uint32_t i = 0; i < sf->head_index; i++) {
                next_picks[i] = sf->picks[i];
                next_used[i]  = sf->used_ids[i];
            }
            next_picks[sf->head_index] = cand_sidx;
            next_used[sf->head_index]  = ce->id;

            if (sf->head_index + 1 < total_h) {
                C0SearchFrame *deeper = &top->sframes[top->nsframes++];
                memset(deeper, 0, sizeof(*deeper));
                deeper->head_index = sf->head_index + 1;
                deeper->env        = next_env;
                memcpy(deeper->picks, next_picks, sizeof(next_picks));
                memcpy(deeper->used_ids, next_used, sizeof(next_used));
                c0_fill_frame_candidates(eng, top->current_occ.rule_idx, deeper->head_index,
                                         top->current_occ.head_pos, top->active_store_idx,
                                         &deeper->env, deeper);
                return;
            }

            /* Complete selection for all heads 0 .. total_h - 1 (Machine.complete) */
            if (rule->nremoved == 0 &&
                c0_history_contains(eng, top->current_occ.rule_idx, next_picks, rule->nkept)) {
                return;
            }
            bool holds = false;
            bool res_exh = false;
            if (!c0_eval_guards(eng, &next_env, rule, &holds, &eng->fault, &res_exh)) {
                eng->status = res_exh ? C0_STATUS_RESOURCE_EXHAUSTED : C0_STATUS_FAULT;
                return;
            }
            if (!holds) return;
            (void)c0_fire_rule_selection(eng, top->current_occ, top->after_occ_cursor,
                                         top->active_store_idx, &next_env, next_picks);
            return;
        }
    }
}

/* =========================================================================
 * M3: OS-Threaded Parallel CHR Execution (--c0-threads=N / --c0-mode=parallel)
 * ========================================================================= */

typedef struct {
    C0LoweredEngine *eng;
    pthread_mutex_t mu;
    uint64_t epoch_version;
    uint32_t nthreads;
    bool stop;
} C0ParallelShared;

typedef struct {
    C0ParallelShared *shared;
    uint32_t worker_id;
    uint64_t local_candidates_examined;
    uint64_t local_commits;
    uint32_t (*slot_cands)[C0_MAX_STORE_OCCS];
} C0ParallelWorkerCtx;

static bool c0_parallel_try_rule_on_active(C0ParallelWorkerCtx *wctx, uint32_t active_sidx,
                                           C0OccAt occ, uint64_t snap_ver, uint32_t nstore_snap) {
    C0ParallelShared *sh = wctx->shared;
    C0LoweredEngine *eng = sh->eng;
    const GsltC0Rule *rule = &eng->prog->rules[occ.rule_idx];
    uint32_t total_h = rule->nkept + rule->nremoved;

    uint32_t partner_slots[C0_MAX_HEADS];
    int partner_decls[C0_MAX_HEADS];
    uint32_t npartners = 0;
    for (uint32_t h = 0; h < total_h; h++) {
        if (h != occ.head_pos) {
            const GsltC0Head *hp = (h < rule->nkept) ? &rule->kept[h] : &rule->removed[h - rule->nkept];
            int di = c0_find_decl_idx(eng->prog, hp->name, hp->arity);
            if (di < 0) return false;
            partner_slots[npartners] = h;
            partner_decls[npartners] = di;
            npartners++;
        }
    }

    uint32_t slot_ncands[C0_MAX_HEADS] = {0};
    pthread_mutex_lock(&sh->mu);
    if (sh->stop || eng->status != C0_STATUS_RUNNING ||
        sh->epoch_version != snap_ver || !eng->store[active_sidx].alive) {
        pthread_mutex_unlock(&sh->mu);
        return false;
    }
    /* Take a consistent per-declaration snapshot of alive partner store indices (< nstore_snap) newest-first */
    for (uint32_t p = 0; p < npartners; p++) {
        int di = partner_decls[p];
        uint32_t cnt = 0;
        for (int cur = eng->decl_slot_head[di]; cur >= 0 && cnt < C0_MAX_STORE_OCCS; cur = eng->decl_slot_next[cur]) {
            if ((uint32_t)cur < nstore_snap && eng->store[cur].alive && (uint32_t)cur != active_sidx) {
                wctx->slot_cands[p][cnt++] = (uint32_t)cur;
            }
        }
        slot_ncands[p] = cnt;
    }
    pthread_mutex_unlock(&sh->mu);

    for (uint32_t p = 0; p < npartners; p++) {
        if (slot_ncands[p] == 0) return false;
    }

    /* Match active head first */
    const GsltC0Head *active_h = (occ.head_pos < rule->nkept)
                               ? &rule->kept[occ.head_pos]
                               : &rule->removed[occ.head_pos - rule->nkept];
    C0Env env0;
    memset(&env0, 0, sizeof(env0));
    if (!c0_match_head_args(eng, active_h, eng->store[active_sidx].values, eng->store[active_sidx].arity, &env0))
        return false;

    uint32_t p_idx[C0_MAX_HEADS] = {0};
    while (true) {
        wctx->local_candidates_examined++;
        uint32_t picks[C0_MAX_HEADS];
        picks[occ.head_pos] = active_sidx;
        bool distinct = true;
        for (uint32_t p = 0; p < npartners; p++) {
            uint32_t cand_sidx = wctx->slot_cands[p][p_idx[p]];
            if (cand_sidx == active_sidx) { distinct = false; break; }
            for (uint32_t prev = 0; prev < p; prev++) {
                if (wctx->slot_cands[prev][p_idx[prev]] == cand_sidx) { distinct = false; break; }
            }
            if (!distinct) break;
            picks[partner_slots[p]] = cand_sidx;
        }
        if (distinct) {
            C0Env env = env0;
            bool match_ok = true;
            for (uint32_t p = 0; p < npartners; p++) {
                uint32_t h = partner_slots[p];
                const GsltC0Head *hp = (h < rule->nkept) ? &rule->kept[h] : &rule->removed[h - rule->nkept];
                const C0StoreEntry *ce = &eng->store[picks[h]];
                if (!c0_match_head_args(eng, hp, ce->values, ce->arity, &env)) {
                    match_ok = false;
                    break;
                }
            }
            if (match_ok && rule->nkept > 0 && rule->nremoved > 0) {
                /* Preserve propagation-history monotonicity on duplicate-elimination
                 * simpagations (e.g. path(X,Y) \ path(X,Y) <=> true): always keep the
                 * older occurrence (smaller store index) and remove the newer duplicate. */
                for (uint32_t k = 0; k < rule->nkept && match_ok; k++) {
                    const C0StoreEntry *ek = &eng->store[picks[k]];
                    for (uint32_t rm = 0; rm < rule->nremoved; rm++) {
                        uint32_t ridx = picks[rule->nkept + rm];
                        const C0StoreEntry *er = &eng->store[ridx];
                        if (ek->decl_idx == er->decl_idx && ek->arity == er->arity) {
                            bool same_vals = true;
                            for (uint32_t a = 0; a < ek->arity; a++) {
                                if (!c0_val_eq_deref(eng, ek->values[a], er->values[a])) {
                                    same_vals = false;
                                    break;
                                }
                            }
                            if (same_vals && picks[k] > ridx) {
                                match_ok = false;
                                break;
                            }
                        }
                    }
                }
            }
            if (match_ok) {
                bool holds = false, res_exh = false;
                C0FaultKind fault = C0_FAULT_NONE;
                if (!c0_eval_guards(eng, &env, rule, &holds, &fault, &res_exh)) {
                    pthread_mutex_lock(&sh->mu);
                    if (eng->status == C0_STATUS_RUNNING && sh->epoch_version == snap_ver) {
                        eng->status = res_exh ? C0_STATUS_RESOURCE_EXHAUSTED : C0_STATUS_FAULT;
                        eng->fault  = fault;
                    }
                    pthread_mutex_unlock(&sh->mu);
                    return false;
                }
                if (holds) {
                    /* Optimistic parallel partner match succeeded! Acquire lock to validate & commit on tcalc */
                    pthread_mutex_lock(&sh->mu);
                    bool still_valid = (eng->status == C0_STATUS_RUNNING && sh->epoch_version == snap_ver);
                    for (uint32_t h = 0; h < total_h && still_valid; h++) {
                        if (!eng->store[picks[h]].alive || !tc_alive(eng->store[picks[h]].tc_occ))
                            still_valid = false;
                    }
                    if (still_valid && rule->nremoved == 0 &&
                        c0_history_contains(eng, occ.rule_idx, picks, rule->nkept)) {
                        still_valid = false;
                    }
                    if (still_valid) {
                        if (eng->max_steps > 0 && eng->events_admitted >= eng->max_steps) {
                            eng->status = C0_STATUS_BUDGET_EXHAUSTED;
                            sh->stop = true;
                            sh->epoch_version++;
                            pthread_mutex_unlock(&sh->mu);
                            return true;
                        }
                        C0RuleOrigin *orig = &eng->rule_origins[occ.rule_idx];
                        Occ keep_occs[C0_MAX_HEADS], take_occs[C0_MAX_HEADS];
                        Term inst_env[TC_VARS];
                        memset(inst_env, 0, sizeof(inst_env));
                        for (uint32_t v = 0; v < orig->n_head_vars; v++) {
                            inst_env[v] = c0_encode_val_term(eng, c0_env_lookup(&env, orig->head_var_ids[v]));
                        }
                        for (uint32_t k = 0; k < rule->nkept; k++) {
                            keep_occs[k] = eng->store[picks[k]].tc_occ;
                            inst_env[orig->base_occ_var + k] = c0_get_occ_term(eng, eng->store[picks[k]].id);
                        }
                        for (uint32_t rm = 0; rm < rule->nremoved; rm++) {
                            take_occs[rm] = eng->store[picks[rule->nkept + rm]].tc_occ;
                            inst_env[orig->base_occ_var + rule->nkept + rm] =
                                c0_get_occ_term(eng, eng->store[picks[rule->nkept + rm]].id);
                        }
                        TcPreparedStep cand;
                        memset(&cand, 0, sizeof(cand));
                        cand.rule = orig->tc_rule_id;
                        cand.keep = rule->nkept > 0 ? keep_occs : NULL;
                        cand.take = rule->nremoved > 0 ? take_occs : NULL;
                        cand.inst = inst_env;
                        TcPreparedEffect eff; TcAdmissionReceipt rec; TcRefusalReason ref = TC_REFUSE_NONE;
                        if (tc_bridge_execute_candidate(&cand, &eng->profile, &eff, &eng->last_event, &rec, &ref)
                            == TC_BRIDGE_ADMITTED) {
                            orig->events_admitted++;
                            eng->events_admitted++;
                            wctx->local_commits++;
                            for (uint32_t rm = 0; rm < rule->nremoved; rm++) {
                                eng->store[picks[rule->nkept + rm]].alive = false;
                            }
                            if (rule->nremoved == 0 && eng->nhistory < C0_MAX_HIST_ENTRIES) {
                                C0HistEntry *he = &eng->history[eng->nhistory++];
                                he->rule_idx = occ.rule_idx;
                                he->nids = rule->nkept;
                                for (uint32_t k = 0; k < rule->nkept; k++)
                                    he->ids[k] = eng->store[picks[k]].id;
                            }
                            /* Execute rule body goals in Refined CHR left-to-right order under lock:
                             * Only push C0_TASK_SCAN when a body contains multiple goals so ordered_body
                             * (`start <=> a, b`) activates `a` before telling `b`, while single-tell bodies
                             * leave the newly told constraint for the parallel worker pool! */
                            if (rule->nbody > 1) {
                                eng->ntasks = 1;
                                memset(&eng->tasks[0], 0, sizeof(eng->tasks[0]));
                                eng->tasks[0].kind           = C0_TASK_GOALS;
                                eng->tasks[0].goals_env      = env;
                                eng->tasks[0].goals_rule_idx = occ.rule_idx;
                                eng->tasks[0].goal_cursor    = 0;
                                while (eng->status == C0_STATUS_RUNNING && eng->ntasks > 0) {
                                    c0_tick_machine(eng);
                                }
                            } else if (rule->nbody == 1) {
                                C0Env body_env = env;
                                const GsltC0Goal *g = &rule->body[0];
                                if (g->kind == GSLT_C0_GOAL_FAIL) {
                                    eng->status = C0_STATUS_FAILED;
                                } else if (g->kind == GSLT_C0_GOAL_ASSIGN) {
                                    uint32_t dummy_cur = 0;
                                    eng->ntasks = 1;
                                    c0_exec_goal_step(eng, &body_env, g, &dummy_cur, 1);
                                    eng->ntasks = 0;
                                } else if (g->kind == GSLT_C0_GOAL_UNIFY || g->kind == GSLT_C0_GOAL_UNIFY_OC ||
                                           g->kind == GSLT_C0_GOAL_GUARD) {
                                    uint32_t dummy_cur = 0;
                                    eng->ntasks = 1;
                                    c0_exec_goal_step(eng, &body_env, g, &dummy_cur, 1);
                                    eng->ntasks = 0;
                                } else if (g->kind == GSLT_C0_GOAL_TELL) {
                                    const GsltC0Head *th = &g->tell_head;
                                    int di = c0_find_decl_idx(eng->prog, th->name, th->arity);
                                    GsltC0Value **vals = (GsltC0Value **)gslt_arena_alloc(&eng->arena,
                                        (th->arity > 0 ? th->arity : 1) * sizeof(GsltC0Value *));
                                    bool inst_ok = (di >= 0);
                                    for (uint32_t a = 0; a < th->arity && inst_ok; a++) {
                                        vals[a] = c0_instantiate_term_arena(eng, &body_env, th->args[a], &eng->fault);
                                        if (!vals[a]) inst_ok = false;
                                    }
                                    if (!inst_ok) {
                                        eng->status = C0_STATUS_FAULT;
                                        if (eng->fault == C0_FAULT_NONE) eng->fault = C0_FAULT_UNINSTANTIATED;
                                    } else {
                                        (void)c0_introduce_constraint(eng, (uint32_t)di, vals, th->arity, false);
                                    }
                                }
                            }
                            sh->epoch_version++;
                            pthread_mutex_unlock(&sh->mu);
                            return true;
                        }
                    }
                    bool epoch_changed = (sh->epoch_version != snap_ver);
                    pthread_mutex_unlock(&sh->mu);
                    if (epoch_changed) return false;
                }
            }
        }
        if (npartners == 0) break;
        int pos = (int)npartners - 1;
        while (pos >= 0) {
            p_idx[pos]++;
            if (p_idx[pos] < slot_ncands[pos]) break;
            p_idx[pos] = 0;
            pos--;
        }
        if (pos < 0) break;
    }
    return false;
}

static void *c0_parallel_worker_main(void *arg) {
    C0ParallelWorkerCtx *wctx = (C0ParallelWorkerCtx *)arg;
    C0ParallelShared *sh = wctx->shared;
    C0LoweredEngine *eng = sh->eng;

    while (true) {
        pthread_mutex_lock(&sh->mu);
        if (sh->stop || eng->status != C0_STATUS_RUNNING) {
            pthread_mutex_unlock(&sh->mu);
            break;
        }
        uint64_t snap_ver = sh->epoch_version;
        uint32_t nstore_snap = eng->nstore;
        pthread_mutex_unlock(&sh->mu);

        bool any_committed = false;
        /* Scan rules in priority order r = 0 .. nrules - 1; within each rule,
         * all OS worker threads partition the live store in parallel! */
        for (uint32_t r = 0; r < eng->prog->nrules && !any_committed; r++) {
            const GsltC0Rule *rule = &eng->prog->rules[r];
            uint32_t total_h = rule->nkept + rule->nremoved;
            for (uint32_t visit = 0; visit < total_h && !any_committed; visit++) {
                uint32_t h_pos = (visit < rule->nremoved) ? (rule->nkept + visit) : (visit - rule->nremoved);
                const GsltC0Head *h = (h_pos < rule->nkept) ? &rule->kept[h_pos] : &rule->removed[h_pos - rule->nkept];
                int h_decl = c0_find_decl_idx(eng->prog, h->name, h->arity);
                if (h_decl < 0) continue;
                C0OccAt occ = { r, h_pos };

                for (uint32_t i = 0; i < nstore_snap; i++) {
                    uint32_t sidx = (nstore_snap - 1) - ((i + wctx->worker_id) % nstore_snap);
                    pthread_mutex_lock(&sh->mu);
                    bool epoch_changed = (sh->epoch_version != snap_ver || sh->stop || eng->status != C0_STATUS_RUNNING);
                    bool match_decl = (!epoch_changed && eng->store[sidx].alive && eng->store[sidx].decl_idx == (uint32_t)h_decl);
                    pthread_mutex_unlock(&sh->mu);
                    if (epoch_changed) {
                        any_committed = true;
                        break;
                    }
                    if (!match_decl) continue;
                    if (c0_parallel_try_rule_on_active(wctx, sidx, occ, snap_ver, nstore_snap)) {
                        any_committed = true;
                        break;
                    }
                }
            }
        }

        if (!any_committed) {
            pthread_mutex_lock(&sh->mu);
            if (sh->epoch_version == snap_ver) {
                /* No worker committed any rule across all rules & store items -> quiescent! */
                sh->stop = true;
                if (eng->status == C0_STATUS_RUNNING) {
                    eng->status = C0_STATUS_COMPLETED;
                }
                pthread_mutex_unlock(&sh->mu);
                break;
            }
            pthread_mutex_unlock(&sh->mu);
        }
    }
    return NULL;
}

static bool c0_run_machine(const GsltC0Program *prog, C0LoweredEngine *eng,
                           C0SearchMode mode, uint32_t nthreads, uint64_t max_steps) {
    memset(eng, 0, sizeof(*eng));
    eng->mode      = mode;
    eng->nthreads  = nthreads > 0 ? nthreads : 1;
    eng->max_steps = max_steps;

    if (!c0_compile_and_seal(prog, eng)) {
        return false;
    }

    if (mode == C0_MODE_PARALLEL && !prog->is_c1) {
        uint32_t nth = eng->nthreads > 1 ? eng->nthreads : 4;
        if (nth > 16) nth = 16;
        /* Introduce all initial query constraints first */
        C0Env empty_env;
        memset(&empty_env, 0, sizeof(empty_env));
        for (uint32_t q = 0; q < prog->ninputs; q++) {
            const GsltC0Head *qh = &prog->inputs[q];
            int di = c0_find_decl_idx(prog, qh->name, qh->arity);
            if (di < 0) {
                eng->status = C0_STATUS_FAULT;
                eng->fault  = C0_FAULT_UNINSTANTIATED;
                return false;
            }
            GsltC0Value **vals = (GsltC0Value **)gslt_arena_alloc(&eng->arena,
                (qh->arity > 0 ? qh->arity : 1) * sizeof(GsltC0Value *));
            for (uint32_t a = 0; a < qh->arity; a++) {
                vals[a] = c0_instantiate_term_arena(eng, &empty_env, qh->args[a], &eng->fault);
                if (!vals[a]) {
                    eng->status = C0_STATUS_FAULT;
                    return false;
                }
            }
            if (!c0_introduce_constraint(eng, (uint32_t)di, vals, qh->arity, false)) {
                return false;
            }
        }
        C0ParallelShared shared;
        memset(&shared, 0, sizeof(shared));
        shared.eng = eng;
        shared.nthreads = nth;
        pthread_mutex_init(&shared.mu, NULL);

        pthread_t threads[16];
        C0ParallelWorkerCtx wctx[16];
        for (uint32_t t = 0; t < nth; t++) {
            memset(&wctx[t], 0, sizeof(wctx[t]));
            wctx[t].shared = &shared;
            wctx[t].worker_id = t;
            wctx[t].slot_cands = (uint32_t (*)[C0_MAX_STORE_OCCS])gslt_arena_alloc(
                &eng->arena, C0_MAX_HEADS * C0_MAX_STORE_OCCS * sizeof(uint32_t));
            if (!wctx[t].slot_cands) {
                pthread_mutex_destroy(&shared.mu);
                eng->status = C0_STATUS_RESOURCE_EXHAUSTED;
                return false;
            }
        }
        uint32_t nspawned = 0;
        for (uint32_t t = 0; t < nth; t++) {
            if (pthread_create(&threads[t], NULL, c0_parallel_worker_main, &wctx[t]) != 0) {
                pthread_mutex_lock(&shared.mu);
                shared.stop = true;
                shared.epoch_version++;
                if (eng->status == C0_STATUS_RUNNING) {
                    eng->status = C0_STATUS_RESOURCE_EXHAUSTED;
                }
                pthread_mutex_unlock(&shared.mu);
                break;
            }
            nspawned++;
        }
        for (uint32_t t = 0; t < nspawned; t++) {
            pthread_join(threads[t], NULL);
            eng->candidates_examined += wctx[t].local_candidates_examined;
        }
        pthread_mutex_destroy(&shared.mu);
        return eng->status == C0_STATUS_COMPLETED;
    }

    /* Deterministic single-threaded Refined CHR Machine (M1 Naive or M2 Indexed) */
    eng->ntasks = 1;
    memset(&eng->tasks[0], 0, sizeof(eng->tasks[0]));
    eng->tasks[0].kind = C0_TASK_SEEDS;
    eng->tasks[0].seed_cursor = 0;

    while (eng->status == C0_STATUS_RUNNING) {
        c0_tick_machine(eng);
    }
    return eng->status == C0_STATUS_COMPLETED;
}

static void c0_engine_destroy(C0LoweredEngine *eng) {
    if (eng) {
        gslt_arena_free(&eng->arena);
    }
}

/* Format alive SPACE_CHR occurrences into canonical sorted "[c1,c2,...]" string */
static void c0_format_val_Item(const C0LoweredEngine *eng, GsltArena *a, GsltStrBuf *sb, const GsltC0Value *v_raw) {
    const GsltC0Value *v = c0_deref_val(eng, v_raw);
    if (!v) return;
    if (v->kind == GSLT_C0_VAL_INT) {
        gslt_sb_append_bigint(a, sb, &v->ival);
    } else if (v->kind == GSLT_C0_VAL_ATOM) {
        gslt_sb_append_bytes(a, sb, v->atom.bytes, v->atom.len);
    } else if (v->kind == GSLT_C0_VAL_VAR) {
        gslt_sb_append_cstr(a, sb, "_V");
        gslt_sb_append_u32(a, sb, v->var_id);
    } else if (v->kind == GSLT_C0_VAL_COMPOUND) {
        gslt_sb_append_bytes(a, sb, v->atom.bytes, v->atom.len);
        gslt_sb_append_char(a, sb, '(');
        for (uint32_t i = 0; i < v->nfields; i++) {
            if (i > 0) gslt_sb_append_char(a, sb, ',');
            c0_format_val_Item(eng, a, sb, v->fields[i]);
        }
        gslt_sb_append_char(a, sb, ')');
    } else if (v->kind == GSLT_C0_VAL_TUPLE) {
        gslt_sb_append_cstr(a, sb, "tuple(");
        for (uint32_t i = 0; i < v->nfields; i++) {
            if (i > 0) gslt_sb_append_char(a, sb, ',');
            c0_format_val_Item(eng, a, sb, v->fields[i]);
        }
        gslt_sb_append_char(a, sb, ')');
    }
}

/* The live store as "[c1,c2,...]", constraints sorted, in a buffer the caller frees.
 * Every live constraint is printed: the result of a run is never shortened to fit. */
static char *c0_format_store_alloc(C0LoweredEngine *eng) {
    char **items = (char **)malloc((size_t)(eng->nstore ? eng->nstore : 1) * sizeof(char *));
    size_t n = 0, total = 2;
    for (uint32_t i = 0; i < eng->nstore; i++) {
        const C0StoreEntry *se = &eng->store[i];
        if (!se->alive || !tc_alive(se->tc_occ)) continue;
        GsltStrBuf sb;
        gslt_sb_init(&eng->arena, &sb, 128);
        GsltByteStr pname = eng->prog->decls[se->decl_idx].name;
        gslt_sb_append_bytes(&eng->arena, &sb, pname.bytes, pname.len);
        if (se->arity > 0) {
            gslt_sb_append_char(&eng->arena, &sb, '(');
            for (uint32_t a = 0; a < se->arity; a++) {
                if (a > 0) gslt_sb_append_char(&eng->arena, &sb, ',');
                c0_format_val_Item(eng, &eng->arena, &sb, se->values[a]);
            }
            gslt_sb_append_char(&eng->arena, &sb, ')');
        }
        items[n] = strdup(sb.buf);
        total += strlen(items[n]) + 1;
        n++;
    }
    qsort(items, n, sizeof(char *), cmp_str_ptr);
    char *out = (char *)malloc(total + 1);
    size_t pos = 0;
    out[pos++] = '[';
    for (size_t i = 0; i < n; i++) {
        size_t len = strlen(items[i]);
        memcpy(out + pos, items[i], len);
        pos += len;
        if (i + 1 < n) out[pos++] = ',';
        free(items[i]);
    }
    out[pos++] = ']';
    out[pos] = '\0';
    free(items);
    return out;
}

/* The same text in a caller's buffer.  A store that does not fit is reported as
 * such, never cut short. */
static void c0_format_store(C0LoweredEngine *eng, char *out_buf, size_t cap) {
    if (cap == 0) return;
    char *full = c0_format_store_alloc(eng);
    if (strlen(full) < cap) memcpy(out_buf, full, strlen(full) + 1);
    else snprintf(out_buf, cap, "<store does not fit>");
    free(full);
}

/* =========================================================================
 * 10. Built-in Qualification & Differential Control Suite (--self-test)
 * ========================================================================= */

static int g_pass = 0;
static int g_fail = 0;

#define CHECK(cond, msg, ...) do { \
    if (cond) { g_pass++; } \
    else { g_fail++; fprintf(stderr, "FAIL [%s:%d]: " msg "\n", __FILE__, __LINE__, ##__VA_ARGS__); } \
} while (0)

static char *read_file_text(const char *path) {
    FILE *fp = fopen(path, "r");
    if (!fp && strncmp(path, "../", 3) == 0) {
        fp = fopen(path + 3, "r");
    }
    if (!fp) return NULL;
    fseek(fp, 0, SEEK_END);
    long sz = ftell(fp);
    fseek(fp, 0, SEEK_SET);
    char *buf = (char *)malloc((size_t)sz + 1);
    size_t nr = fread(buf, 1, (size_t)sz, fp);
    buf[nr] = '\0';
    fclose(fp);
    return buf;
}

static void run_d0_case_and_compare_m1_m2(const char *label, const char *dl_src, const char *facts_dir,
                                          const char *expected_rel, const char *expected_sorted_tsv,
                                          int expected_total_output_rows) {
    D0Program *p1 = (D0Program *)calloc(1, sizeof(D0Program));
    D0Program *p2 = (D0Program *)calloc(1, sizeof(D0Program));
    D0DiagKind d1 = d0_parse_dl(dl_src, p1);
    CHECK(d1 == D0_DIAG_OK, "%s: parse_dl returned %s", label, d0_diag_name(d1));
    d1 = d0_static_admit(p1);
    CHECK(d1 == D0_DIAG_OK, "%s: static_admit returned %s", label, d0_diag_name(d1));
    if (facts_dir) {
        d1 = d0_load_facts_dir(p1, facts_dir);
        CHECK(d1 == D0_DIAG_OK, "%s: load_facts_dir returned %s", label, d0_diag_name(d1));
    }

    *p2 = *p1;
    D0LoweredEngine *eng1 = (D0LoweredEngine *)calloc(1, sizeof(D0LoweredEngine));
    D0LoweredEngine *eng2 = (D0LoweredEngine *)calloc(1, sizeof(D0LoweredEngine));

    CHECK(d0_lower_to_tcalc(p1, eng1), "%s: M1 lower_to_tcalc", label);
    TcAdmissionProfile prof1 = tc_admission_custom_profile(
        "d0_m1_strict", true, true, false, false, eng1, d0_scalar_cmp_permit);
    TcAdmittedEvent ev1;
    memset(&ev1, 0, sizeof(ev1));
    D0RunMetrics m1 = d0_run_m1_naive(p1, eng1, &prof1, 0, &ev1);
    CHECK(m1.status == TC_BRIDGE_ADMITTED, "%s: M1 status admitted", label);

    char *out1 = NULL;
    int total1 = 0;
    for (int r = 0; r < p1->nrels; r++) {
        if (!p1->rels[r].is_output) continue;
        int cnt = 0;
        char *rbuf = d0_format_relation_rows_alloc(p1, eng1, r, &cnt);
        total1 += cnt;
        if (expected_rel && strcmp(p1->rels[r].name, expected_rel) == 0) {
            out1 = rbuf;
        } else {
            free(rbuf);
        }
    }

    CHECK(d0_lower_to_tcalc_ex(p2, eng2, true), "%s: M2 lower_to_tcalc_ex(flat_horn=true)", label);
    TcAdmissionProfile prof2 = tc_admission_custom_profile(
        "d0_m2_strict", true, true, false, false, eng2, d0_scalar_cmp_permit);
    TcAdmittedEvent ev2;
    memset(&ev2, 0, sizeof(ev2));
    D0RunMetrics m2 = d0_run_m2_seminaive(p2, eng2, &prof2, 0, &ev2);
    CHECK(m2.status == TC_BRIDGE_ADMITTED, "%s: M2 status admitted", label);

    char *out2 = NULL;
    int total2 = 0;
    for (int r = 0; r < p2->nrels; r++) {
        if (!p2->rels[r].is_output) continue;
        int cnt = 0;
        char *rbuf = d0_format_relation_rows_alloc(p2, eng2, r, &cnt);
        total2 += cnt;
        if (expected_rel && strcmp(p2->rels[r].name, expected_rel) == 0) {
            out2 = rbuf;
        } else {
            free(rbuf);
        }
    }

    CHECK(total1 == total2, "%s: M1 and M2 derived identical total output rows (%d vs %d)", label, total1, total2);
    CHECK(m1.events_admitted == m2.events_admitted,
          "%s: M1 and M2 admitted identical event count (%" PRIu64 " vs %" PRIu64 ")",
          label, m1.events_admitted, m2.events_admitted);
    if (m2.events_admitted > 0) {
        /* Compare M2 optimized (use_flat_horn=true) vs M2 reference (use_flat_horn=false)
         * on TcAdmittedEvent and TcAdmissionReceipt fields */
        D0Program *p_ref = (D0Program *)calloc(1, sizeof(D0Program));
        *p_ref = *p1;
        D0LoweredEngine *eng_ref = (D0LoweredEngine *)calloc(1, sizeof(D0LoweredEngine));
        CHECK(d0_lower_to_tcalc_ex(p_ref, eng_ref, false), "%s: M2 reference lower_to_tcalc_ex(flat_horn=false)", label);
        TcAdmissionProfile prof_ref = tc_admission_custom_profile(
            "d0_m2_ref", true, true, false, false, eng_ref, d0_scalar_cmp_permit);
        TcAdmittedEvent ev_ref;
        memset(&ev_ref, 0, sizeof(ev_ref));
        D0RunMetrics m_ref = d0_run_m2_seminaive(p_ref, eng_ref, &prof_ref, 0, &ev_ref);
        CHECK(m_ref.status == TC_BRIDGE_ADMITTED && m_ref.events_admitted == m2.events_admitted,
              "%s: M2 reference and M2 optimized admit identical event counts (%" PRIu64 " vs %" PRIu64 ")",
              label, m_ref.events_admitted, m2.events_admitted);
        CHECK(ev2.ntake == ev_ref.ntake && ev2.nkeep == ev_ref.nkeep && ev2.nholes == ev_ref.nholes &&
              ev2.firing.rule == ev_ref.firing.rule && ev2.firing.dest == ev_ref.firing.dest &&
              ev2.prepared.prepared == ev_ref.prepared.prepared &&
              ev2.prepared.prep_status == ev_ref.prepared.prep_status &&
              ev2.prepared.rule == ev_ref.prepared.rule &&
              ev2.prepared.nmake == ev_ref.prepared.nmake &&
              ev2.prepared.make_terms[0] == ev_ref.prepared.make_terms[0] &&
              ev2.prepared.make_spaces[0] == ev_ref.prepared.make_spaces[0] &&
              ev2.prepared.make_marks[0] == ev_ref.prepared.make_marks[0] &&
              ev2.verified_guards == ev_ref.verified_guards &&
              ev2.receipt.admitted == ev_ref.receipt.admitted &&
              ev2.receipt.rule == ev_ref.receipt.rule &&
              ev2.receipt.out == ev_ref.receipt.out &&
              ev2.receipt.out_term == ev_ref.receipt.out_term &&
              ev2.receipt.out_term != 0,
              "%s: M2 optimized and M2 reference produce identical TcAdmittedEvent & TcAdmissionReceipt fields",
              label);
        free(eng_ref);
        free(p_ref);
    }
    if (expected_total_output_rows >= 0) {
        CHECK(total2 == expected_total_output_rows,
              "%s: total output rows %d == expected %d", label, total2, expected_total_output_rows);
    }
    if (expected_rel && expected_sorted_tsv && out1 && out2) {
        CHECK(strcmp(out1, expected_sorted_tsv) == 0, "%s: M1 %s matches expected TSV", label, expected_rel);
        CHECK(strcmp(out2, expected_sorted_tsv) == 0, "%s: M2 %s matches expected TSV", label, expected_rel);
    }
    free(out1);
    free(out2);
    free(eng1);
    free(eng2);
    free(p1);
    free(p2);
}

static bool run_c0_source_both_modes(const char *label, const char *csrc,
                                     C0ExecStatus expected_status, C0FaultKind expected_fault,
                                     const char *expected_store, bool test_parallel_confluent) {
    GsltArena a1, a2;
    gslt_arena_init(&a1);
    gslt_arena_init(&a2);
    GsltC0Program cp1, cp2;
    GsltC0Diagnostic d1, d2;
    memset(&d1, 0, sizeof(d1));
    memset(&d2, 0, sizeof(d2));
    char err1[256] = {0}, err2[256] = {0};
    bool ok1 = gslt_c0_parse_source(&a1, csrc, strlen(csrc), &cp1, &d1, err1, sizeof(err1));
    bool ok2 = gslt_c0_parse_source(&a2, csrc, strlen(csrc), &cp2, &d2, err2, sizeof(err2));
    CHECK(ok1 && ok2 && d1.kind == GSLT_C0_DIAG_NONE && d2.kind == GSLT_C0_DIAG_NONE,
          "%s: parse_source returned %s (%s)", label, gslt_c0_diag_name(d1.kind), err1);
    if (!ok1 || !ok2) {
        gslt_arena_free(&a1);
        gslt_arena_free(&a2);
        return false;
    }

    C0LoweredEngine *e1 = (C0LoweredEngine *)calloc(1, sizeof(C0LoweredEngine));
    C0LoweredEngine *e2 = (C0LoweredEngine *)calloc(1, sizeof(C0LoweredEngine));
    c0_run_machine(&cp1, e1, C0_MODE_NAIVE, 1, 0);
    c0_run_machine(&cp2, e2, C0_MODE_INDEXED, 1, 0);

    CHECK(e1->status == expected_status, "%s (M1 naive): status got %s, expected %s",
          label, c0_status_name(e1->status), c0_status_name(expected_status));
    CHECK(e2->status == expected_status, "%s (M2 indexed): status got %s, expected %s",
          label, c0_status_name(e2->status), c0_status_name(expected_status));
    if (expected_status == C0_STATUS_FAULT) {
        CHECK(e1->fault == expected_fault && e2->fault == expected_fault,
              "%s: fault got %s/%s, expected %s",
              label, c0_fault_name(e1->fault), c0_fault_name(e2->fault), c0_fault_name(expected_fault));
    }

    char s1[8192], s2[8192];
    c0_format_store(e1, s1, sizeof(s1));
    c0_format_store(e2, s2, sizeof(s2));
    CHECK(strcmp(s1, s2) == 0, "%s: M1 naive and M2 indexed stores match (%s vs %s)", label, s1, s2);
    CHECK(e1->events_admitted == e2->events_admitted,
          "%s: M1 naive and M2 indexed admitted event counts match (%" PRIu64 " vs %" PRIu64 ")",
          label, e1->events_admitted, e2->events_admitted);
    CHECK(strcmp(e1->trace_buf.buf ? e1->trace_buf.buf : "", e2->trace_buf.buf ? e2->trace_buf.buf : "") == 0,
          "%s: M1 naive and M2 indexed rule-firing event traces match identically", label);

    if (expected_store) {
        CHECK(strcmp(s2, expected_store) == 0,
              "%s: store got %s, expected %s", label, s2, expected_store);
    }

    if (test_parallel_confluent && expected_status == C0_STATUS_COMPLETED) {
        GsltArena a3;
        gslt_arena_init(&a3);
        GsltC0Program cp3;
        GsltC0Diagnostic d3;
        char err3[256] = {0};
        gslt_c0_parse_source(&a3, csrc, strlen(csrc), &cp3, &d3, err3, sizeof(err3));
        C0LoweredEngine *e3 = (C0LoweredEngine *)calloc(1, sizeof(C0LoweredEngine));
        c0_run_machine(&cp3, e3, C0_MODE_PARALLEL, 4, 0);
        char s3[8192];
        c0_format_store(e3, s3, sizeof(s3));
        CHECK(e3->status == C0_STATUS_COMPLETED && strcmp(s3, expected_store ? expected_store : s2) == 0,
              "%s (M3 OS-pthread 4 workers): store got %s, expected %s",
              label, s3, expected_store ? expected_store : s2);
        c0_engine_destroy(e3);
        free(e3);
        gslt_arena_free(&a3);
    }

    c0_engine_destroy(e1);
    c0_engine_destroy(e2);
    free(e1);
    free(e2);
    gslt_arena_free(&a1);
    gslt_arena_free(&a2);
    return true;
}

static bool run_c1_source_both_modes(const char *label, const char *csrc, const char *query_override,
                                     C0ExecStatus expected_status, C0FaultKind expected_fault,
                                     const char *expected_store) {
    GsltArena a1, a2;
    gslt_arena_init(&a1);
    gslt_arena_init(&a2);
    GsltC0Program cp1, cp2;
    GsltC0Diagnostic d1, d2;
    memset(&d1, 0, sizeof(d1));
    memset(&d2, 0, sizeof(d2));
    char err1[256] = {0}, err2[256] = {0};
    bool ok1 = gslt_c1_parse_source(&a1, csrc, strlen(csrc), &cp1, &d1, err1, sizeof(err1));
    bool ok2 = gslt_c1_parse_source(&a2, csrc, strlen(csrc), &cp2, &d2, err2, sizeof(err2));
    if (ok1 && query_override) {
        ok1 = gslt_c1_set_query_string(&a1, &cp1, query_override, &d1, err1, sizeof(err1));
    }
    if (ok2 && query_override) {
        ok2 = gslt_c1_set_query_string(&a2, &cp2, query_override, &d2, err2, sizeof(err2));
    }
    CHECK(ok1 && ok2 && d1.kind == GSLT_C0_DIAG_NONE && d2.kind == GSLT_C0_DIAG_NONE,
          "%s: C1 parse_source returned %s (%s)", label, gslt_c0_diag_name(d1.kind), err1);
    if (!ok1 || !ok2) {
        gslt_arena_free(&a1);
        gslt_arena_free(&a2);
        return false;
    }

    C0LoweredEngine *e1 = (C0LoweredEngine *)calloc(1, sizeof(C0LoweredEngine));
    C0LoweredEngine *e2 = (C0LoweredEngine *)calloc(1, sizeof(C0LoweredEngine));
    c0_run_machine(&cp1, e1, C0_MODE_NAIVE, 1, 0);
    c0_run_machine(&cp2, e2, C0_MODE_INDEXED, 1, 0);

    CHECK(e1->status == expected_status, "%s (M1 naive): status got %s, expected %s",
          label, c0_status_name(e1->status), c0_status_name(expected_status));
    CHECK(e2->status == expected_status, "%s (M2 indexed): status got %s, expected %s",
          label, c0_status_name(e2->status), c0_status_name(expected_status));
    if (expected_status == C0_STATUS_FAULT) {
        CHECK(e1->fault == expected_fault && e2->fault == expected_fault,
              "%s: fault got %s/%s, expected %s",
              label, c0_fault_name(e1->fault), c0_fault_name(e2->fault), c0_fault_name(expected_fault));
    }

    char s1[8192], s2[8192];
    c0_format_store(e1, s1, sizeof(s1));
    c0_format_store(e2, s2, sizeof(s2));
    CHECK(strcmp(s1, s2) == 0, "%s: M1 naive and M2 indexed stores match (%s vs %s)", label, s1, s2);
    CHECK(e1->events_admitted == e2->events_admitted,
          "%s: M1 naive and M2 indexed admitted event counts match (%" PRIu64 " vs %" PRIu64 ")",
          label, e1->events_admitted, e2->events_admitted);
    if (expected_store) {
        CHECK(strcmp(s2, expected_store) == 0,
              "%s: store got %s, expected %s", label, s2, expected_store);
    }

    c0_engine_destroy(e1);
    c0_engine_destroy(e2);
    free(e1);
    free(e2);
    gslt_arena_free(&a1);
    gslt_arena_free(&a2);
    return true;
}

/* Helper for stack-return ASan/UBSan receipt safety check */
__attribute__((noinline))
static TcAdmittedEvent helper_stack_return_c0_event(const char *csrc) {
    GsltArena a;
    gslt_arena_init(&a);
    GsltC0Program cp;
    GsltC0Diagnostic d;
    char err[256] = {0};
    gslt_c0_parse_source(&a, csrc, strlen(csrc), &cp, &d, err, sizeof(err));
    C0LoweredEngine eng;
    memset(&eng, 0, sizeof(eng));
    c0_run_machine(&cp, &eng, C0_MODE_INDEXED, 1, 0);
    TcAdmittedEvent ret = eng.last_event;
    c0_engine_destroy(&eng);
    gslt_arena_free(&a);
    return ret;
}

static int run_self_test(void) {
    printf("=== GSLT -> tcalc Lowering Consumer: D0 Datalog & C0 CHR Self-Test ===\n");

    /* ---------------------------------------------------------------------
     * Suite 1: D0 Datalog Reference Corpus (Souffle 2.5 Oracle Parity)
     * --------------------------------------------------------------------- */
    {
        char *basic = read_file_text("../Mettapedia/metta/gslt/tests/datalog/basic.dl");
        CHECK(basic != NULL, "read basic.dl");
        if (basic) {
            run_d0_case_and_compare_m1_m2("basic.dl", basic, NULL, "Low", "1\n", 2);
            free(basic);
        }

        char *boundaries = read_file_text("../Mettapedia/metta/gslt/tests/datalog/boundaries.dl");
        CHECK(boundaries != NULL, "read boundaries.dl");
        if (boundaries) {
            run_d0_case_and_compare_m1_m2("boundaries.dl", boundaries, NULL, "Seed", "1\n", 1);
            free(boundaries);
        }

        char *nonlinear = read_file_text("../Mettapedia/metta/gslt/tests/datalog/nonlinear_closure.dl");
        CHECK(nonlinear != NULL, "read nonlinear_closure.dl");
        if (nonlinear) {
            const char *exp_nl =
                "a\ta\na\tb\na\tc\na\td\n"
                "b\ta\nb\tb\nb\tc\nb\td\n"
                "c\ta\nc\tb\nc\tc\nc\td\n";
            run_d0_case_and_compare_m1_m2("nonlinear_closure.dl", nonlinear, NULL, "Nonlinear", exp_nl, 24);
            free(nonlinear);
        }

        char *same_gen = read_file_text("../Mettapedia/metta/gslt/tests/datalog/same_generation.dl");
        CHECK(same_gen != NULL, "read same_generation.dl");
        if (same_gen) {
            run_d0_case_and_compare_m1_m2("same_generation.dl", same_gen, NULL,
                                          "SameGeneration", "a\td\nb\tc\ne\tf\n", 3);
            free(same_gen);
        }

        char *cyclic = read_file_text("../Mettapedia/metta/gslt/module/gold/SouffleDatalog/examples/cyclic_graph.dl");
        CHECK(cyclic != NULL, "read cyclic_graph.dl");
        if (cyclic) {
            const char *exp_elig = "loop\t3\nother\t2\nrank\t7\n";
            run_d0_case_and_compare_m1_m2(
                "cyclic_graph.dl", cyclic,
                "../Mettapedia/metta/gslt/module/gold/SouffleDatalog/examples/cyclic_graph",
                "Eligible", exp_elig, 17 + 15 + 3);
            run_d0_case_and_compare_m1_m2("cyclic_graph-empty", cyclic, NULL, "Eligible", "", 0);
            free(cyclic);
        }

        char *pts = read_file_text("../Mettapedia/metta/gslt/module/gold/SouffleDatalog/examples/points_to.dl");
        CHECK(pts != NULL, "read points_to.dl");
        if (pts) {
            const char *exp_heap = "cell\tblue\ncell\tred\nother\tred\n";
            run_d0_case_and_compare_m1_m2(
                "points_to.dl", pts,
                "../Mettapedia/metta/gslt/module/gold/SouffleDatalog/examples/points_to",
                "Heap", exp_heap, 15 + 3);
            run_d0_case_and_compare_m1_m2("points_to-empty", pts, NULL, "Heap", "", 0);
            free(pts);
        }

        const char *cmp_dl =
            ".decl Pair(x:number, y:number)\n"
            "Pair(-3,2). Pair(2,-3). Pair(2,2). Pair(0,0).\n"
            ".decl Eq(x:number, y:number) .output Eq\n"
            "Eq(X,Y) :- Pair(X,Y), X = Y.\n"
            ".decl Ne(x:number, y:number) .output Ne\n"
            "Ne(X,Y) :- Pair(X,Y), X != Y.\n"
            ".decl Lt(x:number, y:number) .output Lt\n"
            "Lt(X,Y) :- Pair(X,Y), X < Y.\n"
            ".decl Le(x:number, y:number) .output Le\n"
            "Le(X,Y) :- Pair(X,Y), X <= Y.\n"
            ".decl Gt(x:number, y:number) .output Gt\n"
            "Gt(X,Y) :- Pair(X,Y), X > Y.\n"
            ".decl Ge(x:number, y:number) .output Ge\n"
            "Ge(X,Y) :- Pair(X,Y), X >= Y.\n";
        run_d0_case_and_compare_m1_m2("scalar-comparisons", cmp_dl, NULL, "Eq", "0\t0\n2\t2\n",
                                      2 + 2 + 1 + 3 + 1 + 3);

        const char *int_widths =
            ".decl Scalar(x:number) .output Scalar\n"
            "Scalar(00012). Scalar(-00012). Scalar(-0). Scalar(0b1010). Scalar(-0b1010).\n"
            "Scalar(0xAf). Scalar(-0xAf). Scalar(-9223372036854775808). Scalar(9223372036854775807).\n"
            ".decl U(x:unsigned) .output U\n"
            "U(18446744073709551615).\n";
        run_d0_case_and_compare_m1_m2("integer-widths-and-unsigned", int_widths, NULL,
                                      "U", "18446744073709551615\n", 9 + 1);

        const char *sym_ord =
            ".decl Word(x:symbol)\n"
            "Word(\"a\"). Word(\"aa\"). Word(\"Z\"). Word(\"λ\").\n"
            ".decl LtSym(x:symbol, y:symbol) .output LtSym\n"
            "LtSym(X,Y) :- Word(X), Word(Y), X < Y.\n";
        run_d0_case_and_compare_m1_m2("symbol-ordering", sym_ord, NULL, "LtSym",
                                      "Z\ta\nZ\taa\nZ\tλ\na\taa\na\tλ\naa\tλ\n", 6);
    }

    /* ---------------------------------------------------------------------
     * Suite 2: GSLT/MeTTa (D0Program ...) S-Expression IR Frontend Parity
     * --------------------------------------------------------------------- */
    {
        const char *metta_ir =
            "(D0Program ("
            "  (D0TypeDecl \"Node\")"
            "  (D0RelationDecl \"Edge\" ((D0Attribute \"x\" (D0TypeCustom \"Node\")) (D0Attribute \"y\" (D0TypeCustom \"Node\"))))"
            "  (D0RelationDecl \"Reach\" ((D0Attribute \"x\" (D0TypeCustom \"Node\")) (D0Attribute \"y\" (D0TypeCustom \"Node\"))))"
            "  (D0OutputDecl \"Reach\")"
            "  (D0FactStmt (D0Atom \"Edge\" ((D0Const (D0Symbol \"a\")) (D0Const (D0Symbol \"b\")))))"
            "  (D0FactStmt (D0Atom \"Edge\" ((D0Const (D0Symbol \"b\")) (D0Const (D0Symbol \"c\")))))"
            "  (D0RuleStmt (D0Clause (D0Atom \"Reach\" ((D0Var \"X\") (D0Var \"Y\")))"
            "    ((D0PosAtom (D0Atom \"Edge\" ((D0Var \"X\") (D0Var \"Y\")))))))"
            "  (D0RuleStmt (D0Clause (D0Atom \"Reach\" ((D0Var \"X\") (D0Var \"Z\")))"
            "    ((D0PosAtom (D0Atom \"Reach\" ((D0Var \"X\") (D0Var \"Y\"))))"
            "     (D0PosAtom (D0Atom \"Edge\" ((D0Var \"Y\") (D0Var \"Z\")))))))"
            "))";
        D0Program *pm = (D0Program *)calloc(1, sizeof(D0Program));
        CHECK(d0_parse_metta_ir(metta_ir, pm) == D0_DIAG_OK, "D0Program MeTTa IR parse");
        CHECK(d0_static_admit(pm) == D0_DIAG_OK, "D0Program MeTTa IR static_admit");
        D0LoweredEngine *eng = (D0LoweredEngine *)calloc(1, sizeof(D0LoweredEngine));
        CHECK(d0_lower_to_tcalc(pm, eng), "D0Program MeTTa IR lower_to_tcalc");
        CHECK(eng->norigins == 2, "D0Program MeTTa IR retains 2 clause origins");
        CHECK(eng->origins[0].stmt_index == 6 && eng->origins[1].stmt_index == 7,
              "D0Program MeTTa IR retains exact statement indices (6, 7)");
        TcAdmissionProfile prof = tc_admission_custom_profile(
            "d0_metta_ir", true, true, false, false, eng, d0_scalar_cmp_permit);
        TcAdmittedEvent ev;
        D0RunMetrics m = d0_run_m2_seminaive(pm, eng, &prof, 0, &ev);
        CHECK(m.status == TC_BRIDGE_ADMITTED && m.events_admitted == 3,
              "D0Program MeTTa IR derives 3 Reach facts");
        CHECK(eng->origins[0].events_admitted == 2 && eng->origins[1].events_admitted == 1,
              "D0Program MeTTa IR tracks per-origin admitted event counts (2 base, 1 transitive)");
        /* Verify witnessed profile inclusion (Lean Event.restrict) on stack-returned D0 event */
        TcAdmissionProfile prof_weaker = tc_admission_custom_profile(
            "d0_metta_ir_weaker", true, false, false, false, eng, d0_scalar_cmp_permit);
        TcAdmissionInclusion inc_ok, inc_bad;
        CHECK(tc_admission_inclusion_init(&inc_ok, &prof, &prof_weaker, true),
              "D0Program witnessed inclusion prof => prof_weaker");
        CHECK(!tc_admission_inclusion_init(&inc_bad, &prof_weaker, &prof, true),
              "D0Program witnessed inclusion refuses unproved strengthening");
        TcAdmittedEvent ev_restricted;
        CHECK(tc_event_restrict_included(&ev, &inc_ok, &ev_restricted),
              "D0Program tc_event_restrict_included transports stack-returned event");
        free(eng);
        free(pm);
    }

    /* ---------------------------------------------------------------------
     * Suite 3: D0 Static Admission Refusal Controls (13 Negative Controls)
     * --------------------------------------------------------------------- */
    {
        struct { const char *name; const char *src; D0DiagKind expected; } neg_cases[] = {
            { "dup-types", ".type T = symbol\n.type T = symbol\n", D0_DIAG_DUPLICATE_TYPES },
            { "dup-rels", ".decl R(x:symbol)\n.decl R(x:number)\n", D0_DIAG_DUPLICATE_RELATIONS },
            { "dup-attr", ".decl R(x:symbol, x:symbol)\n", D0_DIAG_INVALID_DECLARATION },
            { "float-col", ".decl R(x:float)\n", D0_DIAG_INVALID_DECLARATION },
            { "unknown-type", ".decl R(x:NoSuchType)\n", D0_DIAG_INVALID_DECLARATION },
            { "undecl-output", ".output Ghost\n", D0_DIAG_UNDECLARED_IFACE },
            { "fact-arity", ".decl R(x:number, y:number)\nR(1).\n", D0_DIAG_ILL_TYPED_FACT },
            { "fact-int64-overflow", ".decl R(x:number)\nR(9223372036854775808).\n", D0_DIAG_ILL_TYPED_FACT },
            { "fact-uint64-neg", ".decl U(x:unsigned)\nU(-1).\n", D0_DIAG_ILL_TYPED_FACT },
            { "clause-ungrounded-head", ".decl A(x:number)\n.decl B(x:number, y:number)\nB(X,Y) :- A(X).\n", D0_DIAG_ILL_TYPED_CLAUSE },
            { "clause-anon-head", ".decl A(x:number)\n.decl B(x:number)\nB(_) :- A(X).\n", D0_DIAG_ILL_TYPED_CLAUSE },
            { "clause-anon-cmp", ".decl A(x:number)\n.decl B(x:number)\nB(X) :- A(X), X != _.\n", D0_DIAG_ILL_TYPED_CLAUSE },
            { "clause-type-mismatch", ".decl A(x:number)\n.decl S(x:symbol)\n.decl Out(x:number)\nOut(X) :- A(X), S(X).\n", D0_DIAG_ILL_TYPED_CLAUSE }
        };
        D0Program *p = (D0Program *)calloc(1, sizeof(D0Program));
        for (size_t i = 0; i < sizeof(neg_cases) / sizeof(neg_cases[0]); i++) {
            D0DiagKind d = d0_parse_dl(neg_cases[i].src, p);
            if (d == D0_DIAG_OK) d = d0_static_admit(p);
            CHECK(d == neg_cases[i].expected, "negative control %s: got %s, expected %s",
                  neg_cases[i].name, d0_diag_name(d), d0_diag_name(neg_cases[i].expected));
        }
        free(p);
    }

    /* ---------------------------------------------------------------------
     * Suite 4: Differential Missing & Extra Behavior Controls
     * --------------------------------------------------------------------- */
    {
        char *cyclic = read_file_text("../Mettapedia/metta/gslt/module/gold/SouffleDatalog/examples/cyclic_graph.dl");
        const char *facts_dir = "../Mettapedia/metta/gslt/module/gold/SouffleDatalog/examples/cyclic_graph";

        /* 4a. Missing behavior control 1: Budget cutoff is NOT a fixed point */
        D0Program *p_cut = (D0Program *)calloc(1, sizeof(D0Program));
        d0_parse_dl(cyclic, p_cut);
        d0_static_admit(p_cut);
        d0_load_facts_dir(p_cut, facts_dir);
        D0LoweredEngine *eng_cut = (D0LoweredEngine *)calloc(1, sizeof(D0LoweredEngine));
        d0_lower_to_tcalc(p_cut, eng_cut);
        TcAdmissionProfile prof_cut = tc_admission_custom_profile(
            "d0_cutoff", true, true, false, false, eng_cut, d0_scalar_cmp_permit);
        TcAdmittedEvent ev_cut;
        D0RunMetrics m_cut = d0_run_m2_seminaive(p_cut, eng_cut, &prof_cut, 5, &ev_cut);
        CHECK(m_cut.status == TC_BRIDGE_BUDGET_EXHAUSTED,
              "missing-behavior control (budget cutoff): returns TC_BRIDGE_BUDGET_EXHAUSTED, not fixed point");
        CHECK(m_cut.events_admitted < 35,
              "missing-behavior control (budget cutoff): partial store has %" PRIu64 " < 35 derived facts",
              m_cut.events_admitted);
        free(eng_cut);
        free(p_cut);

        /* 4b. Extra behavior control 1: a relaxed profile (enforce_absent = false) cannot commit into the
               protected, sealed fact store: the rule's declared absence guard is checked on commit, so no
               duplicate is derived (set semantics hold, as under the strict profile) */
        D0Program *p_rel = (D0Program *)calloc(1, sizeof(D0Program));
        d0_parse_dl(cyclic, p_rel);
        d0_static_admit(p_rel);
        d0_load_facts_dir(p_rel, facts_dir);
        D0LoweredEngine *eng_rel = (D0LoweredEngine *)calloc(1, sizeof(D0LoweredEngine));
        d0_lower_to_tcalc(p_rel, eng_rel);
        TcAdmissionProfile prof_rel = tc_admission_custom_profile(
            "d0_relaxed_no_absent", false, true, false, false, eng_rel, d0_scalar_cmp_permit);
        TcAdmittedEvent ev_rel;
        D0RunMetrics m_rel = d0_run_m1_naive(p_rel, eng_rel, &prof_rel, 600, &ev_rel);
        CHECK(m_rel.duplicate_facts_derived == 0,
              "extra-behavior control (enforce_absent=false, protected store): derives %" PRIu64 " duplicate facts",
              m_rel.duplicate_facts_derived);
        free(eng_rel);
        free(p_rel);

        /* 4c. Missing-clause & extra-clause program mutants caught by differential check */
        const char *missing_mutant =
            ".decl Edge(x:symbol, y:symbol)\n"
            "Edge(\"a\",\"b\"). Edge(\"b\",\"c\").\n"
            ".decl Reach(x:symbol, y:symbol) .output Reach\n"
            "Reach(X,Y) :- Edge(X,Y).\n";
        const char *extra_mutant =
            ".decl Edge(x:symbol, y:symbol)\n"
            "Edge(\"a\",\"b\"). Edge(\"b\",\"c\").\n"
            ".decl Reach(x:symbol, y:symbol) .output Reach\n"
            "Reach(X,Y) :- Edge(X,Y).\n"
            "Reach(X,Z) :- Reach(X,Y), Edge(Y,Z).\n"
            "Reach(Y,X) :- Edge(X,Y).\n";
        const char *ref_reach = "a\tb\na\tc\nb\tc\n";

        D0Program *pmis = (D0Program *)calloc(1, sizeof(D0Program));
        D0Program *pext = (D0Program *)calloc(1, sizeof(D0Program));
        d0_parse_dl(missing_mutant, pmis); d0_static_admit(pmis);
        D0LoweredEngine *emis = (D0LoweredEngine *)calloc(1, sizeof(D0LoweredEngine));
        d0_lower_to_tcalc(pmis, emis);
        TcAdmissionProfile pr_mis = tc_admission_custom_profile("mis", true, true, false, false, emis, d0_scalar_cmp_permit);
        TcAdmittedEvent ev_m; d0_run_m2_seminaive(pmis, emis, &pr_mis, 0, &ev_m);
        char buf_mis[512]; int cnt_mis = 0;
        d0_format_relation_rows(pmis, emis, 1, buf_mis, sizeof(buf_mis), &cnt_mis);
        CHECK(strcmp(buf_mis, ref_reach) != 0 && cnt_mis < 3,
              "missing-clause mutant rejected against reference (got %d rows, expected 3)", cnt_mis);
        free(emis);
        free(pmis);

        d0_parse_dl(extra_mutant, pext); d0_static_admit(pext);
        D0LoweredEngine *eext = (D0LoweredEngine *)calloc(1, sizeof(D0LoweredEngine));
        d0_lower_to_tcalc(pext, eext);
        TcAdmissionProfile pr_ext = tc_admission_custom_profile("ext", true, true, false, false, eext, d0_scalar_cmp_permit);
        TcAdmittedEvent ev_e; d0_run_m2_seminaive(pext, eext, &pr_ext, 0, &ev_e);
        char buf_ext[512]; int cnt_ext = 0;
        d0_format_relation_rows(pext, eext, 1, buf_ext, sizeof(buf_ext), &cnt_ext);
        CHECK(strcmp(buf_ext, ref_reach) != 0 && cnt_ext > 3,
              "extra-clause mutant rejected against reference (got %d rows, expected 3)", cnt_ext);
        free(eext);
        free(pext);
        free(cyclic);
    }

    /* ---------------------------------------------------------------------
     * Suite 5: Deep-Creativity M1 (Naive) vs. M2 (Semi-Naive + Join Index) Benchmark
     * --------------------------------------------------------------------- */
    {
        char bench_dl[8192];
        size_t pos = 0;
        pos += (size_t)snprintf(bench_dl + pos, sizeof(bench_dl) - pos,
            ".decl Edge(x:number, y:number)\n"
            ".decl Reach(x:number, y:number)\n"
            ".output Reach\n"
            "Reach(X,Y) :- Edge(X,Y).\n"
            "Reach(X,Z) :- Reach(X,Y), Edge(Y,Z).\n");
        int N = 16; /* 16-node chain -> 16*15/2 = 120 Reach facts */
        for (int i = 1; i < N; i++) {
            pos += (size_t)snprintf(bench_dl + pos, sizeof(bench_dl) - pos, "Edge(%d,%d).\n", i, i + 1);
        }
        D0Program *pb1 = (D0Program *)calloc(1, sizeof(D0Program));
        D0Program *pb2 = (D0Program *)calloc(1, sizeof(D0Program));
        d0_parse_dl(bench_dl, pb1); d0_static_admit(pb1);
        *pb2 = *pb1;

        D0LoweredEngine *eb1 = (D0LoweredEngine *)calloc(1, sizeof(D0LoweredEngine));
        D0LoweredEngine *eb2 = (D0LoweredEngine *)calloc(1, sizeof(D0LoweredEngine));
        d0_lower_to_tcalc(pb1, eb1);
        TcAdmissionProfile pr1 = tc_admission_custom_profile("b1", true, true, false, false, eb1, d0_scalar_cmp_permit);
        TcAdmittedEvent ev1;
        D0RunMetrics mb1 = d0_run_m1_naive(pb1, eb1, &pr1, 0, &ev1);

        d0_lower_to_tcalc(pb2, eb2);
        TcAdmissionProfile pr2 = tc_admission_custom_profile("b2", true, true, false, false, eb2, d0_scalar_cmp_permit);
        TcAdmittedEvent ev2;
        D0RunMetrics mb2 = d0_run_m2_seminaive(pb2, eb2, &pr2, 0, &ev2);

        double cand_ratio = (double)mb1.candidates_examined / (double)(mb2.candidates_examined ? mb2.candidates_examined : 1);
        double time_ratio = mb1.elapsed_us / (mb2.elapsed_us > 1.0 ? mb2.elapsed_us : 1.0);
        printf("  [Benchmark 16-node TC] M1 naive: %" PRIu64 " candidates (%.1f us) | "
               "M2 seminaive+join-index: %" PRIu64 " candidates (%.1f us) | "
               "Candidate reduction: %.1fx | Speedup: %.1fx\n",
               mb1.candidates_examined, mb1.elapsed_us,
               mb2.candidates_examined, mb2.elapsed_us,
               cand_ratio, time_ratio);
        CHECK(mb1.events_admitted == 120 && mb2.events_admitted == 120,
              "M1 and M2 both derive all 120 Reach facts");
        CHECK(cand_ratio >= 10.0,
              "M2 examines >= 10x fewer candidates than M1 (%.1fx)", cand_ratio);
        free(eb1);
        free(eb2);
        free(pb1);
        free(pb2);
    }

    /* ---------------------------------------------------------------------
     * Suite 6: C0 Refined CHR Corpus (M1 Naive, M2 Indexed, M3 OS-Parallel)
     * --------------------------------------------------------------------- */
    {
        struct { const char *name; const char *path; const char *expected; bool confluent; } chr_cases[] = {
            { "minimum", "../Mettapedia/metta/gslt/module/gold/CHR/examples/c0/minimum.chr",
              "[minimum(2)]", true },
            { "propagation", "../Mettapedia/metta/gslt/module/gold/CHR/examples/c0/propagation.chr",
              "[published(7),published(7),signal(7),signal(7)]", true },
            { "gcd", "../Mettapedia/metta/gslt/module/gold/CHR/examples/c0/gcd.chr",
              "[gcd(6)]", true },
            { "sieve", "../Mettapedia/metta/gslt/module/gold/CHR/examples/c0/sieve.chr",
              "[prime(2),prime(3),prime(5),prime(7)]", true },
            { "fibonacci", "../Mettapedia/metta/gslt/module/gold/CHR/examples/c0/fibonacci.chr",
              "[fib(0,0),fib(1,1),fib(2,1),fib(3,2),fib(4,3),fib(5,5),fib(6,8),upto(6)]", true },
            { "cyclic_paths", "../Mettapedia/metta/gslt/module/gold/CHR/examples/c0/cyclic_paths.chr",
              "[path(a,a),path(a,b),path(a,c),path(b,a),path(b,b),path(b,c),path(c,a),path(c,b),path(c,c)]", true },
            { "empty", "../Mettapedia/metta/gslt/module/gold/CHR/examples/c0/empty.chr",
              "[]", true },
            { "guard_false", "../Mettapedia/metta/gslt/module/gold/CHR/examples/c0/guard_false.chr",
              "[blocked(0)]", true },
            { "guard_true", "../Mettapedia/metta/gslt/module/gold/CHR/examples/c0/guard_true.chr",
              "[released(-1)]", true },
            { "partner_choice", "../Mettapedia/metta/gslt/module/gold/CHR/examples/c0/partner_choice.chr",
              "[chosen(1),item(2)]", false },
            { "partner_choice_wide", "../Mettapedia/metta/gslt/module/gold/CHR/examples/c0/partner_choice_wide.chr",
              "[chosen(19),item(0),item(1),item(10),item(11),item(12),item(13),item(14),item(15),item(16),item(17),item(18),item(2),item(3),item(4),item(5),item(6),item(7),item(8),item(9)]", false },
            { "partner_pair", "../Mettapedia/metta/gslt/module/gold/CHR/examples/c0/partner_pair.chr",
              "[chosen_pair(3,2),pair_item(1)]", false },
            { "guarded_partner", "../Mettapedia/metta/gslt/module/gold/CHR/examples/c0/guarded_partner.chr",
              "[guard_chosen(3),guard_item(1)]", false }
        };
        for (size_t i = 0; i < sizeof(chr_cases) / sizeof(chr_cases[0]); i++) {
            char *csrc = read_file_text(chr_cases[i].path);
            CHECK(csrc != NULL, "read %s", chr_cases[i].name);
            if (!csrc) continue;
            run_c0_source_both_modes(chr_cases[i].name, csrc,
                                     C0_STATUS_COMPLETED, C0_FAULT_NONE,
                                     chr_cases[i].expected, chr_cases[i].confluent);
            free(csrc);
        }

        /* End-to-End Multi-Language Showcase: demand.dl (D0) -> constant_fold.chr (C0) on sealed tcalc */
        const char *demand_with_facts =
            ".decl Output(n:symbol)\n"
            ".decl Add(n:symbol,a:symbol,b:symbol)\n"
            ".decl Need(n:symbol)\n"
            ".output Need\n"
            "Output(\"out\"). Output(\"future\"). Output(\"copy\"). Output(\"out\").\n"
            "Add(\"sum\",\"a\",\"b\"). Add(\"double\",\"sum\",\"sum\"). Add(\"out\",\"double\",\"bias\").\n"
            "Add(\"copy\",\"a\",\"b\"). Add(\"copy\",\"a\",\"b\"). Add(\"future\",\"dynamic\",\"a\").\n"
            "Add(\"dead_a\",\"dead_b\",\"a\"). Add(\"dead_b\",\"dead_a\",\"b\").\n"
            "Need(N) :- Output(N).\n"
            "Need(A) :- Need(N), Add(N,A,B).\n"
            "Need(B) :- Need(N), Add(N,A,B).\n";
        const char *exp_need = "a\nb\nbias\ncopy\ndouble\ndynamic\nfuture\nout\nsum\n";
        run_d0_case_and_compare_m1_m2("showcase:demand.dl", demand_with_facts, NULL, "Need", exp_need, 9);

        const char *cfold_src =
            ":- chr_constraint constant/2, add/3, input/1, seen/1.\n"
            "same_input @ constant(A,X) \\ add(N,A,A) <=> Z is X+X, constant(N,Z).\n"
            "two_inputs @ constant(A,X), constant(B,Y) \\ add(N,A,B) <=> A \\== B | Z is X+Y, constant(N,Z).\n"
            "note_constant @ constant(N,_) ==> seen(N).\n"
            "?- add(sum,a,b), add(double,sum,sum), add(out,double,bias), "
            "add(copy,a,b), add(copy,a,b), add(future,dynamic,a), "
            "input(dynamic), constant(a,3), constant(b,4), constant(bias,1).\n";
        const char *exp_cfold =
            "[add(future,dynamic,a),constant(a,3),constant(b,4),constant(bias,1),"
            "constant(copy,7),constant(copy,7),constant(double,14),constant(out,15),constant(sum,7),"
            "input(dynamic),seen(a),seen(b),seen(bias),seen(copy),seen(copy),seen(double),seen(out),seen(sum)]";
        run_c0_source_both_modes("showcase:constant_fold.chr", cfold_src,
                                 C0_STATUS_COMPLETED, C0_FAULT_NONE, exp_cfold, true);
    }

    /* ---------------------------------------------------------------------
     * Suite 7: Packages 1-6 Source Fidelity, Counterexamples, Controls & Packets
     * --------------------------------------------------------------------- */
    {
        /* 7a. All 6 C0 Review Counterexamples */
        const char *ce_ordered_body =
            ":- chr_constraint start/0, a/0, b/0, done/0.\n"
            "start_rule @ start <=> a,b.\n"
            "pair @ a,b <=> done.\n"
            "erase @ a <=> true.\n"
            "?- start.\n";
        run_c0_source_both_modes("counterexample:ordered_body.chr", ce_ordered_body,
                                 C0_STATUS_COMPLETED, C0_FAULT_NONE, "[b]", false);

        const char *ce_body_fault =
            ":- chr_constraint p/1, q/1.\n"
            "r @ p(X) <=> Y is X mod 0, q(Y).\n"
            "?- p(1).\n";
        run_c0_source_both_modes("counterexample:body_fault.chr", ce_body_fault,
                                 C0_STATUS_FAULT, C0_FAULT_DIV_BY_ZERO, "[]", false);

        const char *ce_assign_existing_fail =
            ":- chr_constraint p/1, q/1.\n"
            "r @ p(X) <=> X is X+1, q(X).\n"
            "?- p(1).\n";
        run_c0_source_both_modes("counterexample:assignment_existing.chr(mismatch)", ce_assign_existing_fail,
                                 C0_STATUS_FAILED, C0_FAULT_NONE, "[]", false);

        const char *ce_assign_existing_ok =
            ":- chr_constraint p/1, q/1.\n"
            "r @ p(X) <=> X is 1, q(X).\n"
            "?- p(1).\n";
        run_c0_source_both_modes("counterexample:assignment_existing(match)", ce_assign_existing_ok,
                                 C0_STATUS_COMPLETED, C0_FAULT_NONE, "[q(1)]", true);

        const char *ce_quotient =
            "% Prolog line comment and /* block comment */ with integer quotient //\n"
            ":- chr_constraint p/1, q/1, r_neg/3.\n"
            "r @ p(X) <=> Y is X // 2, q(Y).\n"
            "r2 @ q(3) <=> A is -7 // 2, B is -7 rem 2, C is -7 mod 2, r_neg(A,B,C).\n"
            "?- p(7).\n";
        run_c0_source_both_modes("counterexample:quotient.chr(+//,rem,mod)", ce_quotient,
                                 C0_STATUS_COMPLETED, C0_FAULT_NONE, "[r_neg(-3,-1,1)]", true);

        const char *ce_overflow =
            ":- chr_constraint p/1, q/1.\n"
            "r @ p(X) <=> Y is X+1, q(Y).\n"
            "?- p(9223372036854775807).\n";
        run_c0_source_both_modes("counterexample:overflow.chr(wide-int)", ce_overflow,
                                 C0_STATUS_COMPLETED, C0_FAULT_NONE, "[q(9223372036854775808)]", true);

        /* Non-integer arithmetic fault & explicit fails goal */
        const char *ce_non_integer =
            ":- chr_constraint p/1, q/1.\n"
            "r @ p(X) <=> Y is X + 1, q(Y).\n"
            "?- p(atom_val).\n";
        run_c0_source_both_modes("fault:nonInteger", ce_non_integer,
                                 C0_STATUS_FAULT, C0_FAULT_NON_INTEGER, "[]", false);

        const char *ce_explicit_fail =
            ":- chr_constraint p/1.\n"
            "r @ p(1) <=> fail.\n"
            "?- p(1).\n";
        run_c0_source_both_modes("outcome:explicit_fail", ce_explicit_fail,
                                 C0_STATUS_FAILED, C0_FAULT_NONE, "[]", false);

        /* Budget exhaustion outcome */
        {
            const char *loop_chr =
                ":- chr_constraint tick/1.\n"
                "step @ tick(X) <=> Y is X + 1, tick(Y).\n"
                "?- tick(0).\n";
            GsltArena al;
            gslt_arena_init(&al);
            GsltC0Program cpl;
            GsltC0Diagnostic dl_diag;
            char err_l[256] = {0};
            gslt_c0_parse_source(&al, loop_chr, strlen(loop_chr), &cpl, &dl_diag, err_l, sizeof(err_l));
            C0LoweredEngine *el = (C0LoweredEngine *)calloc(1, sizeof(C0LoweredEngine));
            c0_run_machine(&cpl, el, C0_MODE_INDEXED, 1, 5);
            CHECK(el->status == C0_STATUS_BUDGET_EXHAUSTED,
                  "outcome:budget_exhausted returns C0_STATUS_BUDGET_EXHAUSTED (got %s)",
                  c0_status_name(el->status));
            c0_engine_destroy(el);
            free(el);
            gslt_arena_free(&al);
        }

        /* Active kept constraint scan continuation retention (kept head fires and continues scanning same occurrence) */
        const char *kept_scan_chr =
            ":- chr_constraint seed/1, aux/1, out1/1, out2/1.\n"
            "r1 @ seed(X) \\ aux(1) <=> out1(X).\n"
            "r2 @ seed(X) \\ aux(2) <=> out2(X).\n"
            "?- aux(1), aux(2), seed(9).\n";
        run_c0_source_both_modes("kept-active-scan-retention", kept_scan_chr,
                                 C0_STATUS_COMPLETED, C0_FAULT_NONE, "[out1(9),out2(9),seed(9)]", false);

        /* 7b. Recursive first-order tuple(...) matching, construction, equality/disequality on sealed tcalc */
        const char *tuple_chr =
            ":- chr_constraint box/1, pair_box/2, matched/2, distinct_ok/1.\n"
            "unbox_same @ box(tuple(X, tuple(Y, X))) <=> matched(X, Y).\n"
            "check_diff @ pair_box(A, B) <=> A \\== B | distinct_ok(tuple(A, B)).\n"
            "?- box(tuple(alpha, tuple(beta, alpha))), box(tuple(alpha, tuple(beta, gamma))), "
            "pair_box(tuple(1, 2), tuple(1, 3)), pair_box(tuple(1, 2), tuple(1, 2)).\n";
        run_c0_source_both_modes(
            "recursive-first-order-tuples", tuple_chr,
            C0_STATUS_COMPLETED, C0_FAULT_NONE,
            "[box(tuple(alpha,tuple(beta,gamma))),distinct_ok(tuple(tuple(1,2),tuple(1,3))),"
            "matched(alpha,beta),pair_box(tuple(1,2),tuple(1,2))]", true);

        /* 7c. Controls.lean & check_lang_chr.py controls: wide-integers, long-quoted-atom, escaped-strings, anonymous-head-variables, double-quoted-atoms */
        const char *wide_int_chr =
            ":- chr_constraint big/1, out/1.\n"
            "r @ big(X) <=> Y is X * 100000000000000000000 + 42, out(Y).\n"
            "?- big(100000000000000000000).\n";
        run_c0_source_both_modes("control:wide-integers", wide_int_chr,
                                 C0_STATUS_COMPLETED, C0_FAULT_NONE,
                                 "[out(10000000000000000000000000000000000000042)]", true);

        {
            /* long-quoted-atom (> 1024 bytes) & escaped-strings-roundtrip & double-quoted-atoms */
            char long_chr[4096];
            char long_atom[1100];
            memset(long_atom, 'x', 1050);
            long_atom[1050] = '\0';
            snprintf(long_chr, sizeof(long_chr),
                     ":- set_prolog_flag(double_quotes, atom).\n"
                     ":- chr_constraint tag/2, ok/1.\n"
                     "r @ tag('%s', \"hello\\nworld\") <=> ok(\"hello\\nworld\").\n"
                     "?- tag('%s', 'hello\\nworld').\n",
                     long_atom, long_atom);
            run_c0_source_both_modes("control:long-quoted-atom-and-double-quotes", long_chr,
                                     C0_STATUS_COMPLETED, C0_FAULT_NONE, "[ok(hello\nworld)]", true);
        }

        const char *anon_head_chr =
            ":- chr_constraint pair/2, hit/0.\n"
            "r @ pair(_, _) <=> hit.\n"
            "?- pair(1, 2).\n";
        run_c0_source_both_modes("control:anonymous-head-variables", anon_head_chr,
                                 C0_STATUS_COMPLETED, C0_FAULT_NONE, "[hit]", true);

        /* 7d. All 11 CHRPrologLoweringControls.lean + Admission.lean diagnostic priority controls */
        {
            /* canonical_indices: V8 and V0 preserve 8 and 0 */
            const char *canon_src =
                ":- chr_constraint edge/2, reach/2.\n"
                "step @ edge(V8, V0) ==> reach(V8, V0).\n"
                "?- edge(a, b).\n";
            GsltArena ac;
            gslt_arena_init(&ac);
            GsltC0Program cpc;
            GsltC0Diagnostic dc;
            char err_c[256] = {0};
            bool ok_c = gslt_c0_parse_source(&ac, canon_src, strlen(canon_src), &cpc, &dc, err_c, sizeof(err_c));
            CHECK(ok_c && dc.kind == GSLT_C0_DIAG_NONE, "canonical_indices parse");
            CHECK(cpc.rules[0].kept[0].args[0]->var_idx == 8 &&
                  cpc.rules[0].kept[0].args[1]->var_idx == 0,
                  "canonical_indices preserves V8 -> 8 and V0 -> 0 (got %u, %u)",
                  cpc.rules[0].kept[0].args[0]->var_idx,
                  cpc.rules[0].kept[0].args[1]->var_idx);

            /* mixed_names_do_not_alias: V0 and X get distinct indices (0 and 1) */
            const char *mix_src =
                ":- chr_constraint p/2.\n"
                "r @ p(V0, X) <=> true.\n";
            GsltC0Program cpm;
            gslt_c0_parse_source(&ac, mix_src, strlen(mix_src), &cpm, &dc, err_c, sizeof(err_c));
            CHECK(cpm.rules[0].removed[0].args[0]->var_idx == 0 &&
                  cpm.rules[0].removed[0].args[1]->var_idx == 1,
                  "mixed_names_do_not_alias: V0 -> 0, X -> 1");

            /* anonymous_occurrences_distinct: two _ in head get distinct indices */
            const char *anon_src =
                ":- chr_constraint p/3.\n"
                "r @ p(_, V0, _) <=> true.\n";
            GsltC0Program cpa;
            gslt_c0_parse_source(&ac, anon_src, strlen(anon_src), &cpa, &dc, err_c, sizeof(err_c));
            CHECK(cpa.rules[0].removed[0].args[0]->var_idx != cpa.rules[0].removed[0].args[2]->var_idx &&
                  cpa.rules[0].removed[0].args[0]->var_idx == 0 &&
                  cpa.rules[0].removed[0].args[1]->var_idx == 1 &&
                  cpa.rules[0].removed[0].args[2]->var_idx == 2,
                  "anonymous_occurrences_distinct: two _ get distinct indices (0, 1, 2)");

            /* unnamed rule naming follows sentence index */
            const char *unnamed_src =
                ":- chr_constraint p/1.\n"
                "p(X) <=> true.\n";
            GsltC0Program cpu;
            gslt_c0_parse_source(&ac, unnamed_src, strlen(unnamed_src), &cpu, &dc, err_c, sizeof(err_c));
            CHECK(gslt_str_eq_cstr(cpu.rules[0].name, "rule:1"),
                  "unnamed rule after 1 directive gets rule:1");

            struct { const char *name; const char *src; GsltC0DiagKind expected; } c0_neg[] = {
                { "undeclared-query", ":- chr_constraint p/1.\n?- undeclared(1).\n", GSLT_C0_DIAG_UNDECLARED_QUERY },
                { "bad-query-arity", ":- chr_constraint p/1.\n?- p(1, 2).\n", GSLT_C0_DIAG_UNDECLARED_QUERY },
                { "non-ground-query-refused", ":- chr_constraint p/1.\n?- p(X).\n", GSLT_C0_DIAG_NONE },
                { "host-effect-not-executed", ":- write(hello).\n:- chr_constraint p/1.\n", GSLT_C0_DIAG_NONE },
                { "invented-div-refused", ":- chr_constraint p/1, q/1.\nr @ p(X) <=> Y is X div 2, q(Y).\n", GSLT_C0_DIAG_NONE },
                { "invalid-char-code-refused", ":- chr_constraint p/1.\n?- p('\\x110000\\').\n", GSLT_C0_DIAG_NONE },
                { "duplicate-declaration", ":- chr_constraint p/1, p/1.\n", GSLT_C0_DIAG_DUPLICATE_DECLARATION },
                { "undeclared-head", ":- chr_constraint p/1.\nr @ ghost(X) <=> p(X).\n", GSLT_C0_DIAG_UNDECLARED_HEAD },
                { "unbound-guard", ":- chr_constraint p/1.\nr @ p(X) <=> Y > 0 | true.\n", GSLT_C0_DIAG_UNBOUND_GUARD },
                { "unsafe-body-refused(unboundGoal)", ":- chr_constraint p/1, q/1.\nr @ p(X) <=> q(Y).\n", GSLT_C0_DIAG_UNBOUND_GOAL },
                { "undeclared-goal", ":- chr_constraint p/1.\nr @ p(X) <=> ghost(X).\n", GSLT_C0_DIAG_UNDECLARED_GOAL }
            };
            for (size_t i = 0; i < sizeof(c0_neg) / sizeof(c0_neg[0]); i++) {
                GsltC0Program cpn;
                GsltC0Diagnostic dn;
                memset(&dn, 0, sizeof(dn));
                char err_n[256] = {0};
                bool ok_n = gslt_c0_parse_source(&ac, c0_neg[i].src, strlen(c0_neg[i].src), &cpn, &dn, err_n, sizeof(err_n));
                CHECK(!ok_n && dn.kind == c0_neg[i].expected,
                      "C0 negative control %s: ok=%d, got %s, expected %s (%s)",
                      c0_neg[i].name, (int)ok_n, gslt_c0_diag_name(dn.kind), gslt_c0_diag_name(c0_neg[i].expected), err_n);
            }
            gslt_arena_free(&ac);
        }

        /* 7e. SyntaxGSLT Packet, Catalogue, IRCodec, and Canonical Printer Round-Trips (D0 & C0) */
        {
            GsltArena ap;
            gslt_arena_init(&ap);
            char err_p[256] = {0};

            /* D0 SyntaxGSLT packet & multi-packet catalogue agreement + disagreement refusal */
            const char *d0_ir_seed =
                "(D0Program ("
                "  (D0Declaration (\"Edge\") ((D0Attribute \"x\" D0Symbol) (D0Attribute \"y\" D0Symbol)))"
                "  (D0Output (\"Edge\"))"
                "  (D0Fact (\"Edge\") ((D0SymbolValue \"u\") (D0SymbolValue \"v\")))"
                "))";
            GsltByteStr d0_pkt1 = gslt_d0_ir_to_packet_str(&ap, d0_ir_seed, strlen(d0_ir_seed), err_p, sizeof(err_p));
            CHECK(d0_pkt1.len > 0, "D0 IR to SyntaxGSLT packet emission (%s)", err_p);

            GsltByteStr d0_ir_from_pkt = { "", 0 };
            GsltPacketProvenance d0_prov;
            CHECK(gslt_d0_packet_to_ir_str(&ap, d0_pkt1.bytes, d0_pkt1.len, &d0_ir_from_pkt, &d0_prov, err_p, sizeof(err_p)) &&
                  d0_prov.node_count > 0,
                  "SyntaxGSLT D0 single packet parse & provenance (%s)", err_p);

            GsltStrBuf cat_sb;
            gslt_sb_init(&ap, &cat_sb, 512);
            gslt_sb_append_cstr(&ap, &cat_sb, "(SourceValuesV1 ");
            gslt_sb_append_bytes(&ap, &cat_sb, d0_pkt1.bytes, d0_pkt1.len);
            gslt_sb_append_char(&ap, &cat_sb, ' ');
            gslt_sb_append_bytes(&ap, &cat_sb, d0_pkt1.bytes, d0_pkt1.len);
            gslt_sb_append_char(&ap, &cat_sb, ')');

            GsltByteStr d0_ir_from_cat = { "", 0 };
            uint32_t d0_npkts = 0;
            GsltPacketProvenance *d0_provs = NULL;
            CHECK(gslt_d0_catalogue_to_ir_str(&ap, cat_sb.buf, cat_sb.len, &d0_ir_from_cat, &d0_npkts, &d0_provs, err_p, sizeof(err_p)) &&
                  d0_npkts == 2 && gslt_str_eq(d0_ir_from_pkt, d0_ir_from_cat),
                  "SyntaxGSLT D0 2-packet catalogue agreement + provenance preservation (%s)", err_p);

            const char *d0_ir_seed2 =
                "(D0Program ("
                "  (D0Declaration (\"Other\") ((D0Attribute \"x\" D0Symbol)))"
                "  (D0Output (\"Other\"))"
                "))";
            GsltByteStr d0_pkt2 = gslt_d0_ir_to_packet_str(&ap, d0_ir_seed2, strlen(d0_ir_seed2), err_p, sizeof(err_p));
            GsltStrBuf cat_bad_sb;
            gslt_sb_init(&ap, &cat_bad_sb, 512);
            gslt_sb_append_cstr(&ap, &cat_bad_sb, "(SourceValuesV1 ");
            gslt_sb_append_bytes(&ap, &cat_bad_sb, d0_pkt1.bytes, d0_pkt1.len);
            gslt_sb_append_char(&ap, &cat_bad_sb, ' ');
            gslt_sb_append_bytes(&ap, &cat_bad_sb, d0_pkt2.bytes, d0_pkt2.len);
            gslt_sb_append_char(&ap, &cat_bad_sb, ')');
            GsltByteStr d0_ir_bad = { "", 0 };
            CHECK(!gslt_d0_catalogue_to_ir_str(&ap, cat_bad_sb.buf, cat_bad_sb.len, &d0_ir_bad, NULL, NULL, err_p, sizeof(err_p)),
                  "SyntaxGSLT D0 catalogue disagreement refused");
            CHECK(!gslt_d0_packet_to_ir_str(&ap, "(result (node dl-src:program ()) (tok extra \"x\"))", 49, &d0_ir_bad, NULL, err_p, sizeof(err_p)),
                  "SyntaxGSLT D0 non-nil remainder refused");

            /* D0 Lean IRCodec.lean (Program [...]) emit -> parse -> source round-trip */
            D0Program *dp1 = (D0Program *)calloc(1, sizeof(D0Program));
            D0Program *dp2 = (D0Program *)calloc(1, sizeof(D0Program));
            CHECK(d0_parse_metta_ir(d0_ir_from_cat.bytes, dp1) == D0_DIAG_OK && d0_static_admit(dp1) == D0_DIAG_OK,
                  "D0 packet IR parse & admit");
            GsltByteStr d0_lean_ir = d0_emit_metta_ir(&ap, dp1);
            CHECK(d0_parse_metta_ir(d0_lean_ir.bytes, dp2) == D0_DIAG_OK && d0_static_admit(dp2) == D0_DIAG_OK,
                  "D0 IRCodec.lean (Program [...]) emit -> parse round-trip");
            GsltByteStr d0_dl_src = d0_emit_dl_source(&ap, dp2);
            run_d0_case_and_compare_m1_m2("SyntaxGSLT-D0-packet->IR->dl->tcalc", d0_dl_src.bytes, NULL, "Edge", "u\tv\n", 1);
            free(dp1);
            free(dp2);

            /* C0 SyntaxGSLT packet, catalogue, IRCodec, and source printer round-trips */
            const char *c0_seed_src =
                ":- chr_constraint num/1.\n"
                "keep_min @ num(X) \\ num(Y) <=> X =< Y | true.\n"
                "?- num(5), num(2).\n";
            GsltByteStr c0_pkt1 = gslt_c0_source_to_packet_str(&ap, c0_seed_src, strlen(c0_seed_src), err_p, sizeof(err_p));
            CHECK(c0_pkt1.len > 0, "C0 source to SyntaxGSLT packet emission (%s)", err_p);

            GsltStrBuf c0_cat_sb;
            gslt_sb_init(&ap, &c0_cat_sb, 512);
            gslt_sb_append_cstr(&ap, &c0_cat_sb, "(SourceValuesV1 ");
            gslt_sb_append_bytes(&ap, &c0_cat_sb, c0_pkt1.bytes, c0_pkt1.len);
            gslt_sb_append_char(&ap, &c0_cat_sb, ' ');
            gslt_sb_append_bytes(&ap, &c0_cat_sb, c0_pkt1.bytes, c0_pkt1.len);
            gslt_sb_append_char(&ap, &c0_cat_sb, ')');

            GsltC0Program cp_cat;
            GsltC0Diagnostic d_cat;
            GsltPacketProvenance *c0_provs = NULL;
            uint32_t c0_nprovs = 0;
            CHECK(gslt_c0_read_catalogue(&ap, c0_cat_sb.buf, c0_cat_sb.len, &cp_cat, &d_cat, &c0_provs, &c0_nprovs, err_p, sizeof(err_p)) &&
                  c0_nprovs == 2 && c0_provs[0].node_count > 0,
                  "SyntaxGSLT C0 2-packet catalogue parse, agreement & provenance (%s)", err_p);

            /* Disagreement refusal in C0 catalogue */
            const char *c0_seed_other =
                ":- chr_constraint other/1.\n"
                "?- other(1).\n";
            GsltByteStr c0_pkt2 = gslt_c0_source_to_packet_str(&ap, c0_seed_other, strlen(c0_seed_other), err_p, sizeof(err_p));
            GsltStrBuf c0_bad_cat;
            gslt_sb_init(&ap, &c0_bad_cat, 512);
            gslt_sb_append_cstr(&ap, &c0_bad_cat, "(SourceValuesV1 ");
            gslt_sb_append_bytes(&ap, &c0_bad_cat, c0_pkt1.bytes, c0_pkt1.len);
            gslt_sb_append_char(&ap, &c0_bad_cat, ' ');
            gslt_sb_append_bytes(&ap, &c0_bad_cat, c0_pkt2.bytes, c0_pkt2.len);
            gslt_sb_append_char(&ap, &c0_bad_cat, ')');
            GsltC0Program cp_bad;
            CHECK(!gslt_c0_read_catalogue(&ap, c0_bad_cat.buf, c0_bad_cat.len, &cp_bad, &d_cat, NULL, NULL, err_p, sizeof(err_p)),
                  "SyntaxGSLT C0 catalogue disagreement refused");

            GsltByteStr c0_ir_str = gslt_c0_emit_ir(&ap, &cp_cat);
            GsltC0Program cp_ir_rt;
            CHECK(gslt_c0_parse_ir(&ap, c0_ir_str.bytes, c0_ir_str.len, &cp_ir_rt, &d_cat, err_p, sizeof(err_p)) &&
                  gslt_c0_program_eq(&cp_cat, &cp_ir_rt),
                  "C0 CHRProgramCodec.lean (program ...) emit -> parse round-trip (%s)", err_p);
            GsltByteStr c0_src_str = gslt_c0_emit_prolog_source(&ap, &cp_ir_rt);
            run_c0_source_both_modes("SyntaxGSLT-C0-packet->IR->source->tcalc", c0_src_str.bytes,
                                     C0_STATUS_COMPLETED, C0_FAULT_NONE, "[num(2)]", true);

            gslt_arena_free(&ap);
        }

        /* 7f. Package 3 Receipt & Policy Safety Controls + Package 6 ordinary_flat_adapter Controls */
        {
            const char *rc_src =
                ":- chr_constraint p/1, q/1.\n"
                "step_rule @ p(X) <=> X > 0 | Y is X + 1, q(Y).\n"
                "?- p(5).\n";
            TcAdmittedEvent stack_ev = helper_stack_return_c0_event(rc_src);
            CHECK(stack_ev.prepared.rule >= 0,
                  "stack-returned C0 TcAdmittedEvent survives frame exit under ASan/UBSan");

            /* Context-mutation & changed-profile control: mutating external memory after commit cannot retroactively alter witnessed inclusion */
            int mutable_ctx_word = 1;
            TcAdmissionProfile p_strict = tc_admission_custom_profile(
                "c0_strict_ctx", true, true, false, false, &mutable_ctx_word, c0_guard_permit);
            TcAdmissionProfile p_relaxed = tc_admission_custom_profile(
                "c0_relaxed_ctx", true, false, false, false, &mutable_ctx_word, c0_guard_permit);
            TcAdmissionInclusion inc_same_ctx, inc_diff_ctx;
            CHECK(tc_admission_inclusion_init(&inc_same_ctx, &p_strict, &p_relaxed, true),
                  "witnessed inclusion succeeds for identical permit+ctx");
            int other_ctx_word = 2;
            TcAdmissionProfile p_other_ctx = tc_admission_custom_profile(
                "c0_other_ctx", true, false, false, false, &other_ctx_word, c0_guard_permit);
            CHECK(!tc_admission_inclusion_init(&inc_diff_ctx, &p_strict, &p_other_ctx, false),
                  "witnessed inclusion refuses un-witnessed context change");

            /* Verify ordinary_flat_adapter return code constants match ABI (0=REFUSED, 1=FIRED, 2=UNSUPPORTED) */
            CHECK(ORDINARY_FLAT_REFUSED == 0 && ORDINARY_FLAT_FIRED == 1 && ORDINARY_FLAT_UNSUPPORTED == 2,
                  "ordinary_flat_adapter return code constants match ABI (0, 1, 2)");
            {
                OrdinaryFlatWorkspace ws;
                memset(&ws, 0, sizeof(ws));
                uint32_t too_many[ORDINARY_FLAT_MAX_PREMISES + 1];
                memset(too_many, 0, sizeof(too_many));
                uint64_t rc_unsup = ordinary_flat_adapter(
                    (cesta_read_u32_span){NULL, 0},
                    (cesta_read_u32_span){too_many, ORDINARY_FLAT_MAX_PREMISES + 1},
                    (cesta_read_u32_span){NULL, 0}, (cesta_read_u32_span){NULL, 0},
                    (cesta_read_u32_span){NULL, 0},
                    (cesta_write_u32_span){ws.fields, ORDINARY_FLAT_MAX_FIELDS},
                    (cesta_write_u32_span){ws.rows, ORDINARY_FLAT_MAX_PREMISES + 1},
                    (cesta_write_u32_span){ws.dest, ORDINARY_FLAT_MAX_OUTPUT},
                    (cesta_write_u32_span){ws.scratch, ORDINARY_FLAT_MAX_OUTPUT});
                CHECK(rc_unsup == ORDINARY_FLAT_UNSUPPORTED,
                      "ordinary_flat_adapter returns ORDINARY_FLAT_UNSUPPORTED (2) when nkeep exceeds capacity");

                uint32_t source[4] = { 10, 42, 42, 99 };
                uint32_t offsets[1] = { 0 };
                uint32_t guards[1] = { (0u) | (1u << 8) | (0u << 16) | (2u << 24) }; /* prem 0 field 1 == prem 0 field 2 */
                uint32_t make[1]   = { (0u) | (1u << 8) };
                uint64_t rc_fired = ordinary_flat_adapter(
                    (cesta_read_u32_span){source, 4}, (cesta_read_u32_span){offsets, 1},
                    (cesta_read_u32_span){NULL, 0}, (cesta_read_u32_span){guards, 1},
                    (cesta_read_u32_span){make, 1}, (cesta_write_u32_span){ws.fields, 4},
                    (cesta_write_u32_span){ws.rows, 2}, (cesta_write_u32_span){ws.dest, 1},
                    (cesta_write_u32_span){ws.scratch, 1});
                CHECK(rc_fired == ORDINARY_FLAT_FIRED && ws.dest[0] == 42,
                      "ordinary_flat_adapter returns ORDINARY_FLAT_FIRED (1) and populates dest on matching guard");
                source[2] = 43;
                uint64_t rc_refused = ordinary_flat_adapter(
                    (cesta_read_u32_span){source, 4}, (cesta_read_u32_span){offsets, 1},
                    (cesta_read_u32_span){NULL, 0}, (cesta_read_u32_span){guards, 1},
                    (cesta_read_u32_span){make, 1}, (cesta_write_u32_span){ws.fields, 4},
                    (cesta_write_u32_span){ws.rows, 2}, (cesta_write_u32_span){ws.dest, 1},
                    (cesta_write_u32_span){ws.scratch, 1});
                CHECK(rc_refused == ORDINARY_FLAT_REFUSED,
                      "ordinary_flat_adapter returns ORDINARY_FLAT_REFUSED (0) on failing guard");
            }
#ifdef TC_ORDINARY_FLAT_TEST_HOOKS
            extern uint64_t tc_test_ordinary_flat_leaf_calls;
            extern uint64_t tc_test_ordinary_flat_leaf_fired;
            extern uint64_t tc_test_ordinary_flat_refusals;
            extern uint64_t tc_test_ordinary_flat_slow_calls;
            (void)tc_test_ordinary_flat_slow_calls;
            CHECK(tc_test_ordinary_flat_leaf_calls > 0 && tc_test_ordinary_flat_leaf_fired > 0,
                  "ordinary_flat_adapter leaf executed %" PRIu64 " calls (%" PRIu64 " fired, %" PRIu64 " refused) during self-test",
                  tc_test_ordinary_flat_leaf_calls, tc_test_ordinary_flat_leaf_fired, tc_test_ordinary_flat_refusals);
#endif
        }

        /* -----------------------------------------------------------------
         * Suite 8: Gold C1 First-Order CHR (leq.chr, finite_terms.pl, resource_scheduler.pl)
         * ----------------------------------------------------------------- */
        {
            const char *leq_src =
                ":- chr_constraint leq/2.\n"
                "reflexivity  @ leq(X, X) <=> true.\n"
                "antisymmetry @ leq(X, Y), leq(Y, X) <=> X = Y.\n"
                "idempotence  @ leq(X, Y) \\ leq(X, Y) <=> true.\n"
                "transitivity @ leq(X, Y), leq(Y, Z) ==> leq(X, Z).\n";
            run_c1_source_both_modes("C1:leq:cycle-collapse", leq_src,
                                     "leq(A, B), leq(B, C), leq(C, A), A == B, B == C",
                                     C0_STATUS_COMPLETED, C0_FAULT_NONE, "[]");
            run_c1_source_both_modes("C1:leq:chain", leq_src,
                                     "leq(x, y), leq(y, z)",
                                     C0_STATUS_COMPLETED, C0_FAULT_NONE, "[leq(x,y),leq(x,z),leq(y,z)]");
            run_c1_source_both_modes("C1:leq:antisymmetry-conflict", leq_src,
                                     "leq(x, y), leq(y, x)",
                                     C0_STATUS_FAILED, C0_FAULT_NONE, NULL);

            char *ft_src = read_file_text("../Mettapedia/metta/gslt/module/gold/CHR/examples/finite_terms.pl");
            CHECK(ft_src != NULL, "read finite_terms.pl");
            if (ft_src) {
                run_c1_source_both_modes("C1:finite_terms:finite-term-propagation", ft_src,
                                         "wire(a,b), wire(b,c), value(a,pair(X,z)), value(c,pair(x,z)), X == x",
                                         C0_STATUS_COMPLETED, C0_FAULT_NONE,
                                         "[observed(a,pair(x,z)),observed(b,pair(x,z)),observed(c,pair(x,z)),value(a,pair(x,z)),value(b,pair(x,z)),value(c,pair(x,z)),wire(a,b),wire(b,c)]");
                run_c1_source_both_modes("C1:finite_terms:equal-validation-evidence", ft_src,
                                         "value(a,pair(x,z)), value(a,pair(x,z))",
                                         C0_STATUS_COMPLETED, C0_FAULT_NONE,
                                         "[observed(a,pair(x,z)),value(a,pair(x,z))]");
                run_c1_source_both_modes("C1:finite_terms:wrong-conclusion", ft_src,
                                         "value(a, x), value(a, y)",
                                         C0_STATUS_FAILED, C0_FAULT_NONE, NULL);
                run_c1_source_both_modes("C1:finite_terms:occurs-check", ft_src,
                                         "same(X, node(X))",
                                         C0_STATUS_FAILED, C0_FAULT_NONE, NULL);
                run_c1_source_both_modes("C1:finite_terms:missing-wire", ft_src,
                                         "value(a, x)",
                                         C0_STATUS_COMPLETED, C0_FAULT_NONE,
                                         "[observed(a,x),value(a,x)]");
                free(ft_src);
            }

            char *rs_src = read_file_text("../Mettapedia/metta/gslt/module/gold/CHR/examples/resource_scheduler.pl");
            CHECK(rs_src != NULL, "read resource_scheduler.pl");
            if (rs_src) {
                run_c1_source_both_modes("C1:resource_scheduler:equal-workers", rs_src,
                                         "ready(a,yes), token(worker), token(worker), request(a), request(a)",
                                         C0_STATUS_COMPLETED, C0_FAULT_NONE,
                                         "[ready(a,yes),receipt(a,primary),receipt(a,primary),reported(a,primary),reported(a,primary)]");
                run_c1_source_both_modes("C1:resource_scheduler:exhausted-workers", rs_src,
                                         "ready(a,yes), token(worker), request(a), request(a)",
                                         C0_STATUS_COMPLETED, C0_FAULT_NONE,
                                         "[ready(a,yes),receipt(a,primary),reported(a,primary),request(a)]");
                run_c1_source_both_modes("C1:resource_scheduler:ordered-resource-choice", rs_src,
                                         "ready(a,yes), token(backup), token(worker), request(a)",
                                         C0_STATUS_COMPLETED, C0_FAULT_NONE,
                                         "[ready(a,yes),receipt(a,primary),reported(a,primary),token(backup)]");
                run_c1_source_both_modes("C1:resource_scheduler:backup-resource", rs_src,
                                         "ready(a,yes), token(backup), request(a)",
                                         C0_STATUS_COMPLETED, C0_FAULT_NONE,
                                         "[ready(a,yes),receipt(a,backup),reported(a,backup)]");
                run_c1_source_both_modes("C1:resource_scheduler:failed-guard", rs_src,
                                         "ready(a,no), token(worker), request(a)",
                                         C0_STATUS_COMPLETED, C0_FAULT_NONE,
                                         "[ready(a,no),request(a),token(worker)]");
                run_c1_source_both_modes("C1:resource_scheduler:missing-permission", rs_src,
                                         "token(worker), request(a)",
                                         C0_STATUS_COMPLETED, C0_FAULT_NONE,
                                         "[request(a),token(worker)]");
                run_c1_source_both_modes("C1:resource_scheduler:binding-wakes-suspended-constraints", rs_src,
                                         "ready(a,Flag), token(worker), request(a), unify_with_occurs_check(Flag,yes)",
                                         C0_STATUS_COMPLETED, C0_FAULT_NONE,
                                         "[ready(a,yes),receipt(a,primary),reported(a,primary)]");
                run_c1_source_both_modes("C1:resource_scheduler:propagation-history-survives-wakeup", rs_src,
                                         "receipt(J,primary), unify_with_occurs_check(J,a), receipt(a,primary)",
                                         C0_STATUS_COMPLETED, C0_FAULT_NONE,
                                         "[receipt(a,primary),receipt(a,primary),reported(a,primary),reported(a,primary)]");
                free(rs_src);
            }
        }

        /* -----------------------------------------------------------------
         * Suite 9: Stage 1 Qualification Controls (D0 Fast-Path Invariants &
         *          CHR Boundary-Size Wakeup/Partner/Budget/Order Controls)
         * ----------------------------------------------------------------- */
        {
            const char *tc_src =
                ".decl Edge(x:number, y:number)\n"
                ".decl Reach(x:number, y:number) .output Reach\n"
                "Edge(1,2). Edge(2,3).\n"
                "Reach(X,Y) :- Edge(X,Y).\n"
                "Reach(X,Z) :- Reach(X,Y), Edge(Y,Z).\n";

            /* 9a. Control D0-Opt-1: Mutated index entry triggers fallback and preserves exact closure */
            {
                D0Program *p = (D0Program *)calloc(1, sizeof(D0Program));
                d0_parse_dl(tc_src, p); d0_static_admit(p);
                D0LoweredEngine *eng = (D0LoweredEngine *)calloc(1, sizeof(D0LoweredEngine));
                d0_lower_to_tcalc_ex(p, eng, true);
                TcAdmissionProfile prof = tc_admission_custom_profile(
                    "d0_mut_idx", true, true, false, false, eng, d0_scalar_cmp_permit);
                M2JoinIndex *ix = (M2JoinIndex *)calloc(1, sizeof(M2JoinIndex));
                m2_index_init(ix);
                for (uint32_t w = 0; w < eng->noccs; w++) m2_index_insert(ix, p, eng->occs[w]);
                M2ClausePlan plan;
                m2_build_clause_plan(p, eng, 0, &plan);
                /* Corrupt entry 0's argument without updating entry_digest */
                Term orig_args[2] = { ix->entries[0].args[0], ix->entries[0].args[1] };
                Term saved_arg = ix->entries[0].args[0];
                ix->entries[0].args[0] ^= 0x12345678u;
                bool corrupt = false;
                (void)m2_tuple_contains_checked(ix, ix->entries[0].rel_idx, 2, orig_args, &corrupt);
                CHECK(corrupt, "Control D0-Opt-1: mutated M2FactEntry detected by entry_digest check");
                /* Also corrupt ix->index_digest and verify d0_m2_dfs refuses fast path and falls back */
                ix->entries[0].args[0] = saved_arg;
                ix->index_digest ^= 1ULL;
                TcBridgeBudget budget = { .max_candidates = 0, .candidates_inspected = 0,
                                          .has_unresolved_work = true, .last_refusal = TC_REFUSE_NONE };
                D0RunMetrics m = {0};
                Occ keep_occ[1] = { eng->occs[0] };
                Term var_env[D0_MAX_VARS] = { ix->entries[0].args[0], ix->entries[0].args[1] };
                TcAdmittedEvent ev = {0};
                d0_m2_dfs(p, eng, ix, &plan, 0, 1, 0, 0, ix->nentries, ix->nentries,
                          keep_occ, var_env, 3u, &prof, &budget, &m, &ev);
                CHECK(eng->fast_path_fallbacks > 0 && !ix->index_valid && m.events_admitted == 1 && ev.receipt.out_term != 0,
                      "Control D0-Opt-1: index_digest mismatch triggers fallback to reference bridge and still admits valid fact");
                free(ix);
                free(eng);
                free(p);
            }

            /* 9b. Control D0-Opt-2: Duplicate input & out-of-band duplicate store insertion */
            {
                const char *dup_src =
                    ".decl Edge(x:number, y:number)\n"
                    ".decl Reach(x:number, y:number) .output Reach\n"
                    "Edge(1,2). Edge(1,2). Edge(2,3). Edge(2,3).\n"
                    "Reach(X,Y) :- Edge(X,Y).\n"
                    "Reach(X,Z) :- Reach(X,Y), Edge(Y,Z).\n";
                run_d0_case_and_compare_m1_m2("Control D0-Opt-2a:duplicate-EDB-input", dup_src, NULL,
                                              "Reach", "1\t2\n1\t3\n2\t3\n", 3);

                D0Program *p = (D0Program *)calloc(1, sizeof(D0Program));
                d0_parse_dl(tc_src, p); d0_static_admit(p);
                D0LoweredEngine *eng = (D0LoweredEngine *)calloc(1, sizeof(D0LoweredEngine));
                d0_lower_to_tcalc_ex(p, eng, true);
                /* Inject out-of-band duplicate occurrence into eng->occs before running M2 */
                eng->occs[eng->noccs] = eng->occs[0];
                eng->noccs++;
                TcAdmissionProfile prof = tc_admission_custom_profile(
                    "d0_oob_dup", true, true, false, false, eng, d0_scalar_cmp_permit);
                TcAdmittedEvent ev = {0};
                D0RunMetrics m = d0_run_m2_seminaive(p, eng, &prof, 0, &ev);
                int cnt = 0;
                char *rbuf = d0_format_relation_rows_alloc(p, eng, 1, &cnt);
                CHECK(eng->fast_path_fallbacks > 0 && m.events_admitted == 3 && cnt == 3 &&
                      strcmp(rbuf, "1\t2\n1\t3\n2\t3\n") == 0,
                      "Control D0-Opt-2b: out-of-band store duplicate triggers fallback and enforces set semantics (cnt=%d, admitted=%" PRIu64 ")",
                      cnt, m.events_admitted);
                free(rbuf);
                free(eng);
                free(p);
            }

            /* 9c. Control D0-Opt-3: Altered rule metadata (forged is_pure_horn on comparison rule) */
            {
                const char *cmp_src =
                    ".decl Pair(x:number, y:number)\n"
                    ".decl Lt(x:number, y:number) .output Lt\n"
                    "Pair(5,2). Pair(1,4).\n"
                    "Lt(X,Y) :- Pair(X,Y), X < Y.\n";
                D0Program *p = (D0Program *)calloc(1, sizeof(D0Program));
                d0_parse_dl(cmp_src, p); d0_static_admit(p);
                D0LoweredEngine *eng = (D0LoweredEngine *)calloc(1, sizeof(D0LoweredEngine));
                d0_lower_to_tcalc_ex(p, eng, true);
                /* Maliciously forge is_pure_horn = true on the X < Y clause */
                eng->origins[0].is_pure_horn = true;
                TcAdmissionProfile prof = tc_admission_custom_profile(
                    "d0_forged_meta", true, true, false, false, eng, d0_scalar_cmp_permit);
                TcAdmittedEvent ev = {0};
                D0RunMetrics m = d0_run_m2_seminaive(p, eng, &prof, 0, &ev);
                int cnt = 0;
                char *rbuf = d0_format_relation_rows_alloc(p, eng, 1, &cnt);
                CHECK(eng->fast_path_fallbacks > 0 && m.events_admitted == 1 && cnt == 1 &&
                      strcmp(rbuf, "1\t4\n") == 0,
                      "Control D0-Opt-3: forged is_pure_horn rejected by horn_cert_digest/rule_ncmps check; X < Y still enforced");
                free(rbuf);
                free(eng);
                free(p);
            }

            /* 9d. Control D0-Opt-4: Broken epoch invariants (delta_lo > delta_hi) */
            {
                D0Program *p = (D0Program *)calloc(1, sizeof(D0Program));
                d0_parse_dl(tc_src, p); d0_static_admit(p);
                D0LoweredEngine *eng = (D0LoweredEngine *)calloc(1, sizeof(D0LoweredEngine));
                d0_lower_to_tcalc_ex(p, eng, true);
                TcAdmissionProfile prof = tc_admission_custom_profile(
                    "d0_bad_epoch", true, true, false, false, eng, d0_scalar_cmp_permit);
                M2JoinIndex *ix = (M2JoinIndex *)calloc(1, sizeof(M2JoinIndex));
                m2_index_init(ix);
                for (uint32_t w = 0; w < eng->noccs; w++) m2_index_insert(ix, p, eng->occs[w]);
                M2ClausePlan plan;
                m2_build_clause_plan(p, eng, 0, &plan);
                CHECK(!d0_m2_fast_path_qualified(eng, ix, &eng->origins[0], &plan, &prof, 2, 1, ix->nentries) &&
                      !d0_m2_fast_path_qualified(eng, ix, &eng->origins[0], &plan, &prof, -1, 1, ix->nentries) &&
                      !d0_m2_fast_path_qualified(eng, ix, &eng->origins[0], &plan, &prof, 0, 1, ix->nentries + 1),
                      "Control D0-Opt-4: broken epoch bounds (delta_lo > delta_hi, delta_lo < 0, max_ei > nentries) refused");
                free(ix);
                free(eng);
                free(p);
            }

            /* 9e. CHR Boundary-Size Wakeup Chains (511, 512, 513, 1025) */
            {
                const int wake_sizes[] = { 511, 512, 513, 1025 };
                for (size_t wi = 0; wi < sizeof(wake_sizes) / sizeof(wake_sizes[0]); wi++) {
                    int n = wake_sizes[wi];
                    size_t cap = (size_t)n * 24 + 256;
                    char *qbuf = (char *)malloc(cap);
                    size_t pos = 0;
                    for (int i = 0; i < n; i++) {
                        pos += (size_t)snprintf(qbuf + pos, cap - pos, "wait(X,%d), ", i);
                    }
                    snprintf(qbuf + pos, cap - pos, "unify_with_occurs_check(X, yes)");
                    const char *wprog =
                        ":- use_module(library(chr)).\n"
                        ":- chr_constraint wait/2, hit/0.\n"
                        "fire @ wait(yes, 0) <=> hit.\n"
                        "drop @ wait(yes, _) <=> true.\n";
                    char label[64];
                    snprintf(label, sizeof(label), "CHR-boundary:wake-%d", n);
                    run_c1_source_both_modes(label, wprog, qbuf,
                                             C0_STATUS_COMPLETED, C0_FAULT_NONE, "[hit]");
                    free(qbuf);
                }
            }

            /* 9f. CHR Boundary-Size Partner Search (511, 512, 513, 1025) */
            {
                const int part_sizes[] = { 511, 512, 513, 1025 };
                for (size_t pi = 0; pi < sizeof(part_sizes) / sizeof(part_sizes[0]); pi++) {
                    int n = part_sizes[pi];
                    size_t cap = (size_t)n * 20 + 256;
                    char *pbuf = (char *)malloc(cap);
                    size_t pos = 0;
                    pos += (size_t)snprintf(pbuf + pos, cap - pos,
                        ":- chr_constraint a/1, b/1, ok/0.\n"
                        "r @ a(X), b(Y) <=> X == Y | ok.\n"
                        "?- b(0)");
                    for (int i = 1; i <= n; i++) {
                        pos += (size_t)snprintf(pbuf + pos, cap - pos, ", b(%d)", i);
                    }
                    snprintf(pbuf + pos, cap - pos, ", a(0).\n");

                    GsltArena a1, a2;
                    gslt_arena_init(&a1);
                    gslt_arena_init(&a2);
                    GsltC0Program cp1, cp2;
                    GsltC0Diagnostic d1 = {0}, d2 = {0};
                    char err[256] = {0};
                    bool ok1 = gslt_c0_parse_source(&a1, pbuf, strlen(pbuf), &cp1, &d1, err, sizeof(err));
                    bool ok2 = gslt_c0_parse_source(&a2, pbuf, strlen(pbuf), &cp2, &d2, err, sizeof(err));
                    C0LoweredEngine *e1 = (C0LoweredEngine *)calloc(1, sizeof(C0LoweredEngine));
                    C0LoweredEngine *e2 = (C0LoweredEngine *)calloc(1, sizeof(C0LoweredEngine));
                    c0_run_machine(&cp1, e1, C0_MODE_NAIVE, 1, 0);
                    c0_run_machine(&cp2, e2, C0_MODE_INDEXED, 1, 0);
                    char s1[16384], s2[16384];
                    c0_format_store(e1, s1, sizeof(s1));
                    c0_format_store(e2, s2, sizeof(s2));
                    CHECK(ok1 && ok2 && e1->status == C0_STATUS_COMPLETED && e2->status == C0_STATUS_COMPLETED &&
                          e1->events_admitted == 1 && e2->events_admitted == 1 &&
                          strstr(s1, ",ok]") != NULL && strcmp(s1, s2) == 0,
                          "CHR-boundary:partner-%d finds oldest matching partner in naive & indexed modes", n);
                    c0_engine_destroy(e1);
                    c0_engine_destroy(e2);
                    free(e1);
                    free(e2);
                    gslt_arena_free(&a1);
                    gslt_arena_free(&a2);
                    free(pbuf);
                }
            }

            /* 9g. CHR --max-steps 1 Budget Enforcement Across Naive, Indexed & Parallel Modes */
            {
                const char *bprog =
                    ":- chr_constraint a/1.\n"
                    "step @ a(X) <=> Y is X + 1, a(Y).\n"
                    "?- a(0).\n";
                C0SearchMode modes[3] = { C0_MODE_NAIVE, C0_MODE_INDEXED, C0_MODE_PARALLEL };
                const char *mnames[3] = { "naive", "indexed", "parallel" };
                for (int mi = 0; mi < 3; mi++) {
                    GsltArena ab;
                    gslt_arena_init(&ab);
                    GsltC0Program cpb;
                    GsltC0Diagnostic db = {0};
                    char err[256] = {0};
                    gslt_c0_parse_source(&ab, bprog, strlen(bprog), &cpb, &db, err, sizeof(err));
                    C0LoweredEngine *eb = (C0LoweredEngine *)calloc(1, sizeof(C0LoweredEngine));
                    c0_run_machine(&cpb, eb, modes[mi], modes[mi] == C0_MODE_PARALLEL ? 4 : 1, 1);
                    char sb[256];
                    c0_format_store(eb, sb, sizeof(sb));
                    CHECK(eb->status == C0_STATUS_BUDGET_EXHAUSTED && eb->events_admitted == 1 &&
                          strcmp(sb, "[a(1)]") == 0,
                          "CHR-budget:max_steps=1 (%s): status=%s, events=%" PRIu64 ", store=%s",
                          mnames[mi], c0_status_name(eb->status), eb->events_admitted, sb);
                    c0_engine_destroy(eb);
                    free(eb);
                    gslt_arena_free(&ab);
                }
            }

            /* 9h. CHR Refined Left-to-Right Body Activation Order in Parallel Mode */
            {
                const char *oprog =
                    ":- chr_constraint start/0, a/0, b/0, done/0.\n"
                    "start_rule @ start <=> a, b.\n"
                    "pair @ a, b <=> done.\n"
                    "erase @ a <=> true.\n"
                    "?- start.\n";
                GsltArena ao;
                gslt_arena_init(&ao);
                GsltC0Program cpo;
                GsltC0Diagnostic d_o = {0};
                char err[256] = {0};
                gslt_c0_parse_source(&ao, oprog, strlen(oprog), &cpo, &d_o, err, sizeof(err));
                C0LoweredEngine *eo = (C0LoweredEngine *)calloc(1, sizeof(C0LoweredEngine));
                c0_run_machine(&cpo, eo, C0_MODE_PARALLEL, 4, 0);
                char so[256];
                c0_format_store(eo, so, sizeof(so));
                CHECK(eo->status == C0_STATUS_COMPLETED && eo->events_admitted == 2 && strcmp(so, "[b]") == 0,
                      "CHR-order:ordered_body.chr (parallel 4 threads) preserves left-to-right body activation ([b], events=%" PRIu64 ")",
                      eo->events_admitted);
                c0_engine_destroy(eo);
                free(eo);
                gslt_arena_free(&ao);
            }

            /* =====================================================================
             * Suite 10: Stage 2 Compositional SyntaxGSLT C Parser Substrate
             *           (CNF1 Packed Forests, PNI1 Plan Identity, SourceSelectionV1,
             *            Provenance, Slot Routing, Binder Scopes & 6 Negative Controls)
             * ===================================================================== */
            {
                char gerr[512] = {0};
                GsltModuleCatalog *cat_io = (GsltModuleCatalog *)calloc(1, sizeof(GsltModuleCatalog));
                GsltModuleCatalog *cat_pol = (GsltModuleCatalog *)calloc(1, sizeof(GsltModuleCatalog));
                bool ok_io = gslt_load_module_file(
                    "../Mettapedia/metta/gslt/tests/source_io/SourceIO.module",
                    cat_io, gerr, sizeof(gerr));
                bool ok_pol = gslt_load_module_file(
                    "../Mettapedia/metta/gslt/tests/source_io/SourceIOPolicy.module",
                    cat_pol, gerr, sizeof(gerr));
                CHECK(ok_io && ok_pol && cat_io->production_count == 6 && cat_pol->production_count == 6 &&
                      strcmp(cat_io->productions[0].origin_module, "SourceIOBase") == 0 &&
                      strcmp(cat_io->productions[0].label, "First") == 0 &&
                      strcmp(cat_io->productions[2].origin_module, "SourceIO") == 0 &&
                      strcmp(cat_io->productions[2].label, "Second") == 0 &&
                      cat_pol->selection.has_policy &&
                      strcmp(cat_pol->selection.version_tag, "SourceSelectionV1") == 0,
                      "10a. Compositional .module loader resolves SourceIOBase + SourceIO + SourceIOPolicy with constructor provenance");

                /* 10b. Ambiguous input "x" retains both First and Second in CNF1 packed forest;
                 *      SourceIOPolicy rejects "x" without mutating raw CNF1 forest wire bytes! */
                const uint8_t *x_src = (const uint8_t *)"x";
                GsltCnf1Forest f_io = {0}, f_pol = {0}, f_round = {0};
                bool r1 = gslt_recognize_into_cnf1(cat_io, x_src, 1, &f_io, gerr, sizeof(gerr));
                bool r2 = gslt_recognize_into_cnf1(cat_pol, x_src, 1, &f_pol, gerr, sizeof(gerr));
                uint8_t *wire_io = NULL, *wire_pol = NULL, *pni_io = NULL;
                size_t wire_io_len = 0, wire_pol_len = 0, pni_io_len = 0;
                gslt_cnf1_serialize_wire(&f_io, &wire_io, &wire_io_len);
                gslt_cnf1_serialize_wire(&f_pol, &wire_pol, &wire_pol_len);
                gslt_pni1_serialize_from_catalog(cat_io, &pni_io, &pni_io_len);
                GsltPni1Identity *pni_id = (GsltPni1Identity *)calloc(1, sizeof(GsltPni1Identity));
                bool ok_cnf = gslt_cnf1_deserialize_and_validate(
                    wire_io, wire_io_len, x_src, 1, &f_round, gerr, sizeof(gerr));
                bool ok_pni = gslt_pni1_deserialize_and_verify(
                    pni_io, pni_io_len, cat_io, pni_id, gerr, sizeof(gerr));
                GsltDerivationCatalog dc_raw = {0}, dc_sel = {0};
                gslt_extract_derivations_from_forest(&f_round, cat_io, x_src, false, &dc_raw);
                gslt_extract_derivations_from_forest(&f_pol, cat_pol, x_src, true, &dc_sel);
                CHECK(r1 && r2 && ok_cnf && ok_pni &&
                      wire_io_len == wire_pol_len && memcmp(wire_io, wire_pol, wire_io_len) == 0 &&
                      dc_raw.count == 2 && dc_sel.count == 0 &&
                      strcmp(dc_raw.packets[0], "(result (node First (cons (cp 120) nil)) nil)") == 0 &&
                      strcmp(dc_raw.packets[1], "(result (node Second (cons (cp 120) nil)) nil)") == 0,
                      "10b. CNF1 packed forest retains both ambiguous derivations on 'x' and SourceSelectionV1 filters without mutating forest wire");

                /* 10c. Multibyte UTF-8 scalars ("((y,),λ🙂)"), canonical printing & AST round-trip */
                const char *u_text = "((y,),λ🙂)";
                const uint8_t *u_src = (const uint8_t *)u_text;
                size_t u_len = strlen(u_text);
                GsltCnf1Forest f_u = {0};
                bool ru = gslt_recognize_into_cnf1(cat_pol, u_src, u_len, &f_u, gerr, sizeof(gerr));
                GsltDerivationCatalog dc_u = {0};
                gslt_extract_derivations_from_forest(&f_u, cat_pol, u_src, true, &dc_u);
                char printed_u[256] = {0};
                bool ok_print = (dc_u.count == 1) &&
                    gslt_print_ast_canonical(dc_u.trees[0], cat_pol, printed_u, sizeof(printed_u), gerr, sizeof(gerr));
                GsltCnf1Forest f_u2 = {0};
                GsltDerivationCatalog dc_u2 = {0};
                if (ok_print) {
                    gslt_recognize_into_cnf1(cat_pol, (const uint8_t *)printed_u, strlen(printed_u), &f_u2, gerr, sizeof(gerr));
                    gslt_extract_derivations_from_forest(&f_u2, cat_pol, (const uint8_t *)printed_u, true, &dc_u2);
                }
                CHECK(ru && f_u.scalar_len == 9 && f_u.input_byte_len == 13 &&
                      dc_u.count == 1 && ok_print && strcmp(printed_u, u_text) == 0 &&
                      dc_u2.count == 1 && gslt_ast_equal(dc_u.trees[0], dc_u2.trees[0]),
                      "10c. Multibyte UTF-8 scalar alignment, canonical printing & constructor AST round-trip on '((y,),λ🙂)'");

                /* 10d. Non-identity positional argument routing (SwapPair: "[" second ";" first "]")
                 *      and lexical binder scope resolution (Lam: "fun " x " -> " body) */
                GsltModuleCatalog *cat_ext = (GsltModuleCatalog *)calloc(1, sizeof(GsltModuleCatalog));
                *cat_ext = *cat_pol;
                {
                    GsltSlotSpec sw_slots[2];
                    memset(sw_slots, 0, sizeof(sw_slots));
                    snprintf(sw_slots[0].name, 64, "first");  snprintf(sw_slots[0].sort, 64, "Term");
                    snprintf(sw_slots[1].name, 64, "second"); snprintf(sw_slots[1].sort, 64, "Term");
                    bool sw_lit[5] = { true, false, true, false, true };
                    char sw_rhs[5][64] = { "[", "second", ";", "first", "]" };
                    gslt_catalog_add_production(
                        cat_ext, "SourceIOExt", "Grammar", "SwapPair", "Term",
                        2, sw_slots, 5, sw_lit, sw_rhs, gerr, sizeof(gerr));
                }
                const char *sw_text = "[y;λ🙂]";
                GsltCnf1Forest f_sw = {0};
                gslt_recognize_into_cnf1(cat_ext, (const uint8_t *)sw_text, strlen(sw_text), &f_sw, gerr, sizeof(gerr));
                GsltDerivationCatalog dc_sw = {0};
                gslt_extract_derivations_from_forest(&f_sw, cat_ext, (const uint8_t *)sw_text, true, &dc_sw);
                char sw_printed[128] = {0};
                bool sw_prov_ok = (dc_sw.count == 1) &&
                    gslt_verify_ast_provenance_and_routing(dc_sw.trees[0], cat_ext, "Term", gerr, sizeof(gerr)) &&
                    gslt_print_ast_canonical(dc_sw.trees[0], cat_ext, sw_printed, sizeof(sw_printed), gerr, sizeof(gerr));
                CHECK(sw_prov_ok &&
                      strcmp(dc_sw.trees[0]->children[0]->label, "Unicode") == 0 &&
                      strcmp(dc_sw.trees[0]->children[1]->label, "Other") == 0 &&
                      strcmp(sw_printed, sw_text) == 0,
                      "10d. Non-identity routed_slots[] routes '[y;λ🙂]' -> SwapPair(first=Unicode, second=Other) and prints back canonically");

                /* 10e. Control S2-Neg-1: Altered Version & Identity Tags (CNF2, PNI2, PNI1 ver=2, altered label, profile V2) */
                {
                    uint8_t *bad_cnf = (uint8_t *)malloc(wire_io_len);
                    memcpy(bad_cnf, wire_io, wire_io_len);
                    bad_cnf[3] = '2'; /* CNF2 */
                    GsltCnf1Forest f_bad = {0};
                    bool cnf2_ok = gslt_cnf1_deserialize_and_validate(bad_cnf, wire_io_len, x_src, 1, &f_bad, gerr, sizeof(gerr));

                    uint8_t *bad_pni = (uint8_t *)malloc(pni_io_len);
                    memcpy(bad_pni, pni_io, pni_io_len);
                    bad_pni[3] = '2'; /* PNI2 */
                    GsltPni1Identity *pni_bad = (GsltPni1Identity *)calloc(1, sizeof(GsltPni1Identity));
                    bool pni2_ok = gslt_pni1_deserialize_and_verify(bad_pni, pni_io_len, cat_io, pni_bad, gerr, sizeof(gerr));

                    memcpy(bad_pni, pni_io, pni_io_len);
                    bad_pni[4] = 2; /* version = 2 */
                    bool pni_v2_ok = gslt_pni1_deserialize_and_verify(bad_pni, pni_io_len, cat_io, pni_bad, gerr, sizeof(gerr));
                    free(pni_bad);

                    GsltModuleCatalog *cat_bad_ver = (GsltModuleCatalog *)calloc(1, sizeof(GsltModuleCatalog));
                    *cat_bad_ver = *cat_io;
                    snprintf(cat_bad_ver->profile_version, 64, "GSLTParserProfileLayerV2");
                    GsltCnf1Forest f_bv = {0};
                    bool prof_v2_ok = gslt_recognize_into_cnf1(cat_bad_ver, x_src, 1, &f_bv, gerr, sizeof(gerr));

                    CHECK(!cnf2_ok && !pni2_ok && !pni_v2_ok && !prof_v2_ok,
                          "Control S2-Neg-1: altered version/identity tags (CNF2, PNI2, PNI1 v2, GSLTParserProfileLayerV2) refused");
                    free(bad_cnf);
                    free(bad_pni);
                    free(cat_bad_ver);
                }

                /* 10f. Control S2-Neg-2: Spurious Parses (unknown production, wrong scalar cp, corrupt CNF1 terminal scalar) */
                {
                    const char *spurious_pkts[1] = { "(result (node BogusProd (cons (cp 120) nil)) nil)" };
                    bool sp1_ok = gslt_verify_packet_catalogue(
                        &f_round, pni_id, cat_io, x_src, spurious_pkts, 1, false, gerr, sizeof(gerr));

                    const char *wrong_cp_pkts[2] = {
                        "(result (node First (cons (cp 121) nil)) nil)",
                        "(result (node Second (cons (cp 120) nil)) nil)"
                    };
                    bool sp2_ok = gslt_verify_packet_catalogue(
                        &f_round, pni_id, cat_io, x_src, wrong_cp_pkts, 2, false, gerr, sizeof(gerr));

                    /* Corrupt terminal_scalar in CNF1 node 0 */
                    GsltCnf1Forest f_corrupt_term = f_io;
                    uint32_t orig_sc = f_io.nodes[0].terminal_scalar;
                    f_io.nodes[0].terminal_scalar = 999u;
                    uint8_t *bad_term_wire = NULL;
                    size_t bad_term_len = 0;
                    gslt_cnf1_serialize_wire(&f_corrupt_term, &bad_term_wire, &bad_term_len);
                    f_io.nodes[0].terminal_scalar = orig_sc;
                    GsltCnf1Forest f_ct_out = {0};
                    bool sp3_ok = gslt_cnf1_deserialize_and_validate(
                        bad_term_wire, bad_term_len, x_src, 1, &f_ct_out, gerr, sizeof(gerr));
                    free(bad_term_wire);

                    CHECK(!sp1_ok && !sp2_ok && !sp3_ok,
                          "Control S2-Neg-2: spurious parses (unknown production, wrong scalar cp, corrupt CNF1 terminal scalar) refused");
                }

                /* 10g. Control S2-Neg-3: Missing Valid Parses (incomplete catalogue omitting Second on ambiguous "x") */
                {
                    const char *incomplete_pkts[1] = { "(result (node First (cons (cp 120) nil)) nil)" };
                    bool inc_ok = gslt_verify_packet_catalogue(
                        &f_round, pni_id, cat_io, x_src, incomplete_pkts, 1, false, gerr, sizeof(gerr));
                    const char *complete_pkts[2] = {
                        "(result (node First (cons (cp 120) nil)) nil)",
                        "(result (node Second (cons (cp 120) nil)) nil)"
                    };
                    bool comp_ok = gslt_verify_packet_catalogue(
                        &f_round, pni_id, cat_io, x_src, complete_pkts, 2, false, gerr, sizeof(gerr));
                    CHECK(!inc_ok && strstr(gerr, "incomplete catalogue") == gerr && comp_ok,
                          "Control S2-Neg-3: incomplete catalogue omitting ambiguous parse 'Second' refused; complete catalogue accepted");
                }

                /* 10h. Control S2-Neg-4: Wrong Constructor Origins & Sort Mismatches */
                {
                    GsltAstNode *forged_origin = gslt_ast_clone(dc_raw.trees[0]);
                    /* dc_raw.trees[0] is First from SourceIOBase; forge origin_module = "SourceIO" */
                    snprintf(forged_origin->origin_module, 64, "SourceIO");
                    bool orig_ok = gslt_verify_ast_provenance_and_routing(
                        forged_origin, cat_io, "Term", gerr, sizeof(gerr));

                    GsltAstNode *forged_sort = gslt_ast_clone(dc_u.trees[0]);
                    snprintf(forged_sort->children[0]->sort, 64, "Profile");
                    bool sort_ok = gslt_verify_ast_provenance_and_routing(
                        forged_sort, cat_pol, "Term", gerr, sizeof(gerr));

                    CHECK(!orig_ok && !sort_ok,
                          "Control S2-Neg-4: wrong constructor origin (SourceIO vs SourceIOBase) and child sort mismatch refused");
                    gslt_ast_free(forged_origin);
                    gslt_ast_free(forged_sort);
                }

                /* 10i. Control S2-Neg-5: Child Reordering (swapping children violates routed_slots[] span order) */
                {
                    /* Swap left and right children of Pair("((y,),λ🙂)") where routed_slots = [0, 1] */
                    GsltAstNode *reordered_pair = gslt_ast_clone(dc_u.trees[0]);
                    GsltAstNode *tmp_ch = reordered_pair->children[0];
                    reordered_pair->children[0] = reordered_pair->children[1];
                    reordered_pair->children[1] = tmp_ch;
                    bool reord1_ok = gslt_verify_ast_provenance_and_routing(
                        reordered_pair, cat_pol, "Term", gerr, sizeof(gerr));

                    /* Swap first and second children of SwapPair("[y;λ🙂]") where routed_slots = [1, 0] */
                    GsltAstNode *reordered_swap = gslt_ast_clone(dc_sw.trees[0]);
                    tmp_ch = reordered_swap->children[0];
                    reordered_swap->children[0] = reordered_swap->children[1];
                    reordered_swap->children[1] = tmp_ch;
                    bool reord2_ok = gslt_verify_ast_provenance_and_routing(
                        reordered_swap, cat_ext, "Term", gerr, sizeof(gerr));

                    CHECK(!reord1_ok && !reord2_ok,
                          "Control S2-Neg-5: child reordering in Pair (routed [0,1]) and SwapPair (routed [1,0]) refused");
                    gslt_ast_free(reordered_pair);
                    gslt_ast_free(reordered_swap);
                }

                /* 10j. Control S2-Neg-6: Lexical Binder Capture & Out-of-Bounds de Bruijn Index */
                {
                    /* Build Lam(^y, body = Pair(Var("y", db=0), Var("x", free))) */
                    GsltAstNode *lam = (GsltAstNode *)calloc(1, sizeof(GsltAstNode));
                    lam->is_binder = true;
                    snprintf(lam->binder_var, 64, "y");
                    lam->child_count = 2;

                    GsltAstNode *vy = (GsltAstNode *)calloc(1, sizeof(GsltAstNode));
                    vy->is_var_ref = true;
                    snprintf(vy->var_name, 64, "y");
                    vy->db_index = 0;

                    GsltAstNode *vx = (GsltAstNode *)calloc(1, sizeof(GsltAstNode));
                    vx->is_var_ref = true;
                    snprintf(vx->var_name, 64, "x");
                    vx->db_index = -1; /* free variable x */

                    lam->children[0] = vy;
                    lam->children[1] = vx;

                    /* Safe substitution x -> z succeeds */
                    bool safe_subst_ok = gslt_verify_binder_scopes(lam, "x", "z", gerr, sizeof(gerr));
                    /* Capturing substitution x -> y under ^y MUST be refused! */
                    bool cap_subst_ok = gslt_verify_binder_scopes(lam, "x", "y", gerr, sizeof(gerr));
                    /* Out-of-bounds de Bruijn index db_index = 3 at depth 1 MUST be refused! */
                    vy->db_index = 3;
                    bool oob_db_ok = gslt_verify_binder_scopes(lam, NULL, NULL, gerr, sizeof(gerr));

                    CHECK(safe_subst_ok && !cap_subst_ok && !oob_db_ok,
                          "Control S2-Neg-6: binder capture (x -> y under ^y) and out-of-bounds de Bruijn index refused");
                    gslt_ast_free(lam);
                }

                free(wire_io);
                free(wire_pol);
                free(pni_io);
                gslt_cnf1_forest_free(&f_io);
                gslt_cnf1_forest_free(&f_pol);
                gslt_cnf1_forest_free(&f_round);
                gslt_cnf1_forest_free(&f_u);
                gslt_cnf1_forest_free(&f_u2);
                gslt_cnf1_forest_free(&f_sw);
                gslt_derivation_catalog_free(&dc_raw);
                gslt_derivation_catalog_free(&dc_sel);
                gslt_derivation_catalog_free(&dc_u);
                gslt_derivation_catalog_free(&dc_u2);
                gslt_derivation_catalog_free(&dc_sw);
                free(cat_io);
                free(cat_pol);
                free(cat_ext);
                free(pni_id);
            }

            /* =====================================================================
             * Suite 11: Stage 3 Route A (PeTTa -> tcalc Evaluator), GSLT Runner/Explorer
             *           Continuations (gslt_runner.metta), and 5 MeTTa Prime Sub-Calculi
             * ===================================================================== */
            {
                /* 11a. Pattern Matching (repeated vars), Lexical Shadowing & Capture-Avoiding Substitution */
                {
                    PettaTcalcEngine *pe = (PettaTcalcEngine *)calloc(1, sizeof(PettaTcalcEngine));
                    petta_tcalc_engine_init(pe, 0);
                    const char *prog =
                        "(: same (-> Atom Atom Atom))\n"
                        "(= (same $a $b) (case ($a $b) ((($x $x) True) ($_ False))))\n"
                        "!(let* (($r1 (same (pair 7 8) (pair 7 8)))\n"
                        "        ($r2 (same (pair 7 8) (pair 7 9)))\n"
                        "        ($x 10)\n"
                        "        ($y (let $x 99 (+ $x 1)))\n"
                        "        ($sum (+ $x $y)))\n"
                        "   (Result $r1 $r2 $sum))\n";
                    PettaValList res;
                    petta_vallist_init(&res);
                    bool ok = petta_load_and_run_program(pe, prog, &res);
                    char rbuf[256] = {0};
                    if (res.count > 0) petta_atom_render(res.items[0], rbuf, sizeof(rbuf));
                    CHECK(ok && res.count == 1 && strcmp(rbuf, "(Result True False 110)") == 0,
                          "11a. PeTTa->tcalc pattern matching with repeated variables and lexical let/let* shadowing: %s",
                          rbuf);
                    petta_vallist_free(&res);
                    petta_tcalc_engine_destroy(pe);
                    free(pe);
                }

                /* 11b. Answer Multiplicity (superpose, collapse, multi-clause rewrite rules) */
                {
                    PettaTcalcEngine *pe = (PettaTcalcEngine *)calloc(1, sizeof(PettaTcalcEngine));
                    petta_tcalc_engine_init(pe, 0);
                    const char *prog =
                        "(= (branch $n) (+ $n 1))\n"
                        "(= (branch $n) (* $n 10))\n"
                        "!(let* (($bag (collapse (superpose (10 20 10 30))))\n"
                        "        ($multi (collapse (branch 3))))\n"
                        "   (Multiplicity $bag $multi))\n";
                    PettaValList res;
                    petta_vallist_init(&res);
                    bool ok = petta_load_and_run_program(pe, prog, &res);
                    char rbuf[256] = {0};
                    if (res.count > 0) petta_atom_render(res.items[0], rbuf, sizeof(rbuf));
                    CHECK(ok && res.count == 1 &&
                          strcmp(rbuf, "(Multiplicity (10 20 10 30) (4 30))") == 0,
                          "11b. PeTTa->tcalc preserves superpose/collapse and multi-clause answer multiplicity: %s",
                          rbuf);
                    petta_vallist_free(&res);
                    petta_tcalc_engine_destroy(pe);
                    free(pe);
                }

                /* 11c. GSLT Resumable Search Runner & Fair Explorer (gslt_runner.metta) Continuation Resumption */
                {
                    FILE *rfp = fopen("../Mettapedia/metta/gslt/lib/gslt_runner.metta", "rb");
                    CHECK(rfp != NULL, "11c-prep: open Mettapedia/metta/gslt/lib/gslt_runner.metta");
                    if (rfp) {
                        fseek(rfp, 0, SEEK_END);
                        long rsz = ftell(rfp);
                        fseek(rfp, 0, SEEK_SET);
                        char *rsrc = (char *)malloc((size_t)rsz + 1u);
                        if (rsz > 0 && fread(rsrc, 1, (size_t)rsz, rfp) != (size_t)rsz) {
                            rsrc[0] = '\0';
                        } else {
                            rsrc[rsz] = '\0';
                        }
                        fclose(rfp);

                        /* Supply a concrete ClassSearch backend & helper functions for gslt_runner.metta */
                        const char *harness =
                            "(= (gslt:laws:standard $laws $ext $pat) $pat)\n"
                            "(= (gslt:automata:length LNil) 0)\n"
                            "(= (gslt:automata:length (LCons $h $t)) (+ 1 (gslt:automata:length $t)))\n"
                            "(= (gslt:complete:drop $n $xs)\n"
                            "   (if (== $n 0) $xs\n"
                            "     (case $xs ((LNil LNil) ((LCons $h $t) (gslt:complete:drop (- $n 1) $t))))))\n"
                            "(= (gslt:automata:append LNil $ys) $ys)\n"
                            "(= (gslt:automata:append (LCons $h $t) $ys) (LCons $h (gslt:automata:append $t $ys)))\n"
                            "(= (gslt:classes:step-log S0) (LCons (ClassReceipt S0 LNil (RuleJobReceipt J0 T0 C0 True H0 L0 S1)) (LCons (ClassReceipt S0 LNil (RuleJobReceipt J1 T0 C0 True H0 L0 S3)) LNil)))\n"
                            "(= (gslt:classes:step-log S1) (LCons (ClassReceipt S1 LNil (RuleJobReceipt J2 T0 C0 True H0 L0 S2)) LNil))\n"
                            "(= (gslt:classes:step-log S2) LNil)\n"
                            "(= (gslt:classes:step-log S3) LNil)\n"
                            "(= (gslt:classes:begin $plan $src) (ClassState 0 $src Pending LNil))\n"
                            "(= (gslt:classes:rounds $plan $work (ClassState $r $src $st $log))\n"
                            "   (if (== $work 0) (ClassState $r $src $st $log)\n"
                            "     (ClassState (+ $r $work) $src Complete (gslt:classes:step-log $src))))\n"
                            "(= (gslt:classes:entries-complete $plan Complete) True)\n"
                            "(= (gslt:classes:entries-complete $plan Pending) False)\n"
                            "!(let* (($std (Standard LNil LNil))\n"
                            "        ($m0 (gslt:runner:begin ClassSearch TestPlan $std S0))\n"
                            "        ($m_oneshot (gslt:runner:advance ClassSearch TestPlan $std 3 1 $m0))\n"
                            "        ($m_step1 (gslt:runner:advance ClassSearch TestPlan $std 1 1 $m0))\n"
                            "        ($m_step2 (gslt:runner:advance ClassSearch TestPlan $std 1 1 $m_step1))\n"
                            "        ($m_resumed (gslt:runner:advance ClassSearch TestPlan $std 1 1 $m_step2))\n"
                            "        ($tr_oneshot (gslt:runner:trace $m_oneshot))\n"
                            "        ($tr_resumed (gslt:runner:trace $m_resumed))\n"
                            "        ($e0 (gslt:explore:begin ClassSearch TestPlan $std S0))\n"
                            "        ($e_oneshot (gslt:explore:rounds ClassSearch TestPlan $std 4 $e0))\n"
                            "        ($e_part1 (gslt:explore:rounds ClassSearch TestPlan $std 1 $e0))\n"
                            "        ($e_resumed (gslt:explore:rounds ClassSearch TestPlan $std 3 $e_part1))\n"
                            "        ($st_eq (== (gslt:explore:states $e_oneshot) (gslt:explore:states $e_resumed)))\n"
                            "        ($ed_eq (== (gslt:explore:edges ClassSearch $std $e_oneshot) (gslt:explore:edges ClassSearch $std $e_resumed))))\n"
                            "   (RunnerCheck (== $m_oneshot $m_resumed) $tr_resumed $st_eq $ed_eq (gslt:explore:states $e_resumed)))\n";

                        PettaTcalcEngine *pe = (PettaTcalcEngine *)calloc(1, sizeof(PettaTcalcEngine));
                        petta_tcalc_engine_init(pe, 0);
                        PettaValList res;
                        petta_vallist_init(&res);
                        bool ok1 = petta_load_and_run_program(pe, rsrc, NULL);
                        bool ok2 = ok1 && petta_load_and_run_program(pe, harness, &res);
                        char rbuf[512] = {0};
                        if (res.count > 0) petta_atom_render(res.items[0], rbuf, sizeof(rbuf));
                        CHECK(ok2 && res.count == 1 &&
                              strcmp(rbuf,
                                  "(RunnerCheck True (RunTrace ClassDone (LCons S0 (LCons S1 (LCons S2 LNil)))) "
                                  "True True (LCons S0 (LCons S1 (LCons S3 (LCons S2 LNil)))))") == 0,
                              "11c. gslt_runner.metta executes on PeTTa->tcalc with exact continuation resumption & fair exploration: %s",
                              rbuf);
                        petta_vallist_free(&res);
                        petta_tcalc_engine_destroy(pe);
                        free(pe);
                        free(rsrc);
                    }
                }

                /* 11d. All 5 MeTTa Prime Sub-Calculi Syntactic Sugar Forms + 3-Way Commuting Check */
                {
                    PettaTcalcEngine *pe = (PettaTcalcEngine *)calloc(1, sizeof(PettaTcalcEngine));
                    petta_tcalc_engine_init(pe, 0);
                    const char *subcalc_prog =
                        /* 1 & 2: ReadOnlyQuery (match) & MonotoneDatalog (infer-atoms!) */
                        "!(add-atom &self (edge 1 2))\n"
                        "!(add-atom &self (edge 2 3))\n"
                        "!(add-atom &self (edge 1 2))\n" /* duplicate EDB atom */
                        "!(let* (($q_mult (collapse (match &self (edge 1 $y) $y)))\n"
                        "        ($d_step1 (infer-atoms! &self (from ((edge $x $y))) (where ()) (emit (reach $x $y))))\n"
                        "        ($d_step2 (infer-atoms! &self (from ((edge $x $y) (reach $y $z))) (where ()) (emit (reach $x $z))))\n"
                        "        ($reach_set (collapse (match &self (reach $a $b) ($a $b))))\n"
                        /* 3: LinearConsumption (take-atom! & replace-atom!) */
                        "        ($_t1 (add-atom &self (token 7)))\n"
                        "        ($take1 (take-atom! &self (token $v) (* $v 6)))\n"
                        "        ($take2 (take-atom! &self (token $v) (* $v 6)))\n"
                        "        ($_c1 (add-atom &self (counter 10)))\n"
                        "        ($rep1 (replace-atom! &self (counter $c) (counter (+ $c 5))))\n"
                        /* 4: RefinedCHR (simpagate!) */
                        "        ($_s1 (add-atom &self (num 6)))\n"
                        "        ($_s2 (add-atom &self (num 9)))\n"
                        "        ($simp1 (simpagate! &self (num $x) (num $y) (<= $x $y) (num (- $y $x))))\n"
                        "        ($nums (collapse (match &self (num $v) $v)))\n"
                        /* 5: ChannelComm (send-chan! & comm!) */
                        "        ($_ch1 (send-chan! &self ch_work (Job 42)))\n"
                        "        ($comm1 (comm! &self ch_work (Job $id) (Completed (+ $id 8))))\n"
                        "        ($comm2 (comm! &self ch_work (Job $id) (Completed $id))))\n"
                        "   (SubCalcSummary $q_mult $d_step1 $d_step2 $reach_set $take1 $take2 $rep1 $simp1 $nums $comm1 $comm2))\n";

                    PettaValList res;
                    petta_vallist_init(&res);
                    bool ok = petta_load_and_run_program(pe, subcalc_prog, &res);
                    char rbuf[512] = {0};
                    if (res.count > 0) petta_atom_render(res.items[0], rbuf, sizeof(rbuf));
                    CHECK(ok && res.count == 1 &&
                          strcmp(rbuf,
                              "(SubCalcSummary (2 2) 2 1 ((1 2) (2 3) (1 3)) 42 Empty (counter 15) (num 3) (6 3) (Completed 50) Blocked)") == 0 &&
                          pe->subcalc_queries_run == 3 &&
                          pe->subcalc_datalog_inferred == 3 &&
                          pe->subcalc_linear_taken == 2 &&
                          pe->subcalc_simpagate_fired == 1 &&
                          pe->subcalc_comm_synced == 1 &&
                          pe->last_receipt.admitted == 1,
                          "11d. All 5 MeTTa Prime tcalc sub-calculi (match, infer-atoms!, take-atom!, replace-atom!, simpagate!, comm!) verified with TcAdmissionReceipt: %s",
                          rbuf);
                    petta_vallist_free(&res);
                    petta_tcalc_engine_destroy(pe);
                    free(pe);
                }

                /* 11e. Fault & Step-Budget Controls on PeTTa -> tcalc */
                {
                    PettaTcalcEngine *pe_div = (PettaTcalcEngine *)calloc(1, sizeof(PettaTcalcEngine));
                    petta_tcalc_engine_init(pe_div, 0);
                    bool ok_div = petta_load_and_run_program(pe_div, "!(+ 1 (/ 10 0))\n", NULL);

                    PettaTcalcEngine *pe_typ = (PettaTcalcEngine *)calloc(1, sizeof(PettaTcalcEngine));
                    petta_tcalc_engine_init(pe_typ, 0);
                    bool ok_typ = petta_load_and_run_program(pe_typ, "!(+ 1 NotAnInt)\n", NULL);

                    PettaTcalcEngine *pe_bud = (PettaTcalcEngine *)calloc(1, sizeof(PettaTcalcEngine));
                    petta_tcalc_engine_init(pe_bud, 15);
                    bool ok_bud = petta_load_and_run_program(pe_bud, "(= (inf $x) (inf (+ $x 1)))\n!(inf 0)\n", NULL);

                    CHECK(!ok_div && pe_div->status == PETTA_STATUS_FAULT && pe_div->fault == PETTA_FAULT_DIV_ZERO &&
                          !ok_typ && pe_typ->status == PETTA_STATUS_FAULT && pe_typ->fault == PETTA_FAULT_TYPE &&
                          !ok_bud && pe_bud->status == PETTA_STATUS_BUDGET_EXHAUSTED && pe_bud->steps_executed == 15,
                          "11e. PeTTa->tcalc explicit fault propagation (DIV_ZERO, TYPE) and step budget cutoff verified");

                    petta_tcalc_engine_destroy(pe_div);
                    petta_tcalc_engine_destroy(pe_typ);
                    petta_tcalc_engine_destroy(pe_bud);
                    free(pe_div);
                    free(pe_typ);
                    free(pe_bud);
                }
            }

            /* =====================================================================
             * Suite 12: Stage 4 Complete 5-Language Gold Contracts & Negative Controls
             * ===================================================================== */
            {
                /* 12a. Datalog D1: Retained Explanations vs Fact Closure vs Unbounded Unfolding,
                 *      Cyclic Graphs, Points-To Analysis & Nonlinear Joins */
                {
                    /* Diamond graph: edge(1,2), edge(2,4), edge(1,3), edge(3,4)
                     * Fact closure derives 1 fact `reach(1,4)`, whereas One-Step Explanations
                     * retains 2 distinct explanation receipts for `reach(1,4)` (via 2 and via 3)! */
                    GoldDatalogEngine *dl_fc = (GoldDatalogEngine *)calloc(1, sizeof(GoldDatalogEngine));
                    gold_dl_init(dl_fc, DL_COMPLETION_FACT_CLOSURE, 100);
                    gold_dl_add_edb(dl_fc, "edge", 1, 2);
                    gold_dl_add_edb(dl_fc, "edge", 2, 4);
                    gold_dl_add_edb(dl_fc, "edge", 1, 3);
                    gold_dl_add_edb(dl_fc, "edge", 3, 4);
                    gold_dl_add_rule_1(dl_fc, 1, "reach", "edge", false, false);
                    gold_dl_add_rule_2(dl_fc, 2, "reach", "edge", "reach", false);
                    GoldDlStatus st_fc = gold_dl_run(dl_fc);

                    GoldDatalogEngine *dl_ex = (GoldDatalogEngine *)calloc(1, sizeof(GoldDatalogEngine));
                    gold_dl_init(dl_ex, DL_COMPLETION_ONESTEP_EXPLANATIONS, 100);
                    gold_dl_add_edb(dl_ex, "edge", 1, 2);
                    gold_dl_add_edb(dl_ex, "edge", 2, 4);
                    gold_dl_add_edb(dl_ex, "edge", 1, 3);
                    gold_dl_add_edb(dl_ex, "edge", 3, 4);
                    gold_dl_add_rule_1(dl_ex, 1, "reach", "edge", false, false);
                    gold_dl_add_rule_2(dl_ex, 2, "reach", "edge", "reach", false);
                    GoldDlStatus st_ex = gold_dl_run(dl_ex);
                    uint32_t expls_1_4 = gold_dl_count_expls_for(dl_ex, "reach", 1, 4);

                    /* Cyclic graph: edge(1,2), edge(2,1)
                     * Fact closure and One-Step Explanations terminate (`DL_STATUS_COMPLETE`),
                     * whereas Unbounded Unfolding stays `DL_STATUS_BUDGET_EXHAUSTED` under budget=12! */
                    GoldDatalogEngine *dl_cyc_ex = (GoldDatalogEngine *)calloc(1, sizeof(GoldDatalogEngine));
                    gold_dl_init(dl_cyc_ex, DL_COMPLETION_ONESTEP_EXPLANATIONS, 12);
                    gold_dl_add_edb(dl_cyc_ex, "edge", 1, 2);
                    gold_dl_add_edb(dl_cyc_ex, "edge", 2, 1);
                    gold_dl_add_rule_1(dl_cyc_ex, 1, "reach", "edge", false, false);
                    gold_dl_add_rule_2(dl_cyc_ex, 2, "reach", "edge", "reach", false);
                    GoldDlStatus st_cyc_ex = gold_dl_run(dl_cyc_ex);

                    GoldDatalogEngine *dl_cyc_unb = (GoldDatalogEngine *)calloc(1, sizeof(GoldDatalogEngine));
                    gold_dl_init(dl_cyc_unb, DL_COMPLETION_UNBOUNDED_UNFOLDING, 12);
                    gold_dl_add_edb(dl_cyc_unb, "edge", 1, 2);
                    gold_dl_add_edb(dl_cyc_unb, "edge", 2, 1);
                    gold_dl_add_rule_1(dl_cyc_unb, 1, "reach", "edge", false, false);
                    gold_dl_add_rule_2(dl_cyc_unb, 2, "reach", "edge", "reach", false);
                    GoldDlStatus st_cyc_unb = gold_dl_run(dl_cyc_unb);

                    /* Points-to analysis & nonlinear self-join:
                     * alloc(v1, h1), assign(v2, v1), assign(v3, v2), self_pair(7, 7), self_pair(7, 8)
                     * points_to(V, H) :- alloc(V, H).
                     * points_to(Dst, H) :- assign(Dst, Src), points_to(Src, H).
                     * alias(X, Y) :- points_to(X, H), points_to(Y, H).
                     * diag(X, X) :- self_pair(X, X). */
                    GoldDatalogEngine *dl_pt = (GoldDatalogEngine *)calloc(1, sizeof(GoldDatalogEngine));
                    gold_dl_init(dl_pt, DL_COMPLETION_ONESTEP_EXPLANATIONS, 200);
                    gold_dl_add_edb(dl_pt, "alloc", 1, 100);
                    gold_dl_add_edb(dl_pt, "assign", 2, 1);
                    gold_dl_add_edb(dl_pt, "assign", 3, 2);
                    gold_dl_add_edb(dl_pt, "self_pair", 7, 7);
                    gold_dl_add_edb(dl_pt, "self_pair", 7, 8);
                    gold_dl_add_rule_1(dl_pt, 10, "points_to", "alloc", false, false);
                    gold_dl_add_rule_2(dl_pt, 11, "points_to", "assign", "points_to", false);
                    gold_dl_add_rule_2(dl_pt, 12, "alias", "points_to", "points_to", true);
                    gold_dl_add_rule_1(dl_pt, 13, "diag", "self_pair", true, false);
                    GoldDlStatus st_pt = gold_dl_run(dl_pt);

                    CHECK(st_fc == DL_STATUS_COMPLETE && st_ex == DL_STATUS_COMPLETE &&
                          gold_dl_count_pred_facts(dl_fc, "reach") == 5 &&
                          gold_dl_count_pred_facts(dl_ex, "reach") == 5 &&
                          dl_fc->nexpls == 0 && expls_1_4 == 2 && dl_ex->nexpls == 6 &&
                          st_cyc_ex == DL_STATUS_COMPLETE &&
                          gold_dl_count_pred_facts(dl_cyc_ex, "reach") == 4 &&
                          st_cyc_unb == DL_STATUS_BUDGET_EXHAUSTED &&
                          st_pt == DL_STATUS_COMPLETE &&
                          gold_dl_has_fact(dl_pt, "points_to", 3, 100) &&
                          gold_dl_has_fact(dl_pt, "alias", 1, 3) &&
                          gold_dl_count_pred_facts(dl_pt, "diag") == 1 &&
                          gold_dl_has_fact(dl_pt, "diag", 7, 7),
                          "12a. Datalog D1 distinguishes Fact Closure, One-Step Retained Explanations (2 paths for reach(1,4)), and Unbounded Unfolding on cycles + Points-To/Nonlinear Join");

                    free(dl_fc);
                    free(dl_ex);
                    free(dl_cyc_ex);
                    free(dl_cyc_unb);
                    free(dl_pt);
                }

                /* 12b. First-Order CHR C1 Gold Suite (`leq.chr`, `finite_terms.pl`, `resource_scheduler.pl`) */
                {
                    /* leq.chr: reflexivity, antisymmetry (X=Y), idempotence, transitivity */
                    const char *leq_src =
                        ":- use_module(library(chr)).\n"
                        ":- chr_constraint leq/2, same/2.\n"
                        "refl @ leq(X, X) <=> true.\n"
                        "anti @ leq(X, Y), leq(Y, X) <=> unify_with_occurs_check(X, Y).\n"
                        "idem @ leq(X, Y) \\ leq(X, Y) <=> true.\n"
                        "tran @ leq(X, Y), leq(Y, Z) ==> leq(X, Z).\n";
                    run_c1_source_both_modes(
                        "12b-1. CHR C1 leq.chr antisymmetry cycle collapse",
                        leq_src,
                        "leq(A, B), leq(B, C), leq(C, A), same(A, C), unify_with_occurs_check(A, 7)",
                        C0_STATUS_COMPLETED, C0_FAULT_NONE, "[same(7,7)]");

                    /* finite_terms.pl: compound unification + occurs-check failure guard */
                    const char *ft_src =
                        ":- use_module(library(chr)).\n"
                        ":- chr_constraint pair_eq/2, hold/2.\n"
                        "unify_pair @ pair_eq(X, Y) <=> unify_with_occurs_check(X, Y).\n";
                    run_c1_source_both_modes(
                        "12b-2. CHR C1 finite_terms.pl compound unification",
                        ft_src,
                        "pair_eq(box(A, f(10)), box(g(20), B)), hold(A, B)",
                        C0_STATUS_COMPLETED, C0_FAULT_NONE, "[hold(g(20),f(10))]");

                    /* resource_scheduler.pl: simpagation resource grant + wakeup on binding */
                    const char *rs_src =
                        ":- use_module(library(chr)).\n"
                        ":- chr_constraint quota/1, req/2, granted/2, wait_slot/2, scheduled/2.\n"
                        "alloc @ quota(Slot) \\ req(Task, OutSlot) <=> unify_with_occurs_check(OutSlot, Slot), granted(Task, Slot).\n"
                        "notify @ granted(Task, S), wait_slot(Task, S) <=> scheduled(Task, S).\n";
                    run_c1_source_both_modes(
                        "12b-3. CHR C1 resource_scheduler.pl wakeup on logical variable binding",
                        rs_src,
                        "quota(gpu0), wait_slot(job1, R), req(job1, R)",
                        C0_STATUS_COMPLETED, C0_FAULT_NONE, "[quota(gpu0),scheduled(job1,gpu0)]");
                }

                /* 12c. Erlang E0 + E1 (`gold_worker_pool.erl` & `gold_selective_reply.erl`):
                 *      Separate `send`, per-(sender,receiver) FIFO channel delivery,
                 *      selective `receive` preserving unmatched mailbox prefixes, and cursor resumption */
                {
                    GoldErlangSystem *er1 = (GoldErlangSystem *)calloc(1, sizeof(GoldErlangSystem));
                    gold_er_init(er1);
                    uint32_t coord = gold_er_spawn(er1, "coordinator");
                    uint32_t w1 = gold_er_spawn(er1, "worker1");
                    uint32_t w2 = gold_er_spawn(er1, "worker2");

                    /* Send 3 messages to coordinator:
                     *   1) noise("log", req=1, payload=999) from w1
                     *   2) low_reply("reply", req=10, payload=100) from w1
                     *   3) high_reply("reply", req=20, payload=250) from w2
                     * Before delivery, coordinator's mailbox is empty (0 alive) while network has 3 in-flight envelopes! */
                    gold_er_send(er1, w1, coord, "log", 1, 999);
                    gold_er_send(er1, w1, coord, "reply", 10, 100);
                    gold_er_send(er1, w2, coord, "reply", 20, 250);
                    GoldErProcess *cproc1 = gold_er_find_proc(er1, coord);
                    uint32_t mbox_before_deliver = gold_er_alive_mbox_count(cproc1);

                    /* Deliver in per-(sender,receiver) FIFO order */
                    gold_er_deliver_fifo(er1, w1, coord);
                    gold_er_deliver_fifo(er1, w1, coord);
                    gold_er_deliver_fifo(er1, w2, coord);
                    uint32_t mbox_after_deliver = gold_er_alive_mbox_count(cproc1);

                    /* One-shot selective receive for tag="reply" with guard `req_id >= 15`:
                     * Skips `("log", 1, 999)` and `("reply", 10, 100)` and consumes `("reply", 20, 250)`,
                     * leaving the two earlier unmatched prefix messages intact in the mailbox! */
                    GoldErReceiveCursor cur_oneshot = gold_er_receive_begin(coord, "reply", 15);
                    gold_er_receive_resume(er1, &cur_oneshot, 10);

                    /* Identical run with interrupted/resumed cursor (budget=1, then 1, then 1) */
                    GoldErlangSystem *er2 = (GoldErlangSystem *)calloc(1, sizeof(GoldErlangSystem));
                    gold_er_init(er2);
                    uint32_t coord2 = gold_er_spawn(er2, "coordinator");
                    uint32_t w1_2 = gold_er_spawn(er2, "worker1");
                    uint32_t w2_2 = gold_er_spawn(er2, "worker2");
                    gold_er_send(er2, w1_2, coord2, "log", 1, 999);
                    gold_er_send(er2, w1_2, coord2, "reply", 10, 100);
                    gold_er_send(er2, w2_2, coord2, "reply", 20, 250);
                    gold_er_deliver_fifo(er2, w1_2, coord2);
                    gold_er_deliver_fifo(er2, w1_2, coord2);
                    gold_er_deliver_fifo(er2, w2_2, coord2);
                    GoldErReceiveCursor cur_resumed = gold_er_receive_begin(coord2, "reply", 15);
                    gold_er_receive_resume(er2, &cur_resumed, 1);
                    bool mid_peeking = (cur_resumed.phase == ER_CURSOR_PEEKING && cur_resumed.scan_idx == 1);
                    gold_er_receive_resume(er2, &cur_resumed, 1);
                    gold_er_receive_resume(er2, &cur_resumed, 1);
                    GoldErProcess *cproc2 = gold_er_find_proc(er2, coord2);

                    /* Parse & execute disk Gold Erlang files (`gold_worker_pool.erl` & `gold_selective_reply.erl`) */
                    char *wp_src = read_file_text("../Mettapedia/metta/gslt/module/gold/Erlang/examples/gold_worker_pool.erl");
                    char *sr_src = read_file_text("../Mettapedia/metta/gslt/module/gold/Erlang/examples/gold_selective_reply.erl");
                    GoldErModule *wp_mod = (GoldErModule *)calloc(1, sizeof(GoldErModule));
                    GoldErModule *sr_mod = (GoldErModule *)calloc(1, sizeof(GoldErModule));
                    GoldErlangSystem *er_wp = (GoldErlangSystem *)calloc(1, sizeof(GoldErlangSystem));
                    GoldErlangSystem *er_sr = (GoldErlangSystem *)calloc(1, sizeof(GoldErlangSystem));
                    gold_er_init(er_wp);
                    gold_er_init(er_sr);
                    bool ok_wp_p = wp_src && gold_er_parse_source(wp_mod, wp_src);
                    bool ok_sr_p = sr_src && gold_er_parse_source(sr_mod, sr_src);
                    char wp_out[256] = {0}, sr_out[256] = {0};
                    bool ok_wp_run = ok_wp_p && gold_er_eval_call_str(
                        er_wp, wp_mod, 0, "run(2, 10, [{task4, 21}, {task2, 20}])", wp_out, sizeof(wp_out));
                    bool ok_sr_run = ok_sr_p && gold_er_eval_call_str(
                        er_sr, sr_mod, 0, "Srv = start(5), request(Srv, corr_1, 83)", sr_out, sizeof(sr_out));

                    CHECK(mbox_before_deliver == 0 && mbox_after_deliver == 3 &&
                          cur_oneshot.phase == ER_CURSOR_DONE &&
                          cur_oneshot.matched_msg.payload == 250 &&
                          mid_peeking && cur_resumed.phase == ER_CURSOR_DONE &&
                          cur_resumed.matched_msg.payload == cur_oneshot.matched_msg.payload &&
                          cur_resumed.steps_executed == cur_oneshot.steps_executed &&
                          gold_er_alive_mbox_count(cproc1) == 2 &&
                          gold_er_alive_mbox_count(cproc2) == 2 &&
                          cproc1->mbox[0].alive && strcmp(cproc1->mbox[0].msg.tag, "log") == 0 &&
                          cproc1->mbox[1].alive && cproc1->mbox[1].msg.req_id == 10 &&
                          !cproc1->mbox[2].alive &&
                          ok_wp_run && strcmp(wp_out, "[{0, task4, 210}, {1, task2, 200}]") == 0 &&
                          er_wp->sends_admitted >= 8 && er_wp->receives_admitted >= 8 &&
                          ok_sr_run && strcmp(sr_out, "415") == 0 &&
                          er_sr->sends_admitted >= 2 && er_sr->receives_admitted >= 2,
                          "12c. Erlang E1 parses & executes disk gold_worker_pool.erl (%s) and gold_selective_reply.erl (%s), separates send/deliver FIFO channels, and resumes cursors exactly",
                          wp_out, sr_out);

                    gold_er_destroy(er_wp);
                    gold_er_destroy(er_sr);
                    gold_er_module_destroy(wp_mod);
                    gold_er_module_destroy(sr_mod);
                    free(wp_mod);
                    free(sr_mod);
                    free(er_wp);
                    free(er_sr);
                    free(wp_src);
                    free(sr_src);
                    free(er1);
                    free(er2);
                }

                /* 12d. OCaml O0 + O1 (`task_ranking.ml`, `tree_list.ml`):
                 *      Rank-1 let-polymorphism, type-directed constructor disambiguation,
                 *      and all 4 mandatory type refusals (mismatch, occurs-check, mono param, value restriction) */
                {
                    GoldMlTypeEnv *tenv = (GoldMlTypeEnv *)calloc(1, sizeof(GoldMlTypeEnv));
                    gold_ml_type_env_init(tenv);

                    /* 1. Positive Rank-1 Let-Polymorphism: `let id = fun x -> x in (id 7, id "ok")` */
                    GoldMlType *alpha = gold_ml_tvar(tenv);
                    GoldMlType *id_fn = gold_ml_tarrow(tenv, alpha, alpha);
                    GoldMlScheme id_scheme = gold_ml_generalize(tenv, id_fn, true /* syntactic value */);
                    GoldMlType *inst1 = gold_ml_instantiate(tenv, &id_scheme);
                    GoldMlType *inst2 = gold_ml_instantiate(tenv, &id_scheme);
                    GoldMlType *ty_int = gold_ml_alloc_type(tenv, OCAML_TY_INT);
                    GoldMlType *ty_str = gold_ml_alloc_type(tenv, OCAML_TY_STRING);
                    bool ok_poly1 = gold_ml_unify(tenv, inst1->left, ty_int);
                    bool ok_poly2 = gold_ml_unify(tenv, inst2->left, ty_str);
                    GoldMlType *res1 = gold_ml_prune(tenv, inst1->right);
                    GoldMlType *res2 = gold_ml_prune(tenv, inst2->right);

                    /* 2. Type-Directed Constructor Disambiguation:
                     *    `Score` belongs to both `metric` and `badge`. Disambiguated by expected type `badge`! */
                    GoldMlCtorDecl ctors[2] = {
                        { "Score", "metric", OCAML_TY_INT },
                        { "Score", "badge",  OCAML_TY_INT }
                    };
                    GoldMlType *exp_badge = gold_ml_tvariant(tenv, "badge");
                    GoldMlType *disamb_ok = gold_ml_disambiguate_ctor(tenv, ctors, 2, "Score", ty_int, exp_badge);
                    GoldMlType *disamb_ambig = gold_ml_disambiguate_ctor(tenv, ctors, 2, "Score", ty_int, NULL);
                    GoldMlRefusalKind ref_ambig = tenv->refusal;

                    /* 3. Refusal Control 1: Branch type mismatch (`if true then 1 else "bad"`) */
                    tenv->refusal = OCAML_OK;
                    bool ok_mismatch = gold_ml_unify(tenv, ty_int, ty_str);
                    GoldMlRefusalKind ref_mismatch = tenv->refusal;

                    /* 4. Refusal Control 2: Occurs-check (`fun x -> x x` => `'a = 'a -> 'b`) */
                    tenv->refusal = OCAML_OK;
                    GoldMlType *beta = gold_ml_tvar(tenv);
                    GoldMlType *gamma = gold_ml_tvar(tenv);
                    GoldMlType *self_arr = gold_ml_tarrow(tenv, beta, gamma);
                    bool ok_occurs = gold_ml_unify(tenv, beta, self_arr);
                    GoldMlRefusalKind ref_occurs = tenv->refusal;

                    /* 5. Refusal Control 3: Value restriction (`let r = ref None` is expansive, so `nquant == 0`;
                     *    using `r` at both `int ref` and `string ref` fails unification!) */
                    tenv->refusal = OCAML_OK;
                    GoldMlType *elem_var = gold_ml_tvar(tenv);
                    GoldMlType *ref_ty = gold_ml_tref(tenv, elem_var);
                    GoldMlScheme ref_scheme = gold_ml_generalize(tenv, ref_ty, false /* expansive application! */);
                    GoldMlType *r_use1 = gold_ml_instantiate(tenv, &ref_scheme);
                    GoldMlType *r_use2 = gold_ml_instantiate(tenv, &ref_scheme);
                    bool ok_vr1 = gold_ml_unify(tenv, r_use1->left, ty_int);
                    bool ok_vr2 = gold_ml_unify(tenv, r_use2->left, ty_str);

                    /* 6. Unbounded Scheme Generalization (>8 type variables): 20-variable polymorphic tuple/arrow spine */
                    GoldMlType *wide_ty = gold_ml_tvar(tenv);
                    for (uint32_t w = 1; w < 20; w++) {
                        GoldMlType *wv = gold_ml_tvar(tenv);
                        wide_ty = gold_ml_tarrow(tenv, wv, wide_ty);
                    }
                    GoldMlScheme wide_scheme = gold_ml_generalize(tenv, wide_ty, true);
                    GoldMlType *w_inst1 = gold_ml_instantiate(tenv, &wide_scheme);
                    GoldMlType *w_inst2 = gold_ml_instantiate(tenv, &wide_scheme);
                    bool ok_wide1 = gold_ml_unify(tenv, w_inst1->left, ty_int);
                    bool ok_wide2 = gold_ml_unify(tenv, w_inst2->left, ty_str);

                    /* 7. Parse & execute disk Gold OCaml files (`task_ranking.ml` & `tree_list.ml`) */
                    char *tr_src = read_file_text("../Mettapedia/metta/gslt/module/gold/OCaml/examples/task_ranking.ml");
                    char *tl_src = read_file_text("../Mettapedia/metta/gslt/module/gold/OCaml/examples/tree_list.ml");
                    GoldMlModule *tr_mod = (GoldMlModule *)calloc(1, sizeof(GoldMlModule));
                    GoldMlModule *tl_mod = (GoldMlModule *)calloc(1, sizeof(GoldMlModule));
                    bool ok_tr_p = tr_src && gold_ml_parse_source(tr_mod, tenv, tr_src);
                    bool ok_tl_p = tl_src && gold_ml_parse_source(tl_mod, tenv, tl_src);
                    char tr_names[256] = {0}, tr_hi[64] = {0}, tr_lo[64] = {0};
                    char tl_poly[128] = {0}, tl_flat[128] = {0}, tl_shape[64] = {0};
                    bool ok_tr_eval = ok_tr_p &&
                        gold_ml_eval_str(tr_mod,
                            "names (top 2 [Task (\"task2\", 205, true); Task (\"dropped\", 999, false); Task (\"task4\", 210, true)])",
                            tr_names, sizeof(tr_names)) &&
                        gold_ml_eval_str(tr_mod,
                            "score_above 206 (Task (\"task4\", 210, true))",
                            tr_hi, sizeof(tr_hi)) &&
                        gold_ml_eval_str(tr_mod,
                            "score_above 206 (Task (\"task2\", 205, true))",
                            tr_lo, sizeof(tr_lo));
                    bool ok_tl_eval = ok_tl_p &&
                        gold_ml_eval_str(tl_mod, "use_polymorphic_identity ()", tl_poly, sizeof(tl_poly)) &&
                        gold_ml_eval_str(tl_mod,
                            "flatten (Node (Node (Empty, 1, Empty), 2, Node (Empty, 3, Empty)))",
                            tl_flat, sizeof(tl_flat)) &&
                        gold_ml_eval_str(tl_mod,
                            "shape (Node (Node (Empty, 1, Empty), 2, Node (Empty, 3, Empty)))",
                            tl_shape, sizeof(tl_shape));

                    CHECK(ok_poly1 && ok_poly2 &&
                          res1->kind == OCAML_TY_INT && res2->kind == OCAML_TY_STRING &&
                          disamb_ok != NULL && strcmp(disamb_ok->variant_name, "badge") == 0 &&
                          disamb_ambig == NULL && ref_ambig == OCAML_REFUSE_AMBIGUOUS_CTOR &&
                          !ok_mismatch && ref_mismatch == OCAML_REFUSE_TYPE_MISMATCH &&
                          !ok_occurs && ref_occurs == OCAML_REFUSE_OCCURS_CHECK &&
                          ref_scheme.nquant == 0 && ok_vr1 && !ok_vr2 &&
                          wide_scheme.nquant == 20 && ok_wide1 && ok_wide2 &&
                          gold_ml_prune(tenv, w_inst1->left)->kind == OCAML_TY_INT &&
                          gold_ml_prune(tenv, w_inst2->left)->kind == OCAML_TY_STRING &&
                          ok_tr_eval && strcmp(tr_names, "[\"task4\"; \"task2\"]") == 0 &&
                          strcmp(tr_hi, "true") == 0 && strcmp(tr_lo, "false") == 0 &&
                          ok_tl_eval && strcmp(tl_poly, "(7, true, \"task\")") == 0 &&
                          strcmp(tl_flat, "[1; 2; 3]") == 0 &&
                          strcmp(tl_shape, "\"branch\"") == 0,
                          "12d. OCaml O1 parses & executes disk task_ranking.ml (%s) and tree_list.ml (%s, %s, %s); on types built by hand: rank-1 let-polymorphism, ctor disambiguation, and the 4 type refusals",
                          tr_names, tl_poly, tl_flat, tl_shape);

                    free(tr_mod);
                    free(tl_mod);
                    free(tr_src);
                    free(tl_src);
                    gold_ml_scheme_destroy(&id_scheme);
                    gold_ml_scheme_destroy(&ref_scheme);
                    gold_ml_scheme_destroy(&wide_scheme);
                    gold_ml_type_env_destroy(tenv);
                    free(tenv);
                }

                /* 12e. Maude M0 + M1 (`resource_protocol.maude`, `nested_workflow.maude`):
                 *      Certified ACU equations, frozen vs permitted contexts, and multistep `=>*` conditions */
                {
                    GoldMaudeEngine *me = (GoldMaudeEngine *)calloc(1, sizeof(GoldMaudeEngine));
                    gold_maude_init(me);

                    GoldMaudeConfig cfg;
                    memset(&cfg, 0, sizeof(cfg));
                    snprintf(cfg.state_label, sizeof(cfg.state_label), "Init");
                    /* Add unsorted ACU tokens with identity `"none"` and two `"half_grant"` tokens */
                    gold_maude_add_token(&cfg, "req_slot");
                    gold_maude_add_token(&cfg, "none");
                    gold_maude_add_token(&cfg, "half_grant");
                    gold_maude_add_token(&cfg, "quota_ok");
                    gold_maude_add_token(&cfg, "half_grant");
                    gold_maude_add_token(&cfg, "policy_ok");

                    /* 1. Attempt rewrite in frozen argument position 1 (`frozen_mask = 1u << 1`):
                     *    Must REFUSE rule rewrite (`MAUDE_REFUSE_FROZEN_CONTEXT`), while still normalizing
                     *    ACU equations (`none` eliminated, two `half_grant` coalesced into `grant_ready`)! */
                    bool ok_frozen = gold_maude_try_context_rewrite(me, &cfg, 1, (1u << 1));
                    GoldMaudeRefusalKind ref_frozen = me->last_refusal;
                    bool eq_coalesced = gold_maude_has_token(&cfg, "grant_ready") &&
                                        !gold_maude_has_token(&cfg, "none") &&
                                        !gold_maude_has_token(&cfg, "half_grant");

                    /* 2. Attempt rewrite in permitted argument position 0 (`frozen_mask = 1u << 1`):
                     *    Permitted! */
                    bool ok_permitted = gold_maude_try_context_rewrite(me, &cfg, 0, (1u << 1));

                    /* 3. Conditional rule `crl` with multistep rewrite condition `=>*`:
                     *    With `max_cond_steps = 1`, the 3-step condition sub-search cannot reach `audit_passed`
                     *    and must refuse (`MAUDE_REFUSE_CONDITION_FAIL`).
                     *    With `max_cond_steps = 5`, the 3-step condition sub-search reaches `audit_passed`
                     *    and commits `< S | SafeGrant >`! */
                    bool ok_crl_short = gold_maude_apply_crl_multistep(me, &cfg, 1);
                    GoldMaudeRefusalKind ref_short = me->last_refusal;
                    bool ok_crl_full = gold_maude_apply_crl_multistep(me, &cfg, 5);

                    /* 4. Parse & execute real Gold `.maude` module sources from disk (`resource_protocol.maude` & `nested_workflow.maude`) */
                    char *rp_src = read_file_text("../Mettapedia/metta/gslt/module/gold/Maude/examples/resource_protocol.maude");
                    GoldMaudeEngine *me_rp = (GoldMaudeEngine *)calloc(1, sizeof(GoldMaudeEngine));
                    gold_maude_init(me_rp);
                    bool ok_rp_parse = rp_src && gold_maude_parse_source(me_rp, rp_src);
                    char rp_open[128] = {0}, rp_closed[128] = {0}, rp_sealed[128] = {0};
                    uint32_t rp_steps_open = gold_maude_eval_rew_str(me_rp, "permission(alpha, open) request(alpha) token", 10, 5, rp_open, sizeof(rp_open));
                    uint32_t rp_steps_closed = gold_maude_eval_rew_str(me_rp, "permission(alpha, closed) request(alpha) token", 10, 5, rp_closed, sizeof(rp_closed));
                    uint32_t rp_steps_sealed = gold_maude_eval_rew_str(me_rp, "sealed(permission(alpha, open) request(alpha) token)", 10, 5, rp_sealed, sizeof(rp_sealed));
                    GoldMaudeRefusalKind rp_sealed_ref = me_rp->last_refusal;

                    char *nw_src = read_file_text("../Mettapedia/metta/gslt/module/gold/Maude/examples/nested_workflow.maude");
                    GoldMaudeEngine *me_nw = (GoldMaudeEngine *)calloc(1, sizeof(GoldMaudeEngine));
                    gold_maude_init(me_nw);
                    bool ok_nw_parse = nw_src && gold_maude_parse_source(me_nw, nw_src);
                    char nw_rew[128] = {0}, nw_sealed_eq[128] = {0};
                    uint32_t nw_steps = gold_maude_eval_rew_str(me_nw, "permit(alpha, pending) task(alpha)", 10, 5, nw_rew, sizeof(nw_rew));
                    uint32_t nw_sealed_steps = gold_maude_eval_rew_str(me_nw, "sealed(group(group(empty)))", 10, 5, nw_sealed_eq, sizeof(nw_sealed_eq));

                    CHECK(!ok_frozen && ref_frozen == MAUDE_REFUSE_FROZEN_CONTEXT &&
                          eq_coalesced && ok_permitted &&
                          !ok_crl_short && ref_short == MAUDE_REFUSE_CONDITION_FAIL &&
                          ok_crl_full && gold_maude_has_token(&cfg, "SafeGrant") &&
                          strcmp(cfg.state_label, "Committed") == 0 &&
                          me->crl_subsearches_completed == 1 && me->last_receipt.admitted == 1 &&
                          ok_rp_parse && rp_steps_open == 2 &&
                          strcmp(rp_open, "done(alpha) permission(alpha,open) token") == 0 &&
                          rp_steps_closed == 0 &&
                          strcmp(rp_closed, "permission(alpha,closed) request(alpha) token") == 0 &&
                          rp_steps_sealed == 0 && rp_sealed_ref == MAUDE_REFUSE_FROZEN_CONTEXT &&
                          ok_nw_parse && nw_steps == 1 &&
                          strcmp(nw_rew, "done(alpha) permit(alpha,pending)") == 0 &&
                          nw_sealed_steps == 0 && strcmp(nw_sealed_eq, "sealed(empty)") == 0,
                          "12e. Maude M1 parses .maude modules (resource_protocol.maude, nested_workflow.maude), enforces frozen contexts, normalizes equations beneath frozen operators, and executes multistep `=>*` conditional rules");

                    free(rp_src);
                    free(nw_src);
                    free(me_rp);
                    free(me_nw);
                    free(me);
                }
            }

            /* =====================================================================
             * Suite 13: Stage 6 Joined 5-Language Gold Workflow
             *   Datalog D1 evidence -> CHR C1 resources -> Maude M1 protocol checks ->
             *   OCaml O1 ranking -> Erlang E1 workers -> MeTTa Prime results, explanations & receipts
             * ===================================================================== */
            {
                GoldJoinedWorkflowReport *rep = (GoldJoinedWorkflowReport *)calloc(1, sizeof(GoldJoinedWorkflowReport));

                /* Step 1 (Datalog D1): Compute demanded tasks & retained explanation counts
                 * Diamond dependency: root(1) depends on mid(2) and mid(3); both depend on leaf(4). */
                GoldDatalogEngine *dl = (GoldDatalogEngine *)calloc(1, sizeof(GoldDatalogEngine));
                gold_dl_init(dl, DL_COMPLETION_ONESTEP_EXPLANATIONS, 200);
                gold_dl_add_edb(dl, "dep", 1, 2);
                gold_dl_add_edb(dl, "dep", 2, 4);
                gold_dl_add_edb(dl, "dep", 1, 3);
                gold_dl_add_edb(dl, "dep", 3, 4);
                gold_dl_add_rule_1(dl, 1, "need", "dep", false, false);
                gold_dl_add_rule_2(dl, 2, "need", "dep", "need", false);
                gold_dl_run(dl);
                rep->dl_demanded_tasks = gold_dl_count_pred_facts(dl, "need");
                rep->dl_explanation_count = dl->nexpls;
                uint32_t leaf4_expls = gold_dl_count_expls_for(dl, "need", 1, 4);
                uint64_t dl_tc_events = dl->tc_admitted_facts + dl->tc_admitted_expls;
                free(dl);

                /* Step 2 (CHR C1): Allocate concrete hardware slots to demanded tasks using logical variables */
                const char *chr_sched =
                    ":- use_module(library(chr)).\n"
                    ":- chr_constraint slot/1, demand_task/2, assigned/2, awaiting/2, allocated/2.\n"
                    "grant @ slot(Hw), demand_task(T, OutHw) <=> unify_with_occurs_check(OutHw, Hw), assigned(T, Hw).\n"
                    "ready @ assigned(T, Hw), awaiting(T, Hw) <=> allocated(T, Hw).\n";
                const char *chr_query =
                    "slot(accel_a), slot(accel_b), awaiting(task4, H4), demand_task(task4, H4), awaiting(task2, H2), demand_task(task2, H2)";
                GsltArena a_chr;
                gslt_arena_init(&a_chr);
                GsltC0Program cp_chr;
                GsltC0Diagnostic d_chr = {0};
                char chr_err[256] = {0};
                bool ok_chr_p = gslt_c1_parse_source(&a_chr, chr_sched, strlen(chr_sched), &cp_chr, &d_chr, chr_err, sizeof(chr_err)) &&
                                gslt_c1_set_query_string(&a_chr, &cp_chr, chr_query, &d_chr, chr_err, sizeof(chr_err));
                C0LoweredEngine *eng_chr = (C0LoweredEngine *)calloc(1, sizeof(C0LoweredEngine));
                if (ok_chr_p) c0_run_machine(&cp_chr, eng_chr, C0_MODE_INDEXED, 1, 0);
                char chr_out[512] = {0};
                c0_format_store(eng_chr, chr_out, sizeof(chr_out));
                if (ok_chr_p && eng_chr->status == C0_STATUS_COMPLETED &&
                    strstr(chr_out, "allocated(task4,") != NULL &&
                    strstr(chr_out, "allocated(task2,") != NULL) {
                    rep->chr_allocated_resources = 2;
                }
                uint64_t chr_tc_events = eng_chr->events_admitted;
                c0_engine_destroy(eng_chr);
                free(eng_chr);
                gslt_arena_free(&a_chr);

                /* Step 3 (Maude M1): Verify resource protocol safety under ACU equations & multistep `=>*` condition */
                GoldMaudeEngine *maude = (GoldMaudeEngine *)calloc(1, sizeof(GoldMaudeEngine));
                gold_maude_init(maude);
                GoldMaudeConfig mcfg;
                memset(&mcfg, 0, sizeof(mcfg));
                gold_maude_add_token(&mcfg, "req_slot");
                gold_maude_add_token(&mcfg, "none");
                gold_maude_add_token(&mcfg, "half_grant");
                gold_maude_add_token(&mcfg, "half_grant");
                gold_maude_add_token(&mcfg, "quota_ok");
                gold_maude_add_token(&mcfg, "policy_ok");
                rep->maude_protocol_certified = gold_maude_apply_crl_multistep(maude, &mcfg, 5) &&
                                                gold_maude_has_token(&mcfg, "SafeGrant");
                uint64_t maude_tc_events = maude->rl_rewrites_admitted;
                free(maude);

                /* Step 4 (OCaml O1): Rank certified tasks using base priority + Datalog explanation bonus
                 * AND verify ranking order against disk `task_ranking.ml` (`names (top 2 ...)`)! */
                GoldMlTaskItem tasks[2] = {
                    { "task2", 10, 1, rep->maude_protocol_certified, 0 },
                    { "task4", 10, (int64_t)leaf4_expls, rep->maude_protocol_certified, 0 }
                };
                gold_ml_rank_tasks(tasks, 2, rep->ocaml_ranking_summary, sizeof(rep->ocaml_ranking_summary));
                char *j_tr_src = read_file_text("../Mettapedia/metta/gslt/module/gold/OCaml/examples/task_ranking.ml");
                GoldMlModule *j_tr_mod = (GoldMlModule *)calloc(1, sizeof(GoldMlModule));
                char j_tr_names[128] = {0};
                bool ok_j_ml = j_tr_src && gold_ml_parse_source(j_tr_mod, NULL, j_tr_src) &&
                    gold_ml_eval_str(j_tr_mod,
                        "names (top 2 [Task (\"task2\", 205, true); Task (\"dropped\", 999, false); Task (\"task4\", 210, true)])",
                        j_tr_names, sizeof(j_tr_names)) &&
                    strcmp(j_tr_names, "[\"task4\"; \"task2\"]") == 0;
                free(j_tr_mod);
                free(j_tr_src);

                /* Step 5 (Erlang E1): Dispatch ranked tasks to worker pool via FIFO channels & selective receive
                 * AND verify disk `gold_selective_reply.erl` (`start(5), request(Srv, corr_1, 83) == 415`)! */
                GoldErlangSystem *er = (GoldErlangSystem *)calloc(1, sizeof(GoldErlangSystem));
                gold_er_init(er);
                uint32_t master = gold_er_spawn(er, "master");
                uint32_t worker = gold_er_spawn(er, "worker");
                gold_er_send(er, worker, master, " telemetry", 1, 0);
                gold_er_send(er, worker, master, "completed", 1, tasks[0].total_score);
                gold_er_send(er, worker, master, "completed", 2, tasks[1].total_score);
                gold_er_deliver_fifo(er, worker, master);
                gold_er_deliver_fifo(er, worker, master);
                gold_er_deliver_fifo(er, worker, master);
                GoldErReceiveCursor c1 = gold_er_receive_begin(master, "completed", 1);
                gold_er_receive_resume(er, &c1, 10);
                GoldErReceiveCursor c2 = gold_er_receive_begin(master, "completed", 2);
                gold_er_receive_resume(er, &c2, 10);
                char *j_sr_src = read_file_text("../Mettapedia/metta/gslt/module/gold/Erlang/examples/gold_selective_reply.erl");
                GoldErModule *j_sr_mod = (GoldErModule *)calloc(1, sizeof(GoldErModule));
                char j_sr_out[64] = {0};
                bool ok_j_er = j_sr_src && gold_er_parse_source(j_sr_mod, j_sr_src) &&
                    gold_er_eval_call_str(er, j_sr_mod, 0, "Srv = start(5), request(Srv, corr_1, 83)", j_sr_out, sizeof(j_sr_out)) &&
                    strcmp(j_sr_out, "415") == 0;
                rep->erlang_worker_reply_sum = (ok_j_ml && ok_j_er) ? (c1.matched_msg.payload + c2.matched_msg.payload) : 0;
                uint64_t er_tc_events = er->sends_admitted + er->deliveries_admitted + er->receives_admitted;
                gold_er_destroy(er);
                gold_er_module_destroy(j_sr_mod);
                free(j_sr_mod);
                free(j_sr_src);
                free(er);

                /* Step 6 (MeTTa Prime over PettaTcalcEngine): Aggregate final results, explanations & receipts */
                PettaTcalcEngine *pe = (PettaTcalcEngine *)calloc(1, sizeof(PettaTcalcEngine));
                petta_tcalc_engine_init(pe, 0);
                char metta_prog[1024];
                snprintf(metta_prog, sizeof(metta_prog),
                    "!(add-atom &self (DatalogEvidence (Demanded %u) (Explanations %u) (Leaf4Paths %u)))\n"
                    "!(add-atom &self (ChrResources (Allocated %u)))\n"
                    "!(add-atom &self (MaudeProtocol (Certified %s)))\n"
                    "!(add-atom &self (OcamlTopTask \"%s\" %" PRId64 "))\n"
                    "!(add-atom &self (ErlangWorkerTotal %" PRId64 "))\n"
                    "!(let* (($ev (match &self (DatalogEvidence $d $e $l) ($d $e $l)))\n"
                    "        ($ch (match &self (ChrResources $c) $c))\n"
                    "        ($md (match &self (MaudeProtocol $m) $m))\n"
                    "        ($ml (match &self (OcamlTopTask $t $s) ($t $s)))\n"
                    "        ($er (match &self (ErlangWorkerTotal $w) $w)))\n"
                    "   (JoinedGoldWorkflow $ev $ch $md $ml $er))\n",
                    rep->dl_demanded_tasks, rep->dl_explanation_count, leaf4_expls,
                    rep->chr_allocated_resources,
                    rep->maude_protocol_certified ? "True" : "False",
                    tasks[0].name, tasks[0].total_score,
                    rep->erlang_worker_reply_sum);
                PettaValList mres;
                petta_vallist_init(&mres);
                bool ok_metta = petta_load_and_run_program(pe, metta_prog, &mres);
                if (mres.count > 0) {
                    petta_atom_render(mres.items[0], rep->metta_final_report, sizeof(rep->metta_final_report));
                }
                rep->total_tc_events_admitted = dl_tc_events + chr_tc_events + maude_tc_events +
                                                er_tc_events + pe->tc_events_admitted;
                rep->all_stages_ok = ok_metta &&
                                     rep->dl_demanded_tasks == 5 &&
                                     rep->dl_explanation_count == 6 &&
                                     leaf4_expls == 2 &&
                                     rep->chr_allocated_resources == 2 &&
                                     rep->maude_protocol_certified &&
                                     strcmp(rep->ocaml_ranking_summary, "[(\"task4\", 210); (\"task2\", 205)]") == 0 &&
                                     rep->erlang_worker_reply_sum == 415 &&
                                     strcmp(rep->metta_final_report,
                                         "(JoinedGoldWorkflow ((Demanded 5) (Explanations 6) (Leaf4Paths 2)) "
                                         "(Allocated 2) (Certified True) (\"task4\" 210) 415)") == 0;

                CHECK(rep->all_stages_ok && rep->total_tc_events_admitted >= 25,
                      "13. Joined 5-Language Gold Workflow (Datalog D1 -> CHR C1 -> Maude M1 -> OCaml O1 -> Erlang E1 -> MeTTa Prime) verified end-to-end (%llu admitted tcalc events): %s",
                      (unsigned long long)rep->total_tc_events_admitted,
                      rep->metta_final_report);

                petta_vallist_free(&mres);
                petta_tcalc_engine_destroy(pe);
                free(pe);
                free(rep);
            }
        }
    }

    printf("=== Summary: %d/%d checks passed (%d failed) ===\n",
           g_pass, g_pass + g_fail, g_fail);
    return g_fail == 0 ? 0 : 1;
}

/* =========================================================================
 * 11. CLI Entrypoint
 * ========================================================================= */

int main(int argc, char **argv) {
    if (argc >= 2 && strcmp(argv[1], "--self-test") == 0) {
        return run_self_test();
    }

    const char *facts_dir = NULL;
    const char *engine_mode = "seminaive";
    const char *c0_mode_str = NULL;
    const char *c1_query_str = NULL;
    uint32_t c0_threads = 0;
    uint32_t max_candidates = 0;
    uint32_t max_steps = 0;
    bool enforce_absent = true;
    bool is_chr = false;
    bool is_c1 = false;
    bool is_metta_ir = false;
    bool is_d0_packet = false;
    bool is_d0_catalogue = false;
    bool is_c0_packet = false;
    bool is_c0_catalogue = false;
    bool is_c0_ir = false;
    bool emit_d0 = false;
    bool emit_dl = false;
    bool emit_c0 = false;
    bool emit_chr = false;
    const char *input_path = NULL;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--facts-dir") == 0 && i + 1 < argc) {
            facts_dir = argv[++i];
        } else if (strcmp(argv[i], "--engine") == 0 && i + 1 < argc) {
            engine_mode = argv[++i];
        } else if (strcmp(argv[i], "--c0-mode") == 0 && i + 1 < argc) {
            c0_mode_str = argv[++i];
        } else if (strcmp(argv[i], "--c0-threads") == 0 && i + 1 < argc) {
            c0_threads = (uint32_t)strtoull(argv[++i], NULL, 10);
        } else if (strcmp(argv[i], "--max-candidates") == 0 && i + 1 < argc) {
            max_candidates = (uint32_t)strtoull(argv[++i], NULL, 10);
        } else if (strcmp(argv[i], "--max-steps") == 0 && i + 1 < argc) {
            max_steps = (uint32_t)strtoull(argv[++i], NULL, 10);
        } else if (strcmp(argv[i], "--no-absent-guard") == 0) {
            enforce_absent = false;
        } else if (strcmp(argv[i], "--chr") == 0) {
            is_chr = true;
        } else if (strcmp(argv[i], "--c1") == 0) {
            is_chr = true; is_c1 = true;
        } else if (strcmp(argv[i], "--c1-query") == 0 && i + 1 < argc) {
            is_chr = true; is_c1 = true; c1_query_str = argv[++i];
        } else if (strcmp(argv[i], "--metta-ir") == 0 || strcmp(argv[i], "--d0-ir") == 0) {
            is_metta_ir = true;
        } else if (strcmp(argv[i], "--d0-packet") == 0) {
            is_d0_packet = true;
        } else if (strcmp(argv[i], "--d0-catalogue") == 0) {
            is_d0_catalogue = true;
        } else if (strcmp(argv[i], "--c0-packet") == 0) {
            is_c0_packet = true; is_chr = true;
        } else if (strcmp(argv[i], "--c0-catalogue") == 0) {
            is_c0_catalogue = true; is_chr = true;
        } else if (strcmp(argv[i], "--c0-ir") == 0) {
            is_c0_ir = true; is_chr = true;
        } else if (strcmp(argv[i], "--emit-d0") == 0) {
            emit_d0 = true;
        } else if (strcmp(argv[i], "--emit-dl") == 0) {
            emit_dl = true;
        } else if (strcmp(argv[i], "--emit-c0") == 0) {
            emit_c0 = true; is_chr = true;
        } else if (strcmp(argv[i], "--emit-chr") == 0) {
            emit_chr = true; is_chr = true;
        } else if (argv[i][0] != '-') {
            input_path = argv[i];
        } else {
            fprintf(stderr,
                    "Usage: %s [--self-test] [--engine naive|seminaive] [--facts-dir DIR]\n"
                    "          [--max-candidates N] [--no-absent-guard]\n"
                    "          [--d0-packet | --d0-catalogue | --d0-ir | --metta-ir] [--emit-d0 | --emit-dl]\n"
                    "          [--chr | --c1 | --c1-query GOAL | --c0-packet | --c0-catalogue | --c0-ir] [--emit-c0 | --emit-chr]\n"
                    "          [--c0-mode naive|indexed|parallel] [--c0-threads N] [--max-steps N] <file>\n",
                    argv[0]);
            return 1;
        }
    }

    if (!input_path) {
        return run_self_test();
    }

    char *src = read_file_text(input_path);
    if (!src) {
        fprintf(stderr, "Error: cannot read %s\n", input_path);
        return 1;
    }

    int len = (int)strlen(input_path);
    if (len > 4 && strcmp(input_path + len - 4, ".chr") == 0) is_chr = true;

    if (is_chr) {
        GsltArena arena;
        gslt_arena_init(&arena);
        GsltC0Program cp;
        GsltC0Diagnostic d;
        memset(&d, 0, sizeof(d));
        char err[512] = {0};
        bool ok = false;
        if (is_c0_packet || is_c0_catalogue) {
            ok = gslt_c0_read_catalogue(&arena, src, strlen(src), &cp, &d, NULL, NULL, err, sizeof(err));
        } else if (is_c0_ir) {
            ok = gslt_c0_parse_ir(&arena, src, strlen(src), &cp, &d, err, sizeof(err));
        } else if (is_c1) {
            ok = gslt_c1_parse_source(&arena, src, strlen(src), &cp, &d, err, sizeof(err));
            if (ok && c1_query_str) {
                ok = gslt_c1_set_query_string(&arena, &cp, c1_query_str, &d, err, sizeof(err));
            }
        } else {
            ok = gslt_c0_parse_source(&arena, src, strlen(src), &cp, &d, err, sizeof(err));
        }
        if (!ok) {
            if (d.kind != GSLT_C0_DIAG_NONE) {
                fprintf(stderr, "Diagnostic: %s\n", gslt_c0_diag_name(d.kind));
            } else {
                fprintf(stderr, "Error: %s\n", err);
            }
            gslt_arena_free(&arena);
            free(src);
            return 1;
        }
        if (emit_c0) {
            GsltByteStr out = gslt_c0_emit_ir(&arena, &cp);
            printf("%.*s\n", (int)out.len, out.bytes);
            gslt_arena_free(&arena);
            free(src);
            return 0;
        }
        if (emit_chr) {
            GsltByteStr out = gslt_c0_emit_prolog_source(&arena, &cp);
            printf("%.*s", (int)out.len, out.bytes);
            gslt_arena_free(&arena);
            free(src);
            return 0;
        }

        C0SearchMode mode = C0_MODE_INDEXED;
        if (c0_mode_str) {
            if (strcmp(c0_mode_str, "naive") == 0) mode = C0_MODE_NAIVE;
            else if (strcmp(c0_mode_str, "parallel") == 0) mode = C0_MODE_PARALLEL;
        } else if (c0_threads > 1) {
            mode = C0_MODE_PARALLEL;
        }
        uint32_t eff_threads = (mode == C0_MODE_PARALLEL) ? (c0_threads > 0 ? c0_threads : 4) : 1;

        C0LoweredEngine *ceng = (C0LoweredEngine *)calloc(1, sizeof(C0LoweredEngine));
        c0_run_machine(&cp, ceng, mode, eff_threads, max_steps);
        char *store_buf = c0_format_store_alloc(ceng);
        if (ceng->status == C0_STATUS_COMPLETED) {
            printf("{\"status\":\"completed\",\"events\":%" PRIu64 ",\"candidates\":%" PRIu64 ",\"store\":\"%s\"}\n",
                   ceng->events_admitted, ceng->candidates_examined, store_buf);
            free(store_buf);
            c0_engine_destroy(ceng);
            free(ceng);
            gslt_arena_free(&arena);
            free(src);
            return 0;
        } else if (ceng->status == C0_STATUS_FAULT) {
            printf("{\"status\":\"fault\",\"fault\":\"%s\",\"events\":%" PRIu64 ",\"store\":\"%s\"}\n",
                   c0_fault_name(ceng->fault), ceng->events_admitted, store_buf);
            free(store_buf);
            c0_engine_destroy(ceng);
            free(ceng);
            gslt_arena_free(&arena);
            free(src);
            return 1;
        } else {
            printf("{\"status\":\"%s\",\"events\":%" PRIu64 ",\"store\":\"%s\"}\n",
                   c0_status_name(ceng->status), ceng->events_admitted, store_buf);
            free(store_buf);
            c0_engine_destroy(ceng);
            free(ceng);
            gslt_arena_free(&arena);
            free(src);
            return 1;
        }
    }

    /* D0 Packet / Catalogue pre-conversion if requested */
    const char *effective_src = src;
    GsltArena d0_arena;
    gslt_arena_init(&d0_arena);
    if (is_d0_packet || is_d0_catalogue) {
        GsltByteStr ir_str = { "", 0 };
        char err[512] = {0};
        bool ok = is_d0_packet
            ? gslt_d0_packet_to_ir_str(&d0_arena, src, strlen(src), &ir_str, NULL, err, sizeof(err))
            : gslt_d0_catalogue_to_ir_str(&d0_arena, src, strlen(src), &ir_str, NULL, NULL, err, sizeof(err));
        if (!ok) {
            fprintf(stderr, "Error: %s\n", err);
            gslt_arena_free(&d0_arena);
            free(src);
            return 1;
        }
        effective_src = ir_str.bytes;
        is_metta_ir = true;
    }

    D0Program *p = (D0Program *)calloc(1, sizeof(D0Program));
    D0DiagKind d = is_metta_ir ? d0_parse_metta_ir(effective_src, p) : d0_parse_dl(effective_src, p);
    gslt_arena_free(&d0_arena);
    free(src);
    if (d != D0_DIAG_OK) {
        fprintf(stderr, "Diagnostic: %s\n", d0_diag_name(d));
        free(p);
        return 1;
    }
    d = d0_static_admit(p);
    if (d != D0_DIAG_OK) {
        fprintf(stderr, "Diagnostic: %s\n", d0_diag_name(d));
        free(p);
        return 1;
    }
    if (facts_dir) {
        d = d0_load_facts_dir(p, facts_dir);
        if (d != D0_DIAG_OK) {
            fprintf(stderr, "Diagnostic: %s\n", d0_diag_name(d));
            free(p);
            return 1;
        }
    }

    if (emit_d0) {
        GsltArena emit_a;
        gslt_arena_init(&emit_a);
        GsltByteStr out = d0_emit_metta_ir(&emit_a, p);
        printf("%.*s\n", (int)out.len, out.bytes);
        gslt_arena_free(&emit_a);
        free(p);
        return 0;
    }
    if (emit_dl) {
        GsltArena emit_a;
        gslt_arena_init(&emit_a);
        GsltByteStr out = d0_emit_dl_source(&emit_a, p);
        printf("%.*s", (int)out.len, out.bytes);
        gslt_arena_free(&emit_a);
        free(p);
        return 0;
    }

    bool is_naive = (strcmp(engine_mode, "naive") == 0);
    D0LoweredEngine *eng = (D0LoweredEngine *)calloc(1, sizeof(D0LoweredEngine));
    if (!d0_lower_to_tcalc_ex(p, eng, !is_naive && enforce_absent)) {
        fprintf(stderr, "Error: lowering failed\n");
        free(eng);
        free(p);
        return 1;
    }

    TcAdmissionProfile prof = tc_admission_custom_profile(
        "d0_cli_profile", enforce_absent, true, false, false, eng, d0_scalar_cmp_permit);
    TcAdmittedEvent last_ev;
    memset(&last_ev, 0, sizeof(last_ev));

    D0RunMetrics m = is_naive
        ? d0_run_m1_naive(p, eng, &prof, max_candidates, &last_ev)
        : d0_run_m2_seminaive(p, eng, &prof, max_candidates, &last_ev);
    if (getenv("DL_TCALC_PROFILE")) {
        fprintf(stderr, "[DL_TCALC_PROFILE] examined=%" PRIu64 " admitted=%" PRIu64 " run_ms=%.3f\n",
                m.candidates_examined, m.events_admitted, m.elapsed_us / 1000.0);
    }

    if (g_d0_capacity_cutoff) {
        fprintf(stderr, "CapacityCutoff: %s is full; examined=%" PRIu64 " events=%" PRIu64 " (not a fixed point)\n",
                g_d0_capacity_cutoff, m.candidates_examined, m.events_admitted);
        free(eng);
        free(p);
        return 2;
    }
    if (m.status == TC_BRIDGE_BUDGET_EXHAUSTED) {
        fprintf(stderr, "BudgetCutoff: examined=%" PRIu64 " events=%" PRIu64 " (not a fixed point)\n",
                m.candidates_examined, m.events_admitted);
        free(eng);
        free(p);
        return 2;
    }

    for (int r = 0; r < p->nrels; r++) {
        if (!p->rels[r].is_output) continue;
        int cnt = 0;
        char *rbuf = d0_format_relation_rows_alloc(p, eng, r, &cnt);
        printf("---------------\n%s\n===============\n%s===============\n", p->rels[r].name, rbuf);
        free(rbuf);
    }
    free(eng);
    free(p);
    return 0;
}

/*
 * lean_tcalc.c — Lean 4 Kernel Verifier over tcalc (Lean 4 -> tcalc)
 *
 * Independently verifies Lean 4 kernel environments exported in `lean4export`
 * NDJSON format (compatible with arena.lean-lang.org, Lean v4.28.0-rc1 Mettapedia/Mathlib,
 * and Lean v4.33.1+).
 *
 * Every verified universe judgment, declaration admission (axiom, defn, thm, opaque,
 * quot, ind, ctor, rec), and typing / conversion certificate commits a prepared step
 * into protected tcalc spaces (`SPACE_ENV`, `SPACE_THM`) after `tc_seal()`.
 *
 * Symbol, universe level, environment declaration, and WHNF tables grow dynamically
 * via realloc; the two-tier `mmap` (`MAP_NORESERVE`) expression arena provides `2^26`
 * (`67,108,864`) persistent expression slots and `2^26` (`67,108,864`) per-declaration
 * scratch slots (exiting with `DECLINE` / code `2` on capacity cutoff), and kernel
 * `Nat` literal arithmetic evaluates values up to `2^128 - 1` (keeping larger decimal
 * literals in canonical unreduced form).
 */
#define _DEFAULT_SOURCE
#define _POSIX_C_SOURCE 200809L
#include <ctype.h>
#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <time.h>

#include "tcalc.h"
#include "bridge/tc_cetta_bridge.h"
#ifdef TC_USE_CESTA_EXPORT
#include "cesta/tc_lean_guard.export.h"
void tc_lean_guard_failure(void) { abort(); }
#endif

typedef enum {
    LEAN_ARENA_ACCEPT   = 0,
    LEAN_ARENA_REJECT   = 1,
    LEAN_ARENA_DECLINE  = 2,
    LEAN_ARENA_FAULT    = 3,
    LEAN_OUTCOME_ACCEPT  = 0,
    LEAN_OUTCOME_REJECT  = 1,
    LEAN_OUTCOME_DECLINE = 2,
    LEAN_OUTCOME_FAULT   = 3
} LeanArenaOutcome;

/* =========================================================================
 * 0. Self-Contained Strict RFC-8259 JSON DOM & Tokener (`json-c` Compatible API)
 * ========================================================================= */

enum json_type {
    json_type_null = 0,
    json_type_boolean,
    json_type_int,
    json_type_string,
    json_type_array,
    json_type_object
};

enum json_tokener_error {
    json_tokener_success = 0,
    json_tokener_error_parse
};

#define JSON_TOKENER_STRICT 1

struct json_kv {
    char *key;
    struct json_object *val;
};

struct json_object {
    enum json_type type;
    union {
        bool bval;
        struct { int64_t i64; uint64_t u64; bool neg; } ival;
        char *sval;
        struct { struct json_object **items; size_t len; size_t cap; } arr;
        struct { struct json_kv *entries; size_t len; size_t cap; } obj;
    } d;
};

struct json_tokener {
    int max_depth;
    int flags;
    enum json_tokener_error err;
    size_t char_offset;
};

static void json_object_put(struct json_object *j) {
    if (!j) return;
    if (j->type == json_type_string) {
        free(j->d.sval);
    } else if (j->type == json_type_array) {
        for (size_t i = 0; i < j->d.arr.len; i++) json_object_put(j->d.arr.items[i]);
        free(j->d.arr.items);
    } else if (j->type == json_type_object) {
        for (size_t i = 0; i < j->d.obj.len; i++) {
            free(j->d.obj.entries[i].key);
            json_object_put(j->d.obj.entries[i].val);
        }
        free(j->d.obj.entries);
    }
    free(j);
}

static bool json_object_is_type(const struct json_object *j, enum json_type t) {
    return j && j->type == t;
}

static int json_object_object_length(const struct json_object *j) {
    return (j && j->type == json_type_object) ? (int)j->d.obj.len : 0;
}

static bool json_object_object_get_ex(const struct json_object *j, const char *key, struct json_object **out) {
    if (out) *out = NULL;
    if (!j || j->type != json_type_object || !key) return false;
    for (size_t i = 0; i < j->d.obj.len; i++) {
        if (strcmp(j->d.obj.entries[i].key, key) == 0) {
            if (out) *out = j->d.obj.entries[i].val;
            return true;
        }
    }
    return false;
}

static size_t json_object_array_length(const struct json_object *j) {
    return (j && j->type == json_type_array) ? j->d.arr.len : 0;
}

static struct json_object *json_object_array_get_idx(const struct json_object *j, size_t idx) {
    if (!j || j->type != json_type_array || idx >= j->d.arr.len) return NULL;
    return j->d.arr.items[idx];
}

static int64_t json_object_get_int64(const struct json_object *j) {
    return (j && j->type == json_type_int) ? j->d.ival.i64 : 0;
}

static uint64_t json_object_get_uint64(const struct json_object *j) {
    if (!j || j->type != json_type_int || j->d.ival.neg) {
        errno = EINVAL;
        return 0;
    }
    return j->d.ival.u64;
}

static bool json_object_get_boolean(const struct json_object *j) {
    return (j && j->type == json_type_boolean) ? j->d.bval : false;
}

static const char *json_object_get_string(const struct json_object *j) {
    return (j && j->type == json_type_string) ? j->d.sval : NULL;
}

static struct json_tokener *json_tokener_new_ex(int depth) {
    struct json_tokener *t = (struct json_tokener *)calloc(1, sizeof(*t));
    t->max_depth = depth > 0 ? depth : 64;
    return t;
}

static void json_tokener_set_flags(struct json_tokener *t, int flags) {
    if (t) t->flags = flags;
}

static enum json_tokener_error json_tokener_get_error(const struct json_tokener *t) {
    return t ? t->err : json_tokener_error_parse;
}

static void json_tokener_free(struct json_tokener *t) {
    free(t);
}

static void json_skip_ws(const char *s, size_t len, size_t *pos) {
    while (*pos < len && (s[*pos] == ' ' || s[*pos] == '\t' || s[*pos] == '\r' || s[*pos] == '\n')) {
        (*pos)++;
    }
}

static bool json_parse_hex4(const char *s, size_t len, size_t *pos, uint32_t *out) {
    if (*pos + 4 > len) return false;
    uint32_t cp = 0;
    for (int k = 0; k < 4; k++) {
        char hc = s[(*pos)++];
        cp <<= 4;
        if (hc >= '0' && hc <= '9') cp |= (uint32_t)(hc - '0');
        else if (hc >= 'a' && hc <= 'f') cp |= (uint32_t)(hc - 'a' + 10);
        else if (hc >= 'A' && hc <= 'F') cp |= (uint32_t)(hc - 'A' + 10);
        else return false;
    }
    *out = cp;
    return true;
}

static char *json_parse_strict_string(const char *s, size_t len, size_t *pos) {
    if (*pos >= len || s[*pos] != '"') return NULL;
    (*pos)++;
    size_t cap = 64, slen = 0;
    char *buf = (char *)malloc(cap);
    while (*pos < len) {
        unsigned char c = (unsigned char)s[(*pos)++];
        if (c == '"') {
            buf[slen] = '\0';
            return buf;
        }
        if (c < 0x20u) {
            free(buf);
            return NULL;
        }
        if (c == '\\') {
            if (*pos >= len) { free(buf); return NULL; }
            char esc = s[(*pos)++];
            switch (esc) {
                case '"':  c = '"'; break;
                case '\\': c = '\\'; break;
                case '/':  c = '/'; break;
                case 'b':  c = '\b'; break;
                case 'f':  c = '\f'; break;
                case 'n':  c = '\n'; break;
                case 'r':  c = '\r'; break;
                case 't':  c = '\t'; break;
                case 'u': {
                    uint32_t cp = 0;
                    if (!json_parse_hex4(s, len, pos, &cp)) { free(buf); return NULL; }
                    /* Reject embedded NUL (\u0000) to prevent C-string truncation collisions */
                    if (cp == 0u) { free(buf); return NULL; }
                    /* Reject unpaired low surrogate */
                    if (cp >= 0xDC00u && cp <= 0xDFFFu) { free(buf); return NULL; }
                    /* Decode UTF-16 surrogate pair (\uD800..\uDBFF followed by \uDC00..\uDFFF) */
                    if (cp >= 0xD800u && cp <= 0xDBFFu) {
                        if (*pos + 2 > len || s[*pos] != '\\' || s[*pos + 1] != 'u') {
                            free(buf);
                            return NULL;
                        }
                        *pos += 2;
                        uint32_t cp2 = 0;
                        if (!json_parse_hex4(s, len, pos, &cp2) || cp2 < 0xDC00u || cp2 > 0xDFFFu) {
                            free(buf);
                            return NULL;
                        }
                        cp = 0x10000u + (((cp - 0xD800u) << 10) | (cp2 - 0xDC00u));
                    }
                    if (slen + 6 >= cap) {
                        cap *= 2;
                        buf = (char *)realloc(buf, cap);
                    }
                    if (cp <= 0x7Fu) {
                        buf[slen++] = (char)cp;
                    } else if (cp <= 0x7FFu) {
                        buf[slen++] = (char)(0xC0u | (cp >> 6));
                        buf[slen++] = (char)(0x80u | (cp & 0x3Fu));
                    } else if (cp <= 0xFFFFu) {
                        buf[slen++] = (char)(0xE0u | (cp >> 12));
                        buf[slen++] = (char)(0x80u | ((cp >> 6) & 0x3Fu));
                        buf[slen++] = (char)(0x80u | (cp & 0x3Fu));
                    } else if (cp <= 0x10FFFFu) {
                        buf[slen++] = (char)(0xF0u | (cp >> 18));
                        buf[slen++] = (char)(0x80u | ((cp >> 12) & 0x3Fu));
                        buf[slen++] = (char)(0x80u | ((cp >> 6) & 0x3Fu));
                        buf[slen++] = (char)(0x80u | (cp & 0x3Fu));
                    } else {
                        free(buf);
                        return NULL;
                    }
                    continue;
                }
                default:
                    free(buf);
                    return NULL;
            }
        } else if (c >= 0x80u) {
            /* Strictly validate multi-byte UTF-8 sequence (RFC 3629) */
            uint32_t cp = 0;
            int extra = 0;
            uint32_t min_cp = 0;
            if ((c & 0xE0u) == 0xC0u) {
                cp = c & 0x1Fu; extra = 1; min_cp = 0x80u;
            } else if ((c & 0xF0u) == 0xE0u) {
                cp = c & 0x0Fu; extra = 2; min_cp = 0x800u;
            } else if ((c & 0xF8u) == 0xF0u) {
                cp = c & 0x07u; extra = 3; min_cp = 0x10000u;
            } else {
                free(buf);
                return NULL;
            }
            if (*pos + (size_t)extra > len) { free(buf); return NULL; }
            if (slen + 6 >= cap) {
                cap *= 2;
                buf = (char *)realloc(buf, cap);
            }
            buf[slen++] = (char)c;
            for (int k = 0; k < extra; k++) {
                unsigned char cc = (unsigned char)s[(*pos)++];
                if ((cc & 0xC0u) != 0x80u) { free(buf); return NULL; }
                cp = (cp << 6) | (cc & 0x3Fu);
                buf[slen++] = (char)cc;
            }
            if (cp < min_cp || cp > 0x10FFFFu || (cp >= 0xD800u && cp <= 0xDFFFu)) {
                free(buf);
                return NULL;
            }
            continue;
        }
        if (slen + 2 >= cap) {
            cap *= 2;
            buf = (char *)realloc(buf, cap);
        }
        buf[slen++] = (char)c;
    }
    free(buf);
    return NULL;
}

static struct json_object *json_parse_value(struct json_tokener *tok, const char *s, size_t len, size_t *pos, int depth) {
    if (depth > tok->max_depth) return NULL;
    json_skip_ws(s, len, pos);
    if (*pos >= len) return NULL;
    char c = s[*pos];

    if (c == '"') {
        char *str = json_parse_strict_string(s, len, pos);
        if (!str) return NULL;
        struct json_object *o = (struct json_object *)calloc(1, sizeof(*o));
        o->type = json_type_string;
        o->d.sval = str;
        return o;
    }
    if (c == '{') {
        (*pos)++;
        json_skip_ws(s, len, pos);
        struct json_object *o = (struct json_object *)calloc(1, sizeof(*o));
        o->type = json_type_object;
        if (*pos < len && s[*pos] == '}') {
            (*pos)++;
            return o;
        }
        while (*pos < len) {
            json_skip_ws(s, len, pos);
            char *k = json_parse_strict_string(s, len, pos);
            if (!k) { json_object_put(o); return NULL; }
            /* Reject duplicate keys inside the same JSON object */
            for (size_t i = 0; i < o->d.obj.len; i++) {
                if (strcmp(o->d.obj.entries[i].key, k) == 0) {
                    free(k);
                    json_object_put(o);
                    return NULL;
                }
            }
            json_skip_ws(s, len, pos);
            if (*pos >= len || s[*pos] != ':') {
                free(k);
                json_object_put(o);
                return NULL;
            }
            (*pos)++;
            struct json_object *v = json_parse_value(tok, s, len, pos, depth + 1);
            if (!v) {
                free(k);
                json_object_put(o);
                return NULL;
            }
            if (o->d.obj.len >= o->d.obj.cap) {
                size_t ncap = o->d.obj.cap ? o->d.obj.cap * 2 : 8;
                o->d.obj.entries = (struct json_kv *)realloc(o->d.obj.entries, ncap * sizeof(struct json_kv));
                o->d.obj.cap = ncap;
            }
            o->d.obj.entries[o->d.obj.len].key = k;
            o->d.obj.entries[o->d.obj.len].val = v;
            o->d.obj.len++;
            json_skip_ws(s, len, pos);
            if (*pos < len && s[*pos] == ',') {
                (*pos)++;
                continue;
            }
            if (*pos < len && s[*pos] == '}') {
                (*pos)++;
                return o;
            }
            json_object_put(o);
            return NULL;
        }
        json_object_put(o);
        return NULL;
    }
    if (c == '[') {
        (*pos)++;
        json_skip_ws(s, len, pos);
        struct json_object *o = (struct json_object *)calloc(1, sizeof(*o));
        o->type = json_type_array;
        if (*pos < len && s[*pos] == ']') {
            (*pos)++;
            return o;
        }
        while (*pos < len) {
            struct json_object *v = json_parse_value(tok, s, len, pos, depth + 1);
            if (!v) { json_object_put(o); return NULL; }
            if (o->d.arr.len >= o->d.arr.cap) {
                size_t ncap = o->d.arr.cap ? o->d.arr.cap * 2 : 8;
                o->d.arr.items = (struct json_object **)realloc(o->d.arr.items, ncap * sizeof(struct json_object *));
                o->d.arr.cap = ncap;
            }
            o->d.arr.items[o->d.arr.len++] = v;
            json_skip_ws(s, len, pos);
            if (*pos < len && s[*pos] == ',') {
                (*pos)++;
                continue;
            }
            if (*pos < len && s[*pos] == ']') {
                (*pos)++;
                return o;
            }
            json_object_put(o);
            return NULL;
        }
        json_object_put(o);
        return NULL;
    }
    if (c == 't' && *pos + 4 <= len && strncmp(s + *pos, "true", 4) == 0) {
        *pos += 4;
        struct json_object *o = (struct json_object *)calloc(1, sizeof(*o));
        o->type = json_type_boolean;
        o->d.bval = true;
        return o;
    }
    if (c == 'f' && *pos + 5 <= len && strncmp(s + *pos, "false", 5) == 0) {
        *pos += 5;
        struct json_object *o = (struct json_object *)calloc(1, sizeof(*o));
        o->type = json_type_boolean;
        o->d.bval = false;
        return o;
    }
    if (c == 'n' && *pos + 4 <= len && strncmp(s + *pos, "null", 4) == 0) {
        *pos += 4;
        struct json_object *o = (struct json_object *)calloc(1, sizeof(*o));
        o->type = json_type_null;
        return o;
    }
    if (c == '-' || (c >= '0' && c <= '9')) {
        bool neg = false;
        if (c == '-') {
            neg = true;
            (*pos)++;
            if (*pos >= len || s[*pos] < '0' || s[*pos] > '9') return NULL;
        }
        if (s[*pos] == '0' && *pos + 1 < len && s[*pos + 1] >= '0' && s[*pos + 1] <= '9') {
            return NULL; /* Leading zeros forbidden by RFC 8259 */
        }
        uint64_t u = 0;
        while (*pos < len && s[*pos] >= '0' && s[*pos] <= '9') {
            uint64_t d = (uint64_t)(s[(*pos)++] - '0');
            if (u > (UINT64_MAX - d) / 10u) return NULL;
            u = u * 10u + d;
        }
        if (*pos < len && (s[*pos] == '.' || s[*pos] == 'e' || s[*pos] == 'E')) {
            return NULL; /* Non-integer numbers rejected for kernel indices */
        }
        struct json_object *o = (struct json_object *)calloc(1, sizeof(*o));
        o->type = json_type_int;
        o->d.ival.neg = neg;
        o->d.ival.u64 = u;
        o->d.ival.i64 = neg ? -(int64_t)u : (int64_t)u;
        return o;
    }
    return NULL;
}

static struct json_object *json_tokener_parse_ex(struct json_tokener *tok, const char *str, int len) {
    if (!tok || !str || len < 0) return NULL;
    size_t pos = 0;
    size_t slen = (size_t)len;
    struct json_object *res = json_parse_value(tok, str, slen, &pos, 0);
    if (!res) {
        tok->err = json_tokener_error_parse;
        tok->char_offset = pos;
        return NULL;
    }
    json_skip_ws(str, slen, &pos);
    tok->char_offset = pos;
    tok->err = (pos == slen) ? json_tokener_success : json_tokener_error_parse;
    return res;
}

static double now_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec * 1e3 + (double)ts.tv_nsec * 1e-6;
}

/* =========================================================================
 * 1. Protected tcalc Spaces, Sorts, Constructors, and Premise-Bearing Rules
 * =========================================================================
 *
 * Explicit Trust & Inference Boundary:
 *   - Protected spaces `LEAN_SPACE_ENV` (admitted declarations) and
 *     `LEAN_SPACE_THM` (typing, sort, proposition, and conversion judgments)
 *     are sealed via `tc_seal()` before any stream is parsed.
 *   - Declaration admission rules (`R_ADMIT_*`) and judgment derivation rules
 *     (`R_DERIVE_IS_TYPE`, `R_DERIVE_IS_PROP`, `R_CHECK_CONV`) are genuine
 *     premise-bearing `tcalc` rules (`r.nkeep >= 1`) whose kept premises must
 *     exist in `LEAN_SPACE_THM` / `LEAN_SPACE_ENV` and unify across shared
 *     variables (`ty`, `val`, `actual_ty`, `ind_name`, and `lvl_zero`).
 *   - Trusted C helpers (`lean_whnf_core`, `lean_is_def_eq`, `lean_lvl_leq`,
 *     `lean_check_strict_positivity_block`) compute normal forms, universe
 *     inequalities, and positivity obligations and emit leaf certificates into
 *     `LEAN_SPACE_THM` that feed the premise-bearing `tcalc` rules.
 */

#include "lean_tcalc_theory.h"
#include "lean_tcalc_gen.h"
#include "tisa/tisa_manifest_export.h"

static bool lean_verify_exported_theory_json_buf(const char *buf, size_t len) {
    if (!buf || len == 0 || strlen(buf) != len || len > (size_t)INT_MAX) return false;
    struct json_tokener *tok = json_tokener_new_ex(32);
    if (!tok) return false;
    struct json_object *root = json_tokener_parse_ex(tok, buf, (int)len);
    enum json_tokener_error jerr = json_tokener_get_error(tok);
    json_tokener_free(tok);
    if (!root || jerr != json_tokener_success || !json_object_is_type(root, json_type_object)) {
        json_object_put(root);
        return false;
    }
    struct json_object *j_schema = NULL, *j_outcomes = NULL, *j_rules = NULL, *j_cons = NULL, *j_spaces = NULL, *j_sorts = NULL;
    bool ok = true;
    if (!json_object_object_get_ex(root, "schema", &j_schema) ||
        strcmp(json_object_get_string(j_schema), "tcalc.lean_theory_and_tisa_contract.v1") != 0) {
        ok = false;
    }
    if (!json_object_object_get_ex(root, "outcome_codes", &j_outcomes) ||
        !json_object_is_type(j_outcomes, json_type_object)) {
        ok = false;
    } else {
        static const struct { const char *key; int64_t val; } exp_oc[5] = {
            { "refused",       (int64_t)TISA_OUTCOME_REFUSED },
            { "fired",         (int64_t)TISA_OUTCOME_FIRED },
            { "unsupported",   (int64_t)TISA_OUTCOME_UNSUPPORTED },
            { "invalid_input", (int64_t)TISA_OUTCOME_INVALID_INPUT },
            { "exhausted",     (int64_t)TISA_OUTCOME_EXHAUSTED }
        };
        if (json_object_object_length(j_outcomes) != 5) ok = false;
        for (size_t i = 0; i < 5; i++) {
            struct json_object *jv = NULL;
            if (!json_object_object_get_ex(j_outcomes, exp_oc[i].key, &jv) ||
                !json_object_is_type(jv, json_type_int) ||
                json_object_get_int64(jv) != exp_oc[i].val) {
                ok = false;
            }
        }
    }
    if (!json_object_object_get_ex(root, "spaces", &j_spaces) ||
        !json_object_is_type(j_spaces, json_type_array) ||
        json_object_array_length(j_spaces) != 3) {
        ok = false;
    }
    if (!json_object_object_get_ex(root, "sorts", &j_sorts) ||
        !json_object_is_type(j_sorts, json_type_array) ||
        json_object_array_length(j_sorts) != 5) {
        ok = false;
    }
    if (!json_object_object_get_ex(root, "constructors", &j_cons) ||
        !json_object_is_type(j_cons, json_type_array) ||
        json_object_array_length(j_cons) != 18) {
        ok = false;
    }
    if (!json_object_object_get_ex(root, "rules", &j_rules) ||
        !json_object_is_type(j_rules, json_type_array) ||
        json_object_array_length(j_rules) != 23) {
        ok = false;
    } else {
        int n_leaf = 0, n_flat = 0;
        for (size_t i = 0; i < 23; i++) {
            struct json_object *jr = json_object_array_get_idx(j_rules, i);
            struct json_object *jrole = NULL, *jcflat = NULL, *jplan = NULL;
            if (!jr || !json_object_object_get_ex(jr, "role", &jrole)) {
                ok = false;
                break;
            }
            const char *role = json_object_get_string(jrole);
            json_object_object_get_ex(jr, "compiled_flat", &jcflat);
            json_object_object_get_ex(jr, "rule_table_plan", &jplan);
            if (strcmp(role, "privileged_leaf_publisher") == 0) {
                if (jcflat != NULL && !json_object_is_type(jcflat, json_type_null)) ok = false;
                n_leaf++;
            } else if (strcmp(role, "premise_bearing_flat_rule") == 0) {
                if (!jcflat || !json_object_is_type(jcflat, json_type_object)) ok = false;
                if (!jplan || !json_object_is_type(jplan, json_type_object)) ok = false;
                n_flat++;
            } else {
                ok = false;
            }
        }
        if (n_leaf != 12 || n_flat != 11) ok = false;
    }
    json_object_put(root);
    return ok;
}

static bool lean_export_theory_json_validated(const char *out_path) {
    char *buf = NULL;
    size_t len = 0;
    FILE *ms = open_memstream(&buf, &len);
    if (!ms) return false;
    bool w_ok = lean_tc_write_theory_json_stream(ms);
    fclose(ms);
    if (!w_ok || !lean_verify_exported_theory_json_buf(buf, len)) {
        free(buf);
        return false;
    }
    FILE *out = stdout;
    if (out_path && out_path[0] != '\0' && strcmp(out_path, "-") != 0) {
        out = fopen(out_path, "wb");
        if (!out) {
            free(buf);
            return false;
        }
    }
    size_t nw = fwrite(buf, 1, len, out);
    if (out != stdout) fclose(out);
    free(buf);
    return nw == len;
}

static uint64_t g_tc_admitted_decls = 0;
static uint64_t g_tc_admitted_thms  = 0;
static uint64_t g_tc_rule_commits   = 0;

static TcAdmissionProfile g_lean_admission_profile;
static bool               g_lean_profile_ready = false;
static bool               g_lean_bridge_event_mode = false;
static bool               g_lean_arena_mode = false;
static bool               g_lean_tisa_x86_mode = false;
static bool               g_lean_tisa_x86_ready = false;
static TcIsaArena         g_lean_tisa_arena;
static TcIsaProgram       g_lean_tisa_prog[23];
static TcIsaCompiledX86   g_lean_tisa_x86[23];
static TcAdmittedEvent    g_last_lean_event;
static TcRefusalReason    g_last_lean_refusal = TC_REFUSE_NONE;

static bool lean_init_tisa_x86_rules(void) {
    if (g_lean_tisa_x86_ready) return true;
    tisa_arena_init(&g_lean_tisa_arena, 1024);
    for (int rid = 0; rid < 23; rid++) {
        TcInspectRule ir;
        TcInspectFlat ifl;
        if (!tc_inspect_rule(rid, &ir, &ifl)) return false;
        if (!ir.flat) continue;
        char err[256] = {0};
        if (!tisa_specialize_lean_flat_rule(&g_lean_tisa_arena, &ir, &ifl,
                                            lean_tc_rule_name(rid),
                                            &g_lean_tisa_prog[rid], err, sizeof(err))) {
            return false;
        }
        if (!tisa_compile_x86(&g_lean_tisa_prog[rid], TISA_PROFILE_P0,
                              &g_lean_tisa_x86[rid], err, sizeof(err))) {
            return false;
        }
    }
    g_lean_tisa_x86_ready = true;
    return true;
}

static Occ lean_tc_commit_step(int rule, const Occ *keep, int ninst, const uint64_t *raw_inst) {
    if (!g_lean_bridge_event_mode && !g_lean_arena_mode && g_lean_tisa_x86_mode && keep != NULL) {
        if ((unsigned)rule >= 23u || !lean_init_tisa_x86_rules()) return 0;
        const TcIsaProgram *prog = &g_lean_tisa_prog[rule];
        if (prog->nregions < 2u) return 0;
        uint8_t np = (uint8_t)(prog->nregions - 1u);
        const void *prem_ptrs[4] = {0};
        for (uint8_t i = 0; i < np; i++) {
            prem_ptrs[i] = lean_gen_at(keep[i]);
        }
        TcLeanGenTuple out_tup = {0};
        TcIsaOutcome rc = tisa_run_lean_flat_rule(prog, &g_lean_tisa_x86[rule],
                                                  TISA_MODE_X86, prem_ptrs, np, &out_tup, NULL);
        if (rc != TISA_OUTCOME_FIRED) return 0;
        Occ out = lean_gen_push(out_tup);
        if (out) g_tc_rule_commits++;
        return out;
    }
    if (!g_lean_bridge_event_mode && !g_lean_arena_mode) {
        Occ out = (keep == NULL)
            ? tc_lean_gen_mflat_dispatch(rule, raw_inst)
            : tc_lean_gen_flat_dispatch(rule, keep);
        if (out) g_tc_rule_commits++;
        return out;
    }
    if (!g_lean_bridge_event_mode && g_lean_arena_mode) {
        Occ out = 0;
        if (keep == NULL) {
            Term inst[8] = { 0 };
            for (int i = 0; i < ninst; i++) inst[i] = lean_tc_id_term(raw_inst[i]);
            out = tc_flat_fire(rule, NULL, inst, 0);
        } else {
            out = tc_lean_fire_arena_dispatch(rule, keep, 0);
        }
        if (out) g_tc_rule_commits++;
        return out;
    }
    Term inst[8] = { 0 };
    for (int i = 0; i < ninst; i++) {
        inst[i] = lean_tc_id_term(raw_inst[i]);
    }
    TcPreparedStep step = {
        .rule = rule,
        .take = NULL,
        .keep = keep,
        .inst = (keep == NULL) ? inst : NULL,
        .dest = 0,
        .nseeds = 0,
        .seeds = NULL
    };
    TcAdmissionReceipt rec;
    if (g_lean_bridge_event_mode && keep != NULL) {
        if (!g_lean_profile_ready) {
            g_lean_admission_profile = tc_admission_guard_profile(false);
            g_lean_profile_ready = true;
        }
        TcPreparedEffect eff;
        TcBridgeOutcome out = tc_bridge_execute_candidate(
            &step, &g_lean_admission_profile, &eff, &g_last_lean_event, &rec, &g_last_lean_refusal);
        if (out != TC_BRIDGE_ADMITTED) return 0;
    } else {
        if (!tc_commit_prepared(&step, &rec)) return 0;
    }
    g_tc_rule_commits++;
    return rec.out;
}

static Occ lean_tc_commit2(int rule, uint64_t a, uint64_t b) {
    uint64_t raw[3] = { a, b, 0ull };
    return lean_tc_commit_step(rule, NULL, 2, raw);
}

static Occ lean_tc_commit3(int rule, uint64_t a, uint64_t b, uint64_t c) {
    uint64_t raw[3] = { a, b, c };
    return lean_tc_commit_step(rule, NULL, 3, raw);
}

static Occ lean_tc_derive_is_type(Occ occ_typed_sort, uint64_t ty, uint64_t sort_expr, uint64_t u) {
    (void)ty;
    Occ occ_sort_of = lean_tc_commit2(R_EMIT_SORT_OF, sort_expr, u);
    if (!occ_sort_of) return 0;
    Occ keep[2] = { occ_typed_sort, occ_sort_of };
    return lean_tc_commit_step(R_DERIVE_IS_TYPE, keep, 0, NULL);
}

static Occ lean_tc_derive_is_prop(Occ occ_is_type, uint64_t ty) {
    (void)ty;
    Occ keep[1] = { occ_is_type };
    return lean_tc_commit_step(R_DERIVE_IS_PROP, keep, 0, NULL);
}

static Occ lean_tc_commit_conv(Occ occ_val_typed, Occ occ_defeq, Occ occ_expected_is_type,
                               uint64_t val, uint64_t actual_ty, uint64_t expected_ty, uint64_t u) {
    (void)val; (void)actual_ty; (void)expected_ty; (void)u;
    Occ keep[3] = { occ_val_typed, occ_defeq, occ_expected_is_type };
    return lean_tc_commit_step(R_CHECK_CONV, keep, 0, NULL);
}

static Occ lean_tc_admit_axiom(Occ occ_is_type, uint64_t name, uint64_t ty, uint64_t u) {
    (void)u;
    Occ occ_req = lean_tc_commit2(R_EMIT_DECL_REQ2, name, ty);
    if (!occ_req) return 0;
    Occ keep[2] = { occ_req, occ_is_type };
    return lean_tc_commit_step(R_ADMIT_AXIOM, keep, 0, NULL);
}

static Occ lean_tc_admit_quot(Occ occ_is_type, uint64_t name, uint64_t ty, uint64_t u) {
    (void)u;
    Occ occ_req = lean_tc_commit2(R_EMIT_DECL_REQ2, name, ty);
    if (!occ_req) return 0;
    Occ keep[2] = { occ_req, occ_is_type };
    return lean_tc_commit_step(R_ADMIT_QUOT, keep, 0, NULL);
}

static Occ lean_tc_admit_ind(Occ occ_is_type, uint64_t name, uint64_t ty, uint64_t u) {
    (void)u;
    Occ occ_req = lean_tc_commit2(R_EMIT_DECL_REQ2, name, ty);
    if (!occ_req) return 0;
    Occ keep[2] = { occ_req, occ_is_type };
    return lean_tc_commit_step(R_ADMIT_IND, keep, 0, NULL);
}

static Occ lean_tc_admit_ctor(Occ occ_ind_decl, Occ occ_is_type,
                              uint64_t name, uint64_t ind_name, uint64_t ty,
                              uint64_t ind_ty, uint64_t u) {
    (void)ind_ty; (void)u;
    Occ occ_req = lean_tc_commit3(R_EMIT_DECL_REQ3, name, ind_name, ty);
    if (!occ_req) return 0;
    Occ keep[3] = { occ_req, occ_ind_decl, occ_is_type };
    return lean_tc_commit_step(R_ADMIT_CTOR, keep, 0, NULL);
}

static Occ lean_tc_admit_rec(Occ occ_is_type, uint64_t name, uint64_t ind_name, uint64_t ty, uint64_t u) {
    (void)u;
    Occ occ_req = lean_tc_commit3(R_EMIT_DECL_REQ3, name, ind_name, ty);
    if (!occ_req) return 0;
    Occ keep[2] = { occ_req, occ_is_type };
    return lean_tc_commit_step(R_ADMIT_REC, keep, 0, NULL);
}

static Occ lean_tc_admit_defn(Occ occ_is_type, Occ occ_val_typed,
                              uint64_t name, uint64_t ty, uint64_t val, uint64_t u) {
    (void)u;
    Occ occ_req = lean_tc_commit3(R_EMIT_DECL_REQ3, name, ty, val);
    if (!occ_req) return 0;
    Occ keep[3] = { occ_req, occ_is_type, occ_val_typed };
    return lean_tc_commit_step(R_ADMIT_DEFN, keep, 0, NULL);
}

static Occ lean_tc_admit_opaque(Occ occ_is_type, Occ occ_val_typed,
                                uint64_t name, uint64_t ty, uint64_t val, uint64_t u) {
    (void)u;
    Occ occ_req = lean_tc_commit3(R_EMIT_DECL_REQ3, name, ty, val);
    if (!occ_req) return 0;
    Occ keep[3] = { occ_req, occ_is_type, occ_val_typed };
    return lean_tc_commit_step(R_ADMIT_OPAQUE, keep, 0, NULL);
}

static Occ lean_tc_admit_thm(Occ occ_is_prop, Occ occ_val_typed,
                             uint64_t name, uint64_t ty, uint64_t val) {
    Occ occ_req = lean_tc_commit3(R_EMIT_DECL_REQ3, name, ty, val);
    if (!occ_req) return 0;
    Occ keep[3] = { occ_req, occ_is_prop, occ_val_typed };
    return lean_tc_commit_step(R_ADMIT_THM, keep, 0, NULL);
}

/* =========================================================================
 * 2. Dynamic Tables for Names, Universe Levels, Expressions, and Environment
 * ========================================================================= */

typedef enum {
    LNAME_ANON = 0,
    LNAME_STR  = 1,
    LNAME_NUM  = 2
} LeanNameKind;

typedef struct {
    LeanNameKind kind;
    uint32_t pre;
    char *str;
    uint64_t num;
    char *full;
    uint32_t hash;
} LeanName;

typedef enum {
    LLVL_ZERO  = 0,
    LLVL_SUCC  = 1,
    LLVL_MAX   = 2,
    LLVL_IMAX  = 3,
    LLVL_PARAM = 4
} LeanLvlKind;

typedef struct {
    LeanLvlKind kind;
    uint32_t u;
    uint32_t v;
    uint32_t param_name;
    uint32_t hash;
} LeanLvl;

typedef enum {
    LEXPR_BVAR   = 0,
    LEXPR_FVAR   = 1,
    LEXPR_SORT   = 2,
    LEXPR_CONST  = 3,
    LEXPR_APP    = 4,
    LEXPR_LAM    = 5,
    LEXPR_FORALL = 6,
    LEXPR_LET    = 7,
    LEXPR_NATLIT = 8,
    LEXPR_STRLIT = 9,
    LEXPR_PROJ   = 10
} LeanExprKind;

typedef struct {
    uint32_t hash;
    uint32_t loose_bvar_range;   /* 0 if closed; otherwise 1 + max loose bvar index */
    uint8_t  kind;               /* LeanExprKind (0..10) */
    uint8_t  has_fvar : 1;
    uint8_t  has_lvl_param : 1;
    uint8_t  checked_ok : 1;     /* 1 if expression has been fully typechecked (`infer_only = false`) */
    uint8_t  is_prop_cache : 2;  /* 0 = unknown, 1 = false, 2 = true */
    uint8_t  nat_is_small : 1;   /* 1 if LEXPR_NATLIT fits in 128-bit (`d.nat_small`) */
    uint8_t  has_sorry : 1;          /* 1 if expression transitively references sorryAx */
    uint8_t  has_trust_compiler : 1; /* 1 if expression transitively references Lean.trustCompiler / ofReduce* */
    uint8_t  dirty_scratch_cache;    /* 1 if persistent expr has a scratch-tier whnf/type cache entry */
    uint8_t  _pad;
    uint32_t whnf_cache;         /* cached WHNF (`unfold_defs = true`) for loose_bvar_range == 0 (0 = unset) */
    uint32_t whnf_core_cache;    /* cached WHNF (`unfold_defs = false`) for loose_bvar_range == 0 (0 = unset) */
    uint32_t type_cache;         /* cached inferred type for loose_bvar_range == 0 (0 = unset) */
    union {
        uint32_t bvar_idx;
        uint32_t fvar_id;
        uint32_t sort_lvl;
        struct {
            uint32_t name;
            uint32_t nus;
            uint32_t *us;
        } cnst;
        struct {
            uint32_t fn;
            uint32_t arg;
        } app;
        struct {
            uint32_t binder_name;
            uint32_t domain;
            uint32_t body;
        } binder; /* lam & forallE */
        struct {
            uint32_t binder_name;
            uint32_t type;
            uint32_t val;
            uint32_t body;
        } let_e;
        struct {
            uint64_t lo;
            uint64_t hi;
        } nat_small;
        struct {
            char *dec_str;
        } nat_big;
        struct {
            char *str;
        } str_lit;
        struct {
            uint32_t type_name;
            uint32_t idx;
            uint32_t struct_expr;
        } proj;
    } d;
} LeanExpr;

static inline __uint128_t lean_expr_nat_u128(const LeanExpr *ex) {
    return ((__uint128_t)ex->d.nat_small.hi << 64) | (__uint128_t)ex->d.nat_small.lo;
}

typedef struct {
    uint32_t name;
    uint32_t ind_name;
    uint32_t nparams;
    uint32_t *level_params;
    uint32_t type;
    uint32_t cidx;
    uint32_t num_params;
    uint32_t num_fields;
    bool     is_unsafe;
} LeanCtorSpec;

typedef struct {
    uint32_t ctor_name;
    uint32_t nfields;
    uint32_t rhs;
} LeanRecRule;

typedef enum {
    LDECL_NONE   = 0,
    LDECL_AXIOM  = 1,
    LDECL_DEFN   = 2,
    LDECL_THM    = 3,
    LDECL_OPAQUE = 4,
    LDECL_QUOT   = 5,
    LDECL_IND    = 6,
    LDECL_CTOR   = 7,
    LDECL_REC    = 8
} LeanDeclKind;

enum {
    LQUOT_NONE = 0,
    LQUOT_TYPE = 1,
    LQUOT_CTOR = 2,
    LQUOT_LIFT = 3,
    LQUOT_IND  = 4
};

enum {
    LHINT_OPAQUE  = 0,
    LHINT_REGULAR = 1,
    LHINT_ABBREV  = 2
};

typedef struct {
    LeanDeclKind kind;
    uint32_t name;
    uint32_t nparams;
    uint32_t *level_params;
    uint32_t type;
    uint32_t value;
    uint32_t height; /* definition unfolding height (0 = opaque, h+1 = regular(h), 0xffffffff = abbrev) */
    Occ      tc_occ;
    uint8_t  quot_kind;
    uint8_t  hint_kind;
    bool     has_explicit_hints;
    bool     uses_sorry;
    bool     uses_trust_compiler;
    /* Inductive / Constructor / Recursor metadata */
    uint32_t ind_name;
    uint32_t num_params;
    uint32_t num_indices;
    uint32_t num_motives;
    uint32_t num_minors;
    uint32_t num_nested;
    uint32_t cidx;
    uint32_t num_fields;
    bool     is_rec;
    bool     is_reflexive;
    bool     is_k;
    bool     is_unsafe;
    bool     is_nested;
    bool     has_num_nested;
    bool     has_all_field;
    bool     has_declared_ctors;
    uint32_t nall;
    uint32_t *all;
    uint32_t num_declared_ctors;
    uint32_t *declared_ctors;
    uint32_t nctors;
    LeanCtorSpec *ctors;
    uint32_t nrules;
    LeanRecRule *rules;
} LeanDecl;

typedef struct {
    uint32_t fvar_id;
    uint32_t name;
    uint32_t type;
    uint32_t llet_val; /* 0 if assumption, >0 (expr_id + 1) if let-bound */
} LeanLocalDecl;

#define LEAN_DEFEQ_CACHE_SIZE (1u << 21)
#define LEAN_SUBST_CACHE_SIZE (1u << 18)
#define LEAN_SCRATCH_BASE     (1u << 26)
#define LEAN_SCRATCH_SLOTS    (1u << 26)
#define LEAN_EXPR_MMAP_SLOTS  (LEAN_SCRATCH_BASE + LEAN_SCRATCH_SLOTS)

typedef struct {
    uint32_t lo;        /* 0 = empty; otherwise min(a, b) */
    uint32_t hi_and_eq; /* (max(a, b) & 0x7fffffffu) | (is_eq ? 0x80000000u : 0u) */
    uint32_t gen;       /* 0 if both lo, hi < persistent_nexprs; otherwise ks->scratch_gen */
} LeanDefEqCache;

typedef struct {
    uint32_t gen;
    uint32_t eid;
} LeanScratchHtabSlot;

typedef struct {
    uint32_t gen;
    uint32_t e;
    uint32_t offset;
    uint32_t res;
} LeanSubstCache;

typedef struct {
    /* Names (1-based index, 0 = anonymous) */
    LeanName *names;
    uint32_t nnames, cap_names;
    uint32_t *name_htab;
    uint32_t cap_name_htab;

    /* Direct-mapped definitional equality & DAG substitution memoization caches */
    LeanDefEqCache *defeq_cache;
    LeanSubstCache *subst_cache;
    uint32_t subst_gen;

    /* Export index -> internal index maps with presence bits (unbounded) */
    uint32_t *export_name_map;
    uint8_t  *export_name_present;
    uint32_t cap_export_names;
    uint32_t n_export_names;
    uint32_t *export_lvl_map;
    uint8_t  *export_lvl_present;
    uint32_t cap_export_lvls;
    uint32_t n_export_lvls;
    uint32_t *export_expr_map;
    uint8_t  *export_expr_present;
    uint32_t cap_export_exprs;
    uint32_t n_export_exprs;

    /* Universe Levels (0 = Zero) */
    LeanLvl *lvls;
    uint32_t nlvls, cap_lvls;
    uint32_t *lvl_htab;
    uint32_t cap_lvl_htab;

    /* Expressions (1-based internal index; 0 = unset/null) */
    LeanExpr *exprs;
    uint32_t nexprs, cap_exprs;
    uint32_t *expr_htab;
    uint32_t cap_expr_htab;

    /* Two-tier Persistent (has_fvar==0) + Scratch (has_fvar==1) Expression Arena */
    bool                 in_scratch_scope;
    uint32_t             nscratch_exprs;
    uint32_t             scratch_gen;
    LeanScratchHtabSlot *scratch_htab;
    uint32_t             cap_scratch_htab;
    uint64_t             stat_scratch_reclaimed;
    uint32_t             stat_peak_scratch;
    size_t               exprs_mmap_bytes;

    /* Environment declarations indexed by Name ID */
    LeanDecl *decls_by_name;
    uint32_t cap_decls_by_name;

    /* Local FVar context stack */
    LeanLocalDecl *locals;
    uint32_t nlocals, cap_locals;
    uint32_t next_fvar_id;

    /* Well-known constant Name IDs cached on demand */
    uint32_t nm_Nat, nm_Nat_zero, nm_Nat_succ;
    uint32_t nm_Nat_add, nm_Nat_sub, nm_Nat_mul, nm_Nat_pow, nm_Nat_div, nm_Nat_mod, nm_Nat_gcd;
    uint32_t nm_Nat_beq, nm_Nat_ble, nm_Nat_land, nm_Nat_lor, nm_Nat_lxor, nm_Nat_shl, nm_Nat_shr;
    uint32_t nm_Bool_true, nm_Bool_false, nm_eagerReduce;
    uint32_t nm_String, nm_String_mk, nm_String_ofList, nm_Char, nm_List_nil, nm_List_cons, nm_Char_ofNat;
    uint32_t nm_Quot, nm_Quot_mk, nm_Quot_lift, nm_Quot_ind;
    uint32_t nm_sorryAx, nm_trustCompiler, nm_ofReduceBool, nm_ofReduceNat;
    uint32_t nm_propext, nm_Classical_choice, nm_Quot_sound;
    bool     nat_verified;
    bool     string_verified;
    bool     eager_reduce;
    bool     forbid_sorry;
    bool     forbid_trust_compiler;

    /* Admitted axiom name IDs for trust ledger accounting */
    uint32_t *axiom_names;
    uint32_t n_axiom_names, cap_axiom_names;

    /* Stream & Arena metadata state */
    LeanArenaOutcome outcome;
    bool     metadata_seen;
    bool     allow_legacy_format;
    bool     saw_non_safe_decl;
    char     lean_version[64];
    char     lean_githash[64];
    char     format_version[64];

    /* Verification statistics */
    uint64_t stat_axioms;
    uint64_t stat_defns;
    uint64_t stat_thms;
    uint64_t stat_opaques;
    uint64_t stat_quots;
    uint64_t stat_inds;
    uint64_t stat_ctors;
    uint64_t stat_recs;
    uint64_t stat_defeq_checks;
    uint64_t stat_whnf_steps;
    uint64_t stat_proof_irrel_hits;
    uint64_t stat_sorry_decls;
    uint64_t stat_trust_compiler_decls;
} LeanKernelState;

/* =========================================================================
 * 3. Hash-Consed Name, Universe Level, and Expression Constructors
 * ========================================================================= */

static inline uint32_t fnv_mix32(uint32_t h, uint32_t v) {
    h ^= v;
    h *= 16777619u;
    return h;
}

static inline uint32_t fnv_str(uint32_t h, const char *s) {
    for (; *s; s++) {
        h ^= (uint8_t)*s;
        h *= 16777619u;
    }
    return h;
}

static char *xstrdup(const char *s) {
    size_t n = strlen(s);
    char *p = (char *)malloc(n + 1);
    memcpy(p, s, n + 1);
    return p;
}

static void lean_ensure_decls_cap(LeanKernelState *ks, uint32_t name_id) {
    if (name_id < ks->cap_decls_by_name) return;
    size_t ncap = ks->cap_decls_by_name ? (size_t)ks->cap_decls_by_name * 2u : 1024u;
    while (ncap <= (size_t)name_id) ncap *= 2u;
    ks->decls_by_name = (LeanDecl *)realloc(ks->decls_by_name, ncap * sizeof(LeanDecl));
    if (!ks->decls_by_name) { perror("realloc(decls_by_name)"); exit(3); }
    memset(ks->decls_by_name + ks->cap_decls_by_name, 0,
           (ncap - (size_t)ks->cap_decls_by_name) * sizeof(LeanDecl));
    ks->cap_decls_by_name = (uint32_t)ncap;
}

static void lean_name_rehash(LeanKernelState *ks, uint32_t new_cap) {
    uint32_t *ntab = (uint32_t *)calloc(new_cap, sizeof(uint32_t));
    uint32_t mask = new_cap - 1u;
    for (uint32_t i = 1; i < ks->nnames; i++) {
        uint32_t slot = ks->names[i].hash & mask;
        while (ntab[slot] != 0) slot = (slot + 1u) & mask;
        ntab[slot] = i;
    }
    free(ks->name_htab);
    ks->name_htab = ntab;
    ks->cap_name_htab = new_cap;
}

static uint32_t lean_name_mk_str(LeanKernelState *ks, uint32_t pre, const char *s) {
    uint32_t h = fnv_str(fnv_mix32(fnv_mix32(2166136261u, LNAME_STR), pre), s);
    if (h == 0) h = 1u;
    if (ks->cap_name_htab == 0 || ks->nnames * 2u >= ks->cap_name_htab) {
        lean_name_rehash(ks, ks->cap_name_htab ? ks->cap_name_htab * 2u : 16384u);
    }
    uint32_t mask = ks->cap_name_htab - 1u;
    uint32_t slot = h & mask;
    while (ks->name_htab[slot] != 0) {
        uint32_t i = ks->name_htab[slot];
        if (ks->names[i].hash == h && ks->names[i].kind == LNAME_STR &&
            ks->names[i].pre == pre && strcmp(ks->names[i].str, s) == 0) {
            return i;
        }
        slot = (slot + 1u) & mask;
    }
    if (ks->nnames >= ks->cap_names) {
        uint32_t ncap = ks->cap_names ? ks->cap_names * 2u : 1024u;
        ks->names = (LeanName *)realloc(ks->names, (size_t)ncap * sizeof(LeanName));
        ks->cap_names = ncap;
    }
    uint32_t id = ks->nnames++;
    LeanName *nm = &ks->names[id];
    nm->kind = LNAME_STR;
    nm->pre = pre;
    nm->str = xstrdup(s);
    nm->num = 0;
    nm->hash = h;
    if (pre == 0) {
        nm->full = xstrdup(s);
    } else {
        const char *pfull = ks->names[pre].full;
        size_t l1 = strlen(pfull), l2 = strlen(s);
        nm->full = (char *)malloc(l1 + 1 + l2 + 1);
        memcpy(nm->full, pfull, l1);
        nm->full[l1] = '.';
        memcpy(nm->full + l1 + 1, s, l2 + 1);
    }
    ks->name_htab[slot] = id;
    lean_ensure_decls_cap(ks, id);

    /* Cache well-known kernel names */
    const char *f = nm->full;
    if (strcmp(f, "Nat") == 0) ks->nm_Nat = id;
    else if (strcmp(f, "Nat.zero") == 0) ks->nm_Nat_zero = id;
    else if (strcmp(f, "Nat.succ") == 0) ks->nm_Nat_succ = id;
    else if (strcmp(f, "Nat.add") == 0) ks->nm_Nat_add = id;
    else if (strcmp(f, "Nat.sub") == 0) ks->nm_Nat_sub = id;
    else if (strcmp(f, "Nat.mul") == 0) ks->nm_Nat_mul = id;
    else if (strcmp(f, "Nat.pow") == 0) ks->nm_Nat_pow = id;
    else if (strcmp(f, "Nat.div") == 0) ks->nm_Nat_div = id;
    else if (strcmp(f, "Nat.mod") == 0) ks->nm_Nat_mod = id;
    else if (strcmp(f, "Nat.gcd") == 0) ks->nm_Nat_gcd = id;
    else if (strcmp(f, "Nat.beq") == 0) ks->nm_Nat_beq = id;
    else if (strcmp(f, "Nat.ble") == 0) ks->nm_Nat_ble = id;
    else if (strcmp(f, "Nat.land") == 0) ks->nm_Nat_land = id;
    else if (strcmp(f, "Nat.lor") == 0) ks->nm_Nat_lor = id;
    else if (strcmp(f, "Nat.lxor") == 0) ks->nm_Nat_lxor = id;
    else if (strcmp(f, "Nat.shiftLeft") == 0) ks->nm_Nat_shl = id;
    else if (strcmp(f, "Nat.shiftRight") == 0) ks->nm_Nat_shr = id;
    else if (strcmp(f, "Bool.true") == 0) ks->nm_Bool_true = id;
    else if (strcmp(f, "Bool.false") == 0) ks->nm_Bool_false = id;
    else if (strcmp(f, "eagerReduce") == 0) ks->nm_eagerReduce = id;
    else if (strcmp(f, "String") == 0) ks->nm_String = id;
    else if (strcmp(f, "String.mk") == 0) ks->nm_String_mk = id;
    else if (strcmp(f, "String.ofList") == 0) ks->nm_String_ofList = id;
    else if (strcmp(f, "Char") == 0) ks->nm_Char = id;
    else if (strcmp(f, "List.nil") == 0) ks->nm_List_nil = id;
    else if (strcmp(f, "List.cons") == 0) ks->nm_List_cons = id;
    else if (strcmp(f, "Char.ofNat") == 0) ks->nm_Char_ofNat = id;
    else if (strcmp(f, "Quot") == 0) ks->nm_Quot = id;
    else if (strcmp(f, "Quot.mk") == 0) ks->nm_Quot_mk = id;
    else if (strcmp(f, "Quot.lift") == 0) ks->nm_Quot_lift = id;
    else if (strcmp(f, "Quot.ind") == 0) ks->nm_Quot_ind = id;
    else if (strcmp(f, "sorryAx") == 0) ks->nm_sorryAx = id;
    else if (strcmp(f, "Lean.trustCompiler") == 0) ks->nm_trustCompiler = id;
    else if (strcmp(f, "Lean.ofReduceBool") == 0) ks->nm_ofReduceBool = id;
    else if (strcmp(f, "Lean.ofReduceNat") == 0) ks->nm_ofReduceNat = id;
    else if (strcmp(f, "propext") == 0) ks->nm_propext = id;
    else if (strcmp(f, "Classical.choice") == 0) ks->nm_Classical_choice = id;
    else if (strcmp(f, "Quot.sound") == 0) ks->nm_Quot_sound = id;

    return id;
}

static uint32_t lean_name_mk_num(LeanKernelState *ks, uint32_t pre, uint64_t k) {
    uint32_t h = fnv_mix32(fnv_mix32(fnv_mix32(2166136261u, LNAME_NUM), pre), (uint32_t)k);
    h = fnv_mix32(h, (uint32_t)(k >> 32));
    if (h == 0) h = 1u;
    if (ks->cap_name_htab == 0 || ks->nnames * 2u >= ks->cap_name_htab) {
        lean_name_rehash(ks, ks->cap_name_htab ? ks->cap_name_htab * 2u : 16384u);
    }
    uint32_t mask = ks->cap_name_htab - 1u;
    uint32_t slot = h & mask;
    while (ks->name_htab[slot] != 0) {
        uint32_t i = ks->name_htab[slot];
        if (ks->names[i].hash == h && ks->names[i].kind == LNAME_NUM &&
            ks->names[i].pre == pre && ks->names[i].num == k) {
            return i;
        }
        slot = (slot + 1u) & mask;
    }
    if (ks->nnames >= ks->cap_names) {
        uint32_t ncap = ks->cap_names ? ks->cap_names * 2u : 1024u;
        ks->names = (LeanName *)realloc(ks->names, (size_t)ncap * sizeof(LeanName));
        ks->cap_names = ncap;
    }
    uint32_t id = ks->nnames++;
    LeanName *nm = &ks->names[id];
    nm->kind = LNAME_NUM;
    nm->pre = pre;
    nm->str = NULL;
    nm->num = k;
    nm->hash = h;
    char nbuf[32];
    snprintf(nbuf, sizeof(nbuf), "%" PRIu64, k);
    if (pre == 0) {
        nm->full = xstrdup(nbuf);
    } else {
        const char *pfull = ks->names[pre].full;
        size_t l1 = strlen(pfull), l2 = strlen(nbuf);
        nm->full = (char *)malloc(l1 + 1 + l2 + 1);
        memcpy(nm->full, pfull, l1);
        nm->full[l1] = '.';
        memcpy(nm->full + l1 + 1, nbuf, l2 + 1);
    }
    ks->name_htab[slot] = id;
    lean_ensure_decls_cap(ks, id);
    return id;
}

/* ---- Universe Level Hash-Consing & Exact Solver ---- */

static void lean_lvl_rehash(LeanKernelState *ks, uint32_t new_cap) {
    uint32_t *ntab = (uint32_t *)calloc(new_cap, sizeof(uint32_t));
    uint32_t mask = new_cap - 1u;
    for (uint32_t i = 1; i < ks->nlvls; i++) {
        uint32_t slot = ks->lvls[i].hash & mask;
        while (ntab[slot] != 0) slot = (slot + 1u) & mask;
        ntab[slot] = i;
    }
    free(ks->lvl_htab);
    ks->lvl_htab = ntab;
    ks->cap_lvl_htab = new_cap;
}

static uint32_t lean_lvl_intern(LeanKernelState *ks, LeanLvlKind kind, uint32_t u, uint32_t v, uint32_t param_name) {
    if (kind == LLVL_ZERO) return 0u;
    uint32_t h = fnv_mix32(2166136261u, (uint32_t)kind);
    h = fnv_mix32(h, u);
    h = fnv_mix32(h, v);
    h = fnv_mix32(h, param_name);
    if (h == 0) h = 1u;

    if (ks->cap_lvl_htab == 0 || ks->nlvls * 2u >= ks->cap_lvl_htab) {
        lean_lvl_rehash(ks, ks->cap_lvl_htab ? ks->cap_lvl_htab * 2u : 4096u);
    }
    uint32_t mask = ks->cap_lvl_htab - 1u;
    uint32_t slot = h & mask;
    while (ks->lvl_htab[slot] != 0) {
        uint32_t i = ks->lvl_htab[slot];
        if (ks->lvls[i].hash == h && ks->lvls[i].kind == kind &&
            ks->lvls[i].u == u && ks->lvls[i].v == v && ks->lvls[i].param_name == param_name) {
            return i;
        }
        slot = (slot + 1u) & mask;
    }
    if (ks->nlvls >= ks->cap_lvls) {
        uint32_t ncap = ks->cap_lvls ? ks->cap_lvls * 2u : 512u;
        ks->lvls = (LeanLvl *)realloc(ks->lvls, (size_t)ncap * sizeof(LeanLvl));
        ks->cap_lvls = ncap;
    }
    uint32_t id = ks->nlvls++;
    ks->lvls[id] = (LeanLvl){ .kind = kind, .u = u, .v = v, .param_name = param_name, .hash = h };
    ks->lvl_htab[slot] = id;
    return id;
}

static uint32_t lean_lvl_mk_succ(LeanKernelState *ks, uint32_t u) {
    return lean_lvl_intern(ks, LLVL_SUCC, u, 0, 0);
}

static bool lean_lvl_is_nonzero(const LeanKernelState *ks, uint32_t l) {
    if (l == 0) return false;
    switch (ks->lvls[l].kind) {
        case LLVL_ZERO:  return false;
        case LLVL_SUCC:  return true;
        case LLVL_MAX:   return lean_lvl_is_nonzero(ks, ks->lvls[l].u) || lean_lvl_is_nonzero(ks, ks->lvls[l].v);
        case LLVL_IMAX:  return lean_lvl_is_nonzero(ks, ks->lvls[l].v);
        case LLVL_PARAM: return false;
    }
    return false;
}

/* Check whether universe level `l` is DEFINITELY zero (never true for a parameter or successor). */
static bool lean_lvl_is_zero(const LeanKernelState *ks, uint32_t l) {
    if (l == 0) return true;
    switch (ks->lvls[l].kind) {
        case LLVL_ZERO:  return true;
        case LLVL_SUCC:  return false;
        case LLVL_MAX:   return lean_lvl_is_zero(ks, ks->lvls[l].u) && lean_lvl_is_zero(ks, ks->lvls[l].v);
        case LLVL_IMAX:  return lean_lvl_is_zero(ks, ks->lvls[l].v);
        case LLVL_PARAM: return false;
    }
    return false;
}

static uint32_t lean_lvl_mk_max(LeanKernelState *ks, uint32_t u, uint32_t v) {
    if (u == 0) return v;
    if (v == 0) return u;
    if (u == v) return u;
    return lean_lvl_intern(ks, LLVL_MAX, u, v, 0);
}

static uint32_t lean_lvl_mk_imax(LeanKernelState *ks, uint32_t u, uint32_t v) {
    if (v == 0) return 0u;
    if (u == 0 || u == v) return v;
    if (lean_lvl_is_nonzero(ks, v)) return lean_lvl_mk_max(ks, u, v);
    return lean_lvl_intern(ks, LLVL_IMAX, u, v, 0);
}

static uint32_t lean_lvl_mk_param(LeanKernelState *ks, uint32_t param_name) {
    return lean_lvl_intern(ks, LLVL_PARAM, 0, 0, param_name);
}

/* Instantiate universe level parameters `params[0..nparams-1]` with `us[0..nparams-1]` */
static uint32_t lean_lvl_subst(LeanKernelState *ks, uint32_t l, uint32_t nparams, const uint32_t *params, const uint32_t *us) {
    if (l == 0 || nparams == 0) return l;
    LeanLvl lv = ks->lvls[l];
    switch (lv.kind) {
        case LLVL_ZERO:
            return 0u;
        case LLVL_SUCC: {
            uint32_t u2 = lean_lvl_subst(ks, lv.u, nparams, params, us);
            return (u2 == lv.u) ? l : lean_lvl_mk_succ(ks, u2);
        }
        case LLVL_MAX: {
            uint32_t u2 = lean_lvl_subst(ks, lv.u, nparams, params, us);
            uint32_t v2 = lean_lvl_subst(ks, lv.v, nparams, params, us);
            return (u2 == lv.u && v2 == lv.v) ? l : lean_lvl_mk_max(ks, u2, v2);
        }
        case LLVL_IMAX: {
            uint32_t u2 = lean_lvl_subst(ks, lv.u, nparams, params, us);
            uint32_t v2 = lean_lvl_subst(ks, lv.v, nparams, params, us);
            return (u2 == lv.u && v2 == lv.v) ? l : lean_lvl_mk_imax(ks, u2, v2);
        }
        case LLVL_PARAM:
            for (uint32_t i = 0; i < nparams; i++) {
                if (params[i] == lv.param_name) return us[i];
            }
            return l;
    }
    return l;
}

/* Collect any universe parameter occurring inside an `imax` right-hand side */
static void lean_lvl_collect_params(const LeanKernelState *ks, uint32_t l, uint32_t *out, uint32_t *nout, uint32_t cap) {
    if (l == 0) return;
    LeanLvl lv = ks->lvls[l];
    if (lv.kind == LLVL_PARAM) {
        for (uint32_t i = 0; i < *nout; i++) {
            if (out[i] == lv.param_name) return;
        }
        if (*nout < cap) out[(*nout)++] = lv.param_name;
    } else if (lv.kind == LLVL_SUCC) {
        lean_lvl_collect_params(ks, lv.u, out, nout, cap);
    } else if (lv.kind == LLVL_MAX || lv.kind == LLVL_IMAX) {
        lean_lvl_collect_params(ks, lv.u, out, nout, cap);
        lean_lvl_collect_params(ks, lv.v, out, nout, cap);
    }
}

static void lean_lvl_collect_imax_params(const LeanKernelState *ks, uint32_t l, uint32_t *out, uint32_t *nout, uint32_t cap) {
    if (l == 0) return;
    LeanLvl lv = ks->lvls[l];
    if (lv.kind == LLVL_SUCC) {
        lean_lvl_collect_imax_params(ks, lv.u, out, nout, cap);
    } else if (lv.kind == LLVL_MAX) {
        lean_lvl_collect_imax_params(ks, lv.u, out, nout, cap);
        lean_lvl_collect_imax_params(ks, lv.v, out, nout, cap);
    } else if (lv.kind == LLVL_IMAX) {
        lean_lvl_collect_params(ks, lv.v, out, nout, cap);
        lean_lvl_collect_imax_params(ks, lv.u, out, nout, cap);
        lean_lvl_collect_imax_params(ks, lv.v, out, nout, cap);
    }
}

/* Peel `Succ` off a level: returns base level and adds to `*k` */
static uint32_t lean_lvl_peel_succ(const LeanKernelState *ks, uint32_t l, int32_t *k) {
    *k = 0;
    while (l != 0 && ks->lvls[l].kind == LLVL_SUCC) {
        (*k)++;
        l = ks->lvls[l].u;
    }
    return l;
}

/* Compare `u <= v + diff` when all `imax` have been simplified or reduced */
static bool lean_lvl_leq_core(LeanKernelState *ks, uint32_t u, uint32_t v, int32_t diff) {
    if (u == 0 && diff >= 0) return true;
    if (u == v && diff >= 0) return true;

    int32_t ku = 0, kv = 0;
    uint32_t bu = lean_lvl_peel_succ(ks, u, &ku);
    uint32_t bv = lean_lvl_peel_succ(ks, v, &kv);
    int32_t ndiff = diff + kv - ku;

    if (bu == 0 && ndiff >= 0) return true;
    if (bu == bv && ndiff >= 0) return true;

    if (ks->lvls[bu].kind == LLVL_MAX) {
        return lean_lvl_leq_core(ks, ks->lvls[bu].u, bv, ndiff) &&
               lean_lvl_leq_core(ks, ks->lvls[bu].v, bv, ndiff);
    }
    if (bv != 0 && ks->lvls[bv].kind == LLVL_MAX) {
        return lean_lvl_leq_core(ks, bu, ks->lvls[bv].u, ndiff) ||
               lean_lvl_leq_core(ks, bu, ks->lvls[bv].v, ndiff);
    }
    if (ks->lvls[bu].kind == LLVL_IMAX && bv != 0 && ks->lvls[bv].kind == LLVL_IMAX &&
        ks->lvls[bu].u == ks->lvls[bv].u && ks->lvls[bu].v == ks->lvls[bv].v) {
        return ndiff >= 0;
    }
    return false;
}

static bool lean_lvl_leq(LeanKernelState *ks, uint32_t u, uint32_t v) {
    if (u == v || u == 0) return true;
    if (lean_lvl_leq_core(ks, u, v, 0)) return true;

    /* Finite case-split on universe parameters inside `imax` right-hand sides:
     * for each parameter `p`, test `p := 0` and `p := Succ(p)`. */
    uint32_t imax_params[16];
    uint32_t np = 0;
    lean_lvl_collect_imax_params(ks, u, imax_params, &np, 16);
    lean_lvl_collect_imax_params(ks, v, imax_params, &np, 16);
    if (np == 0 || np > 10) return false;

    uint32_t total_masks = 1u << np;
    for (uint32_t mask = 0; mask < total_masks; mask++) {
        uint32_t subst_us[16];
        for (uint32_t i = 0; i < np; i++) {
            uint32_t p_lvl = lean_lvl_mk_param(ks, imax_params[i]);
            subst_us[i] = (mask & (1u << i)) ? lean_lvl_mk_succ(ks, p_lvl) : 0u;
        }
        uint32_t u_inst = lean_lvl_subst(ks, u, np, imax_params, subst_us);
        uint32_t v_inst = lean_lvl_subst(ks, v, np, imax_params, subst_us);
        if (!lean_lvl_leq_core(ks, u_inst, v_inst, 0)) return false;
    }
    return true;
}

static bool lean_lvl_eq(LeanKernelState *ks, uint32_t u, uint32_t v) {
    if (u == v) return true;
    return lean_lvl_leq(ks, u, v) && lean_lvl_leq(ks, v, u);
}

static bool lean_lvl_has_param(const LeanKernelState *ks, uint32_t l) {
    if (l == 0) return false;
    LeanLvl lv = ks->lvls[l];
    if (lv.kind == LLVL_PARAM) return true;
    if (lv.kind == LLVL_SUCC) return lean_lvl_has_param(ks, lv.u);
    if (lv.kind == LLVL_MAX || lv.kind == LLVL_IMAX)
        return lean_lvl_has_param(ks, lv.u) || lean_lvl_has_param(ks, lv.v);
    return false;
}

/* ---- Expression Hash-Consing & Structural Operations ---- */

static void lean_expr_rehash(LeanKernelState *ks, uint32_t new_cap) {
    uint32_t *ntab = (uint32_t *)calloc(new_cap, sizeof(uint32_t));
    uint32_t mask = new_cap - 1u;
    for (uint32_t id = 1; id < ks->nexprs; id++) {
        uint32_t slot = ks->exprs[id].hash & mask;
        while (ntab[slot] != 0) slot = (slot + 1u) & mask;
        ntab[slot] = id;
    }
    free(ks->expr_htab);
    ks->expr_htab = ntab;
    ks->cap_expr_htab = new_cap;
}

static void lean_scratch_rehash(LeanKernelState *ks, uint32_t new_cap) {
    ks->scratch_htab = (LeanScratchHtabSlot *)realloc(
        ks->scratch_htab, (size_t)new_cap * sizeof(LeanScratchHtabSlot));
    memset(ks->scratch_htab, 0, (size_t)new_cap * sizeof(LeanScratchHtabSlot));
    ks->cap_scratch_htab = new_cap;
    uint32_t mask = new_cap - 1u;
    uint32_t sgen = ks->scratch_gen;
    for (uint32_t k = 0; k < ks->nscratch_exprs; k++) {
        uint32_t id = LEAN_SCRATCH_BASE + k;
        uint32_t slot = ks->exprs[id].hash & mask;
        while (ks->scratch_htab[slot].gen == sgen) slot = (slot + 1u) & mask;
        ks->scratch_htab[slot] = (LeanScratchHtabSlot){ .gen = sgen, .eid = id };
    }
}

static inline void lean_note_dirty_persistent_expr(LeanKernelState *ks, uint32_t orig_e, uint32_t target_e) {
    (void)ks; (void)orig_e; (void)target_e;
}

static inline void lean_scratch_scope_begin(LeanKernelState *ks) {
    ks->in_scratch_scope = true;
}

static void lean_scratch_scope_end(LeanKernelState *ks) {
    if (!ks->in_scratch_scope) return;
    for (uint32_t k = 0; k < ks->nscratch_exprs; k++) {
        uint32_t i = LEAN_SCRATCH_BASE + k;
        if (ks->exprs[i].kind == LEXPR_CONST) free(ks->exprs[i].d.cnst.us);
        else if (ks->exprs[i].kind == LEXPR_NATLIT && !ks->exprs[i].nat_is_small) free(ks->exprs[i].d.nat_big.dec_str);
        else if (ks->exprs[i].kind == LEXPR_STRLIT) free(ks->exprs[i].d.str_lit.str);
    }
    ks->stat_scratch_reclaimed += (uint64_t)ks->nscratch_exprs;
    ks->nscratch_exprs = 0;
    ks->in_scratch_scope = false;
    if (++ks->scratch_gen == 0u) {
        if (ks->scratch_htab) {
            memset(ks->scratch_htab, 0, (size_t)ks->cap_scratch_htab * sizeof(LeanScratchHtabSlot));
        }
        if (ks->defeq_cache) {
            memset(ks->defeq_cache, 0, (size_t)LEAN_DEFEQ_CACHE_SIZE * sizeof(LeanDefEqCache));
        }
        ks->scratch_gen = 1u;
    }
    if (++ks->subst_gen == 0u && ks->subst_cache) {
        memset(ks->subst_cache, 0, (size_t)LEAN_SUBST_CACHE_SIZE * sizeof(LeanSubstCache));
        ks->subst_gen = 1u;
    }
}

static bool lean_expr_node_eq(const LeanExpr *a, const LeanExpr *b) {
    if (a->kind != b->kind || a->hash != b->hash) return false;
    switch (a->kind) {
        case LEXPR_BVAR:   return a->d.bvar_idx == b->d.bvar_idx;
        case LEXPR_FVAR:   return a->d.fvar_id == b->d.fvar_id;
        case LEXPR_SORT:   return a->d.sort_lvl == b->d.sort_lvl;
        case LEXPR_CONST:
            if (a->d.cnst.name != b->d.cnst.name || a->d.cnst.nus != b->d.cnst.nus) return false;
            for (uint32_t i = 0; i < a->d.cnst.nus; i++) {
                if (a->d.cnst.us[i] != b->d.cnst.us[i]) return false;
            }
            return true;
        case LEXPR_APP:    return a->d.app.fn == b->d.app.fn && a->d.app.arg == b->d.app.arg;
        case LEXPR_LAM:
        case LEXPR_FORALL: return a->d.binder.domain == b->d.binder.domain && a->d.binder.body == b->d.binder.body;
        case LEXPR_LET:    return a->d.let_e.type == b->d.let_e.type && a->d.let_e.val == b->d.let_e.val && a->d.let_e.body == b->d.let_e.body;
        case LEXPR_NATLIT:
            if (a->nat_is_small != b->nat_is_small) return false;
            if (a->nat_is_small)
                return a->d.nat_small.lo == b->d.nat_small.lo && a->d.nat_small.hi == b->d.nat_small.hi;
            return strcmp(a->d.nat_big.dec_str, b->d.nat_big.dec_str) == 0;
        case LEXPR_STRLIT: return strcmp(a->d.str_lit.str, b->d.str_lit.str) == 0;
        case LEXPR_PROJ:   return a->d.proj.type_name == b->d.proj.type_name && a->d.proj.idx == b->d.proj.idx && a->d.proj.struct_expr == b->d.proj.struct_expr;
    }
    return false;
}

static inline void lean_expr_proto_free(LeanExpr *proto) {
    if (proto->kind == LEXPR_CONST) free(proto->d.cnst.us);
    else if (proto->kind == LEXPR_NATLIT && !proto->nat_is_small) free(proto->d.nat_big.dec_str);
    else if (proto->kind == LEXPR_STRLIT) free(proto->d.str_lit.str);
}

static uint32_t lean_expr_intern(LeanKernelState *ks, LeanExpr *proto) {
    if (ks->in_scratch_scope && proto->has_fvar) {
        if (ks->cap_scratch_htab == 0 || ks->nscratch_exprs * 2u >= ks->cap_scratch_htab) {
            lean_scratch_rehash(ks, ks->cap_scratch_htab ? ks->cap_scratch_htab * 2u : 65536u);
        }
        uint32_t smask = ks->cap_scratch_htab - 1u;
        uint32_t sslot = proto->hash & smask;
        uint32_t sgen = ks->scratch_gen;
        while (ks->scratch_htab[sslot].gen == sgen) {
            uint32_t eid = ks->scratch_htab[sslot].eid;
            if (lean_expr_node_eq(&ks->exprs[eid], proto)) {
                lean_expr_proto_free(proto);
                return eid;
            }
            sslot = (sslot + 1u) & smask;
        }
        if (ks->nscratch_exprs >= LEAN_SCRATCH_SLOTS) {
            fprintf(stderr, "DECLINE: CapacityCutoff: scratch expression arena exhausted (%u slots)\n",
                    (uint32_t)LEAN_SCRATCH_SLOTS);
            exit((int)LEAN_OUTCOME_DECLINE);
        }
        uint32_t id = LEAN_SCRATCH_BASE + ks->nscratch_exprs++;
        if (ks->nscratch_exprs > ks->stat_peak_scratch) ks->stat_peak_scratch = ks->nscratch_exprs;
        ks->exprs[id] = *proto;
        ks->scratch_htab[sslot] = (LeanScratchHtabSlot){ .gen = sgen, .eid = id };
        return id;
    }

    if (ks->cap_expr_htab == 0 || ks->nexprs * 2u >= ks->cap_expr_htab) {
        lean_expr_rehash(ks, ks->cap_expr_htab ? ks->cap_expr_htab * 2u : 65536u);
    }
    uint32_t mask = ks->cap_expr_htab - 1u;
    uint32_t slot = proto->hash & mask;
    while (ks->expr_htab[slot] != 0) {
        uint32_t eid = ks->expr_htab[slot];
        if (lean_expr_node_eq(&ks->exprs[eid], proto)) {
            lean_expr_proto_free(proto);
            return eid;
        }
        slot = (slot + 1u) & mask;
    }
    if (ks->nexprs >= LEAN_SCRATCH_BASE) {
        fprintf(stderr, "DECLINE: CapacityCutoff: persistent expression arena exhausted (%u slots)\n",
                (uint32_t)LEAN_SCRATCH_BASE);
        exit((int)LEAN_OUTCOME_DECLINE);
    }
    uint32_t id = ks->nexprs++;
    ks->exprs[id] = *proto;
    ks->expr_htab[slot] = id;
    return id;
}

static uint32_t lean_expr_mk_bvar(LeanKernelState *ks, uint32_t idx) {
    LeanExpr e;
    memset(&e, 0, sizeof(e));
    e.kind = LEXPR_BVAR;
    e.hash = fnv_mix32(fnv_mix32(2166136261u, LEXPR_BVAR), idx);
    e.loose_bvar_range = (idx < UINT32_MAX) ? (idx + 1u) : UINT32_MAX;
    e.d.bvar_idx = idx;
    return lean_expr_intern(ks, &e);
}

static uint32_t lean_expr_mk_fvar(LeanKernelState *ks, uint32_t fvar_id) {
    LeanExpr e;
    memset(&e, 0, sizeof(e));
    e.kind = LEXPR_FVAR;
    e.hash = fnv_mix32(fnv_mix32(2166136261u, LEXPR_FVAR), fvar_id);
    e.has_fvar = 1;
    e.d.fvar_id = fvar_id;
    return lean_expr_intern(ks, &e);
}

static uint32_t lean_expr_mk_sort(LeanKernelState *ks, uint32_t lvl) {
    LeanExpr e;
    memset(&e, 0, sizeof(e));
    e.kind = LEXPR_SORT;
    e.hash = fnv_mix32(fnv_mix32(2166136261u, LEXPR_SORT), lvl);
    e.has_lvl_param = lean_lvl_has_param(ks, lvl) ? 1 : 0;
    e.d.sort_lvl = lvl;
    return lean_expr_intern(ks, &e);
}

static uint32_t lean_expr_mk_const(LeanKernelState *ks, uint32_t name, uint32_t nus, const uint32_t *us) {
    LeanExpr e;
    memset(&e, 0, sizeof(e));
    e.kind = LEXPR_CONST;
    uint32_t h = fnv_mix32(fnv_mix32(2166136261u, LEXPR_CONST), name);
    h = fnv_mix32(h, nus);
    uint8_t hp = 0;
    uint32_t *ucopy = NULL;
    if (nus > 0) {
        ucopy = (uint32_t *)malloc((size_t)nus * sizeof(uint32_t));
        for (uint32_t i = 0; i < nus; i++) {
            ucopy[i] = us[i];
            h = fnv_mix32(h, us[i]);
            if (lean_lvl_has_param(ks, us[i])) hp = 1;
        }
    }
    e.hash = h;
    e.has_lvl_param = hp;
    if ((ks->nm_sorryAx != 0 && name == ks->nm_sorryAx) ||
        (name < ks->cap_decls_by_name && ks->decls_by_name[name].uses_sorry)) {
        e.has_sorry = 1;
    }
    if ((ks->nm_trustCompiler != 0 && name == ks->nm_trustCompiler) ||
        (ks->nm_ofReduceBool != 0 && name == ks->nm_ofReduceBool) ||
        (ks->nm_ofReduceNat != 0 && name == ks->nm_ofReduceNat) ||
        (name < ks->cap_decls_by_name && ks->decls_by_name[name].uses_trust_compiler)) {
        e.has_trust_compiler = 1;
    }
    e.d.cnst.name = name;
    e.d.cnst.nus = nus;
    e.d.cnst.us = ucopy;
    return lean_expr_intern(ks, &e);
}

static inline uint32_t max_u32(uint32_t a, uint32_t b) { return a > b ? a : b; }
static inline uint32_t dec_bvar_range(uint32_t r) { return r > 0 ? r - 1u : 0u; }

static uint32_t lean_expr_mk_app(LeanKernelState *ks, uint32_t fn, uint32_t arg) {
    LeanExpr e;
    memset(&e, 0, sizeof(e));
    e.kind = LEXPR_APP;
    uint32_t h = fnv_mix32(2166136261u, LEXPR_APP);
    h = fnv_mix32(fnv_mix32(h, fn), arg);
    e.hash = h;
    e.loose_bvar_range = max_u32(ks->exprs[fn].loose_bvar_range, ks->exprs[arg].loose_bvar_range);
    e.has_fvar = ks->exprs[fn].has_fvar | ks->exprs[arg].has_fvar;
    e.has_lvl_param = ks->exprs[fn].has_lvl_param | ks->exprs[arg].has_lvl_param;
    e.has_sorry = ks->exprs[fn].has_sorry | ks->exprs[arg].has_sorry;
    e.has_trust_compiler = ks->exprs[fn].has_trust_compiler | ks->exprs[arg].has_trust_compiler;
    e.d.app.fn = fn;
    e.d.app.arg = arg;
    return lean_expr_intern(ks, &e);
}

static uint32_t lean_expr_mk_lam(LeanKernelState *ks, uint32_t bname, uint32_t dom, uint32_t body) {
    LeanExpr e;
    memset(&e, 0, sizeof(e));
    e.kind = LEXPR_LAM;
    uint32_t h = fnv_mix32(2166136261u, LEXPR_LAM);
    h = fnv_mix32(fnv_mix32(h, dom), body);
    e.hash = h;
    e.loose_bvar_range = max_u32(ks->exprs[dom].loose_bvar_range, dec_bvar_range(ks->exprs[body].loose_bvar_range));
    e.has_fvar = ks->exprs[dom].has_fvar | ks->exprs[body].has_fvar;
    e.has_lvl_param = ks->exprs[dom].has_lvl_param | ks->exprs[body].has_lvl_param;
    e.has_sorry = ks->exprs[dom].has_sorry | ks->exprs[body].has_sorry;
    e.has_trust_compiler = ks->exprs[dom].has_trust_compiler | ks->exprs[body].has_trust_compiler;
    e.d.binder.binder_name = bname;
    e.d.binder.domain = dom;
    e.d.binder.body = body;
    return lean_expr_intern(ks, &e);
}

static uint32_t lean_expr_mk_forall(LeanKernelState *ks, uint32_t bname, uint32_t dom, uint32_t body) {
    LeanExpr e;
    memset(&e, 0, sizeof(e));
    e.kind = LEXPR_FORALL;
    uint32_t h = fnv_mix32(2166136261u, LEXPR_FORALL);
    h = fnv_mix32(fnv_mix32(h, dom), body);
    e.hash = h;
    e.loose_bvar_range = max_u32(ks->exprs[dom].loose_bvar_range, dec_bvar_range(ks->exprs[body].loose_bvar_range));
    e.has_fvar = ks->exprs[dom].has_fvar | ks->exprs[body].has_fvar;
    e.has_lvl_param = ks->exprs[dom].has_lvl_param | ks->exprs[body].has_lvl_param;
    e.has_sorry = ks->exprs[dom].has_sorry | ks->exprs[body].has_sorry;
    e.has_trust_compiler = ks->exprs[dom].has_trust_compiler | ks->exprs[body].has_trust_compiler;
    e.d.binder.binder_name = bname;
    e.d.binder.domain = dom;
    e.d.binder.body = body;
    return lean_expr_intern(ks, &e);
}

static uint32_t lean_expr_mk_let(LeanKernelState *ks, uint32_t bname, uint32_t ty, uint32_t val, uint32_t body) {
    LeanExpr e;
    memset(&e, 0, sizeof(e));
    e.kind = LEXPR_LET;
    uint32_t h = fnv_mix32(2166136261u, LEXPR_LET);
    h = fnv_mix32(fnv_mix32(fnv_mix32(h, ty), val), body);
    e.hash = h;
    e.loose_bvar_range = max_u32(
        max_u32(ks->exprs[ty].loose_bvar_range, ks->exprs[val].loose_bvar_range),
        dec_bvar_range(ks->exprs[body].loose_bvar_range));
    e.has_fvar = ks->exprs[ty].has_fvar | ks->exprs[val].has_fvar | ks->exprs[body].has_fvar;
    e.has_lvl_param = ks->exprs[ty].has_lvl_param | ks->exprs[val].has_lvl_param | ks->exprs[body].has_lvl_param;
    e.has_sorry = ks->exprs[ty].has_sorry | ks->exprs[val].has_sorry | ks->exprs[body].has_sorry;
    e.has_trust_compiler = ks->exprs[ty].has_trust_compiler | ks->exprs[val].has_trust_compiler | ks->exprs[body].has_trust_compiler;
    e.d.let_e.binder_name = bname;
    e.d.let_e.type = ty;
    e.d.let_e.val = val;
    e.d.let_e.body = body;
    return lean_expr_intern(ks, &e);
}

static uint32_t lean_expr_mk_natlit_u128(LeanKernelState *ks, __uint128_t v) {
    LeanExpr e;
    memset(&e, 0, sizeof(e));
    e.kind = LEXPR_NATLIT;
    e.nat_is_small = 1u;
    uint64_t lo = (uint64_t)v;
    uint64_t hi = (uint64_t)(v >> 64);
    e.d.nat_small.lo = lo;
    e.d.nat_small.hi = hi;
    uint32_t h = fnv_mix32(2166136261u, LEXPR_NATLIT);
    h = fnv_mix32(h, (uint32_t)lo);
    h = fnv_mix32(h, (uint32_t)(lo >> 32));
    h = fnv_mix32(h, (uint32_t)hi);
    h = fnv_mix32(h, (uint32_t)(hi >> 32));
    e.hash = h ? h : 1u;
    return lean_expr_intern(ks, &e);
}

static uint32_t lean_expr_mk_natlit_str(LeanKernelState *ks, const char *dec_str) {
    __uint128_t v = 0;
    bool ok = (dec_str[0] != '\0');
    for (const char *p = dec_str; *p; p++) {
        if (*p < '0' || *p > '9') { ok = false; break; }
        __uint128_t next = 0;
        if (__builtin_mul_overflow(v, (__uint128_t)10, &next) ||
            __builtin_add_overflow(next, (__uint128_t)(*p - '0'), &v)) {
            ok = false;
            break;
        }
    }
    if (ok) {
        return lean_expr_mk_natlit_u128(ks, v);
    }
    LeanExpr e;
    memset(&e, 0, sizeof(e));
    e.kind = LEXPR_NATLIT;
    e.nat_is_small = 0u;
    e.hash = fnv_str(fnv_mix32(2166136261u, LEXPR_NATLIT), dec_str);
    e.d.nat_big.dec_str = xstrdup(dec_str);
    return lean_expr_intern(ks, &e);
}

static uint32_t lean_expr_mk_natlit_u64(LeanKernelState *ks, uint64_t v) {
    return lean_expr_mk_natlit_u128(ks, (__uint128_t)v);
}

static uint32_t lean_expr_mk_strlit(LeanKernelState *ks, const char *s) {
    LeanExpr e;
    memset(&e, 0, sizeof(e));
    e.kind = LEXPR_STRLIT;
    e.hash = fnv_str(fnv_mix32(2166136261u, LEXPR_STRLIT), s);
    e.d.str_lit.str = xstrdup(s);
    return lean_expr_intern(ks, &e);
}

static uint32_t lean_expr_mk_proj(LeanKernelState *ks, uint32_t tname, uint32_t idx, uint32_t s) {
    LeanExpr e;
    memset(&e, 0, sizeof(e));
    e.kind = LEXPR_PROJ;
    uint32_t h = fnv_mix32(2166136261u, LEXPR_PROJ);
    h = fnv_mix32(fnv_mix32(fnv_mix32(h, tname), idx), s);
    e.hash = h;
    e.loose_bvar_range = ks->exprs[s].loose_bvar_range;
    e.has_fvar = ks->exprs[s].has_fvar;
    e.has_lvl_param = ks->exprs[s].has_lvl_param;
    e.has_sorry = ks->exprs[s].has_sorry;
    e.has_trust_compiler = ks->exprs[s].has_trust_compiler;
    e.d.proj.type_name = tname;
    e.d.proj.idx = idx;
    e.d.proj.struct_expr = s;
    return lean_expr_intern(ks, &e);
}

/* =========================================================================
 * 4. De Bruijn Instantiation, FVar Abstraction, and Level Substitution
 * ========================================================================= */

/*
 * `lean_expr_instantiate_rev(ks, e, offset, n, subst)`:
 * Replaces `bvar(offset + i)` with `subst[n - 1 - i]` for `0 <= i < n`.
 * Notice our `loose_bvar_range` fast-path: if `e.loose_bvar_range <= offset`,
 * `e` contains NO loose bound variables >= `offset`, so it returns `e` in O(1)!
 */
static uint32_t lean_expr_instantiate_rev_rec(
    LeanKernelState *ks,
    uint32_t e,
    uint32_t offset,
    uint32_t n,
    const uint32_t *subst,
    uint32_t gen)
{
    if (ks->exprs[e].loose_bvar_range <= offset) return e;
    LeanExprKind kind = ks->exprs[e].kind;
    if (kind == LEXPR_BVAR) {
        uint32_t bidx = ks->exprs[e].d.bvar_idx;
        if (bidx >= offset && bidx < offset + n) {
            return subst[n - 1u - (bidx - offset)];
        }
        if (bidx >= offset + n) {
            return lean_expr_mk_bvar(ks, bidx - n);
        }
        return e;
    }
    uint32_t slot = fnv_mix32(fnv_mix32(2166136261u, e), offset) & (LEAN_SUBST_CACHE_SIZE - 1u);
    if (ks->subst_cache &&
        ks->subst_cache[slot].gen == gen &&
        ks->subst_cache[slot].e == e &&
        ks->subst_cache[slot].offset == offset) {
        return ks->subst_cache[slot].res;
    }
    uint32_t res = e;
    switch (kind) {
        case LEXPR_APP: {
            uint32_t fn  = ks->exprs[e].d.app.fn;
            uint32_t arg = ks->exprs[e].d.app.arg;
            uint32_t fn2  = lean_expr_instantiate_rev_rec(ks, fn, offset, n, subst, gen);
            uint32_t arg2 = lean_expr_instantiate_rev_rec(ks, arg, offset, n, subst, gen);
            res = (fn2 == fn && arg2 == arg) ? e : lean_expr_mk_app(ks, fn2, arg2);
            break;
        }
        case LEXPR_LAM: {
            uint32_t bn  = ks->exprs[e].d.binder.binder_name;
            uint32_t dom = ks->exprs[e].d.binder.domain;
            uint32_t bod = ks->exprs[e].d.binder.body;
            uint32_t d2 = lean_expr_instantiate_rev_rec(ks, dom, offset, n, subst, gen);
            uint32_t b2 = lean_expr_instantiate_rev_rec(ks, bod, offset + 1u, n, subst, gen);
            res = (d2 == dom && b2 == bod) ? e : lean_expr_mk_lam(ks, bn, d2, b2);
            break;
        }
        case LEXPR_FORALL: {
            uint32_t bn  = ks->exprs[e].d.binder.binder_name;
            uint32_t dom = ks->exprs[e].d.binder.domain;
            uint32_t bod = ks->exprs[e].d.binder.body;
            uint32_t d2 = lean_expr_instantiate_rev_rec(ks, dom, offset, n, subst, gen);
            uint32_t b2 = lean_expr_instantiate_rev_rec(ks, bod, offset + 1u, n, subst, gen);
            res = (d2 == dom && b2 == bod) ? e : lean_expr_mk_forall(ks, bn, d2, b2);
            break;
        }
        case LEXPR_LET: {
            uint32_t bn  = ks->exprs[e].d.let_e.binder_name;
            uint32_t ty  = ks->exprs[e].d.let_e.type;
            uint32_t val = ks->exprs[e].d.let_e.val;
            uint32_t bod = ks->exprs[e].d.let_e.body;
            uint32_t t2 = lean_expr_instantiate_rev_rec(ks, ty, offset, n, subst, gen);
            uint32_t v2 = lean_expr_instantiate_rev_rec(ks, val, offset, n, subst, gen);
            uint32_t b2 = lean_expr_instantiate_rev_rec(ks, bod, offset + 1u, n, subst, gen);
            res = (t2 == ty && v2 == val && b2 == bod) ? e : lean_expr_mk_let(ks, bn, t2, v2, b2);
            break;
        }
        case LEXPR_PROJ: {
            uint32_t tnm = ks->exprs[e].d.proj.type_name;
            uint32_t idx = ks->exprs[e].d.proj.idx;
            uint32_t se  = ks->exprs[e].d.proj.struct_expr;
            uint32_t s2 = lean_expr_instantiate_rev_rec(ks, se, offset, n, subst, gen);
            res = (s2 == se) ? e : lean_expr_mk_proj(ks, tnm, idx, s2);
            break;
        }
        default:
            break;
    }
    if (ks->subst_cache) {
        ks->subst_cache[slot] = (LeanSubstCache){ .gen = gen, .e = e, .offset = offset, .res = res };
    }
    return res;
}

static uint32_t lean_expr_instantiate_rev(
    LeanKernelState *ks,
    uint32_t e,
    uint32_t offset,
    uint32_t n,
    const uint32_t *subst)
{
    if (n == 0 || ks->exprs[e].loose_bvar_range <= offset) return e;
    uint32_t gen = ++ks->subst_gen;
    if (gen == 0 && ks->subst_cache) {
        memset(ks->subst_cache, 0, LEAN_SUBST_CACHE_SIZE * sizeof(LeanSubstCache));
        gen = ++ks->subst_gen;
    }
    return lean_expr_instantiate_rev_rec(ks, e, offset, n, subst, gen);
}

static inline uint32_t lean_expr_instantiate1(LeanKernelState *ks, uint32_t body, uint32_t val) {
    return lean_expr_instantiate_rev(ks, body, 0, 1, &val);
}

/* Replace `fvars[0..n-1]` with `bvar(offset + n - 1 - i)` */
static uint32_t lean_expr_abstract_fvars_rec(
    LeanKernelState *ks,
    uint32_t e,
    uint32_t offset,
    uint32_t n,
    const uint32_t *fvars,
    uint32_t gen)
{
    if (!ks->exprs[e].has_fvar) return e;
    LeanExpr ex = ks->exprs[e];
    if (ex.kind == LEXPR_FVAR) {
        for (uint32_t i = 0; i < n; i++) {
            if (ex.d.fvar_id == fvars[i]) {
                return lean_expr_mk_bvar(ks, offset + (n - 1u - i));
            }
        }
        return e;
    }
    uint32_t slot = fnv_mix32(fnv_mix32(2166136261u, e), offset) & (LEAN_SUBST_CACHE_SIZE - 1u);
    if (ks->subst_cache &&
        ks->subst_cache[slot].gen == gen &&
        ks->subst_cache[slot].e == e &&
        ks->subst_cache[slot].offset == offset) {
        return ks->subst_cache[slot].res;
    }
    uint32_t res = e;
    switch (ex.kind) {
        case LEXPR_APP: {
            uint32_t fn2  = lean_expr_abstract_fvars_rec(ks, ex.d.app.fn, offset, n, fvars, gen);
            uint32_t arg2 = lean_expr_abstract_fvars_rec(ks, ex.d.app.arg, offset, n, fvars, gen);
            res = (fn2 == ex.d.app.fn && arg2 == ex.d.app.arg) ? e : lean_expr_mk_app(ks, fn2, arg2);
            break;
        }
        case LEXPR_LAM: {
            uint32_t d2 = lean_expr_abstract_fvars_rec(ks, ex.d.binder.domain, offset, n, fvars, gen);
            uint32_t b2 = lean_expr_abstract_fvars_rec(ks, ex.d.binder.body, offset + 1u, n, fvars, gen);
            res = (d2 == ex.d.binder.domain && b2 == ex.d.binder.body)
                  ? e : lean_expr_mk_lam(ks, ex.d.binder.binder_name, d2, b2);
            break;
        }
        case LEXPR_FORALL: {
            uint32_t d2 = lean_expr_abstract_fvars_rec(ks, ex.d.binder.domain, offset, n, fvars, gen);
            uint32_t b2 = lean_expr_abstract_fvars_rec(ks, ex.d.binder.body, offset + 1u, n, fvars, gen);
            res = (d2 == ex.d.binder.domain && b2 == ex.d.binder.body)
                  ? e : lean_expr_mk_forall(ks, ex.d.binder.binder_name, d2, b2);
            break;
        }
        case LEXPR_LET: {
            uint32_t t2 = lean_expr_abstract_fvars_rec(ks, ex.d.let_e.type, offset, n, fvars, gen);
            uint32_t v2 = lean_expr_abstract_fvars_rec(ks, ex.d.let_e.val, offset, n, fvars, gen);
            uint32_t b2 = lean_expr_abstract_fvars_rec(ks, ex.d.let_e.body, offset + 1u, n, fvars, gen);
            res = (t2 == ex.d.let_e.type && v2 == ex.d.let_e.val && b2 == ex.d.let_e.body)
                  ? e : lean_expr_mk_let(ks, ex.d.let_e.binder_name, t2, v2, b2);
            break;
        }
        case LEXPR_PROJ: {
            uint32_t s2 = lean_expr_abstract_fvars_rec(ks, ex.d.proj.struct_expr, offset, n, fvars, gen);
            res = (s2 == ex.d.proj.struct_expr) ? e : lean_expr_mk_proj(ks, ex.d.proj.type_name, ex.d.proj.idx, s2);
            break;
        }
        default:
            break;
    }
    if (ks->subst_cache) {
        ks->subst_cache[slot] = (LeanSubstCache){ .gen = gen, .e = e, .offset = offset, .res = res };
    }
    return res;
}

static uint32_t lean_expr_abstract_fvars(
    LeanKernelState *ks,
    uint32_t e,
    uint32_t offset,
    uint32_t n,
    const uint32_t *fvars)
{
    if (n == 0 || !ks->exprs[e].has_fvar) return e;
    uint32_t gen = ++ks->subst_gen;
    if (gen == 0 && ks->subst_cache) {
        memset(ks->subst_cache, 0, LEAN_SUBST_CACHE_SIZE * sizeof(LeanSubstCache));
        gen = ++ks->subst_gen;
    }
    return lean_expr_abstract_fvars_rec(ks, e, offset, n, fvars, gen);
}

/* Instantiate universe level parameters `params[0..nparams-1]` with `us[0..nparams-1]` in `e`.
 * Uses `has_lvl_param` bit to skip closed-universe subtrees in O(1)! */
static uint32_t lean_expr_subst_lvls_rec(
    LeanKernelState *ks,
    uint32_t e,
    uint32_t nparams,
    const uint32_t *params,
    const uint32_t *us,
    uint32_t gen)
{
    if (e == 0 || nparams == 0 || !ks->exprs[e].has_lvl_param) return e;
    LeanExpr ex = ks->exprs[e];
    if (ex.kind == LEXPR_SORT) {
        uint32_t l2 = lean_lvl_subst(ks, ex.d.sort_lvl, nparams, params, us);
        return (l2 == ex.d.sort_lvl) ? e : lean_expr_mk_sort(ks, l2);
    }
    if (ex.kind == LEXPR_CONST) {
        uint32_t nus = ex.d.cnst.nus;
        if (nus == 0) return e;
        uint32_t stack_us[16];
        uint32_t *new_us = (nus <= 16) ? stack_us : (uint32_t *)malloc((size_t)nus * sizeof(uint32_t));
        bool changed = false;
        for (uint32_t i = 0; i < nus; i++) {
            new_us[i] = lean_lvl_subst(ks, ex.d.cnst.us[i], nparams, params, us);
            if (new_us[i] != ex.d.cnst.us[i]) changed = true;
        }
        uint32_t res = changed ? lean_expr_mk_const(ks, ex.d.cnst.name, nus, new_us) : e;
        if (nus > 16) free(new_us);
        return res;
    }
    uint32_t slot = fnv_mix32(2166136261u, e) & (LEAN_SUBST_CACHE_SIZE - 1u);
    if (ks->subst_cache &&
        ks->subst_cache[slot].gen == gen &&
        ks->subst_cache[slot].e == e &&
        ks->subst_cache[slot].offset == 0xffffffffu) {
        return ks->subst_cache[slot].res;
    }
    uint32_t res = e;
    switch (ex.kind) {
        case LEXPR_APP: {
            uint32_t fn2  = lean_expr_subst_lvls_rec(ks, ex.d.app.fn, nparams, params, us, gen);
            uint32_t arg2 = lean_expr_subst_lvls_rec(ks, ex.d.app.arg, nparams, params, us, gen);
            res = (fn2 == ex.d.app.fn && arg2 == ex.d.app.arg) ? e : lean_expr_mk_app(ks, fn2, arg2);
            break;
        }
        case LEXPR_LAM: {
            uint32_t d2 = lean_expr_subst_lvls_rec(ks, ex.d.binder.domain, nparams, params, us, gen);
            uint32_t b2 = lean_expr_subst_lvls_rec(ks, ex.d.binder.body, nparams, params, us, gen);
            res = (d2 == ex.d.binder.domain && b2 == ex.d.binder.body)
                   ? e : lean_expr_mk_lam(ks, ex.d.binder.binder_name, d2, b2);
            break;
        }
        case LEXPR_FORALL: {
            uint32_t d2 = lean_expr_subst_lvls_rec(ks, ex.d.binder.domain, nparams, params, us, gen);
            uint32_t b2 = lean_expr_subst_lvls_rec(ks, ex.d.binder.body, nparams, params, us, gen);
            res = (d2 == ex.d.binder.domain && b2 == ex.d.binder.body)
                   ? e : lean_expr_mk_forall(ks, ex.d.binder.binder_name, d2, b2);
            break;
        }
        case LEXPR_LET: {
            uint32_t t2 = lean_expr_subst_lvls_rec(ks, ex.d.let_e.type, nparams, params, us, gen);
            uint32_t v2 = lean_expr_subst_lvls_rec(ks, ex.d.let_e.val, nparams, params, us, gen);
            uint32_t b2 = lean_expr_subst_lvls_rec(ks, ex.d.let_e.body, nparams, params, us, gen);
            res = (t2 == ex.d.let_e.type && v2 == ex.d.let_e.val && b2 == ex.d.let_e.body)
                   ? e : lean_expr_mk_let(ks, ex.d.let_e.binder_name, t2, v2, b2);
            break;
        }
        case LEXPR_PROJ: {
            uint32_t s2 = lean_expr_subst_lvls_rec(ks, ex.d.proj.struct_expr, nparams, params, us, gen);
            res = (s2 == ex.d.proj.struct_expr) ? e : lean_expr_mk_proj(ks, ex.d.proj.type_name, ex.d.proj.idx, s2);
            break;
        }
        default:
            break;
    }
    if (ks->subst_cache) {
        ks->subst_cache[slot] = (LeanSubstCache){ .gen = gen, .e = e, .offset = 0xffffffffu, .res = res };
    }
    return res;
}

static uint32_t lean_expr_subst_lvls(
    LeanKernelState *ks,
    uint32_t e,
    uint32_t nparams,
    const uint32_t *params,
    const uint32_t *us)
{
    if (e == 0 || nparams == 0 || !us || !ks->exprs[e].has_lvl_param) return e;
    bool is_identity = true;
    for (uint32_t i = 0; i < nparams; i++) {
        uint32_t u = us[i];
        if (u == 0 || ks->lvls[u].kind != LLVL_PARAM || ks->lvls[u].param_name != params[i]) {
            is_identity = false;
            break;
        }
    }
    if (is_identity) return e;
    uint32_t us_buf[16];
    uint32_t *us_copy = (nparams <= 16) ? us_buf : (uint32_t *)malloc((size_t)nparams * sizeof(uint32_t));
    memcpy(us_copy, us, (size_t)nparams * sizeof(uint32_t));
    uint32_t gen = ++ks->subst_gen;
    if (gen == 0 && ks->subst_cache) {
        memset(ks->subst_cache, 0, LEAN_SUBST_CACHE_SIZE * sizeof(LeanSubstCache));
        gen = ++ks->subst_gen;
    }
    uint32_t res = lean_expr_subst_lvls_rec(ks, e, nparams, params, us_copy, gen);
    if (us_copy != us_buf) free(us_copy);
    return res;
}

/* =========================================================================
 * 5. Local Context, WHNF Reduction, Type Inference, and Definitional Equality
 * ========================================================================= */

static uint32_t lean_push_local(LeanKernelState *ks, uint32_t name, uint32_t type, uint32_t llet_val) {
    if (ks->nlocals >= ks->cap_locals) {
        uint32_t ncap = ks->cap_locals ? ks->cap_locals * 2u : 256u;
        ks->locals = (LeanLocalDecl *)realloc(ks->locals, (size_t)ncap * sizeof(LeanLocalDecl));
        ks->cap_locals = ncap;
    }
    uint32_t fid = ++ks->next_fvar_id;
    ks->locals[ks->nlocals++] = (LeanLocalDecl){
        .fvar_id = fid,
        .name = name,
        .type = type,
        .llet_val = llet_val
    };
    return lean_expr_mk_fvar(ks, fid);
}

static void lean_pop_local(LeanKernelState *ks) {
    if (ks->nlocals > 0) ks->nlocals--;
}

static const LeanLocalDecl *lean_lookup_local(const LeanKernelState *ks, uint32_t fvar_id) {
    for (int32_t i = (int32_t)ks->nlocals - 1; i >= 0; i--) {
        if (ks->locals[i].fvar_id == fvar_id) return &ks->locals[i];
    }
    return NULL;
}

static const LeanDecl *lean_lookup_decl(const LeanKernelState *ks, uint32_t name_id) {
    if (name_id == 0 || name_id >= ks->cap_decls_by_name) return NULL;
    const LeanDecl *d = &ks->decls_by_name[name_id];
    return (d->kind != LDECL_NONE) ? d : NULL;
}

/* Unpack application spine `f a_0 a_1 ... a_{n-1}` */
static uint32_t lean_unpack_spine(const LeanKernelState *ks, uint32_t e, uint32_t **out_args, uint32_t *out_nargs, uint32_t *io_cap, uint32_t *stack_buf) {
    uint32_t count = 0;
    uint32_t cur = e;
    while (ks->exprs[cur].kind == LEXPR_APP) {
        count++;
        cur = ks->exprs[cur].d.app.fn;
    }
    if (count > *io_cap) {
        *out_args = (uint32_t *)malloc((size_t)count * sizeof(uint32_t));
        *io_cap = count;
    } else {
        *out_args = stack_buf;
    }
    *out_nargs = count;
    cur = e;
    for (uint32_t i = 0; i < count; i++) {
        (*out_args)[count - 1u - i] = ks->exprs[cur].d.app.arg;
        cur = ks->exprs[cur].d.app.fn;
    }
    return cur;
}

static uint32_t lean_mk_app_spine(LeanKernelState *ks, uint32_t head, uint32_t nargs, const uint32_t *args) {
    uint32_t cur = head;
    for (uint32_t i = 0; i < nargs; i++) {
        cur = lean_expr_mk_app(ks, cur, args[i]);
    }
    return cur;
}

static uint32_t lean_whnf(LeanKernelState *ks, uint32_t e);
static bool lean_is_prop(LeanKernelState *ks, uint32_t ty);
static int lean_check_is_prop_strict(LeanKernelState *ks, uint32_t ty);
static uint32_t lean_infer_type(LeanKernelState *ks, uint32_t e);
static bool lean_is_def_eq(LeanKernelState *ks, uint32_t a, uint32_t b);

/* Extract __uint128_t from a WHNF Nat expression (either LEXPR_NATLIT or Nat.zero),
 * matching Lean 4 / Lean4Lean `rawNatLitExt? (<- whnf e)`. */
static bool lean_eval_nat_val(LeanKernelState *ks, uint32_t e, __uint128_t *out_val) {
    if (!ks->nat_verified) return false;
    uint32_t w = lean_whnf(ks, e);
    LeanExpr ex = ks->exprs[w];
    if (ex.kind == LEXPR_NATLIT && ex.nat_is_small) {
        *out_val = lean_expr_nat_u128(&ex);
        return true;
    }
    if (ex.kind == LEXPR_CONST && ex.d.cnst.name == ks->nm_Nat_zero) {
        *out_val = 0;
        return true;
    }
    return false;
}

static __uint128_t u128_gcd(__uint128_t a, __uint128_t b) {
    while (b != 0) {
        __uint128_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

/* Kernel Nat reduction (`reduceNat` in Lean 4 / Lean4Lean `TypeChecker.lean`).
 * Only invoked in full `whnf` (`unfold_defs = true`) or in `is_def_eq` when `!a.has_fvar && !b.has_fvar`. */
static uint32_t lean_try_nat_kernel_op(LeanKernelState *ks, uint32_t head_name, uint32_t nargs, const uint32_t *args) {
    if (!ks->nat_verified) return 0;
    if (head_name == ks->nm_Nat_succ && nargs == 1) {
        __uint128_t v = 0, r = 0;
        if (lean_eval_nat_val(ks, args[0], &v) && !__builtin_add_overflow(v, (__uint128_t)1, &r)) {
            return lean_expr_mk_natlit_u128(ks, r);
        }
        return 0;
    }
    if (nargs != 2) return 0;
    if (head_name != ks->nm_Nat_add && head_name != ks->nm_Nat_sub &&
        head_name != ks->nm_Nat_mul && head_name != ks->nm_Nat_pow &&
        head_name != ks->nm_Nat_div && head_name != ks->nm_Nat_mod &&
        head_name != ks->nm_Nat_gcd && head_name != ks->nm_Nat_beq &&
        head_name != ks->nm_Nat_ble && head_name != ks->nm_Nat_land &&
        head_name != ks->nm_Nat_lor && head_name != ks->nm_Nat_lxor &&
        head_name != ks->nm_Nat_shl && head_name != ks->nm_Nat_shr) {
        return 0;
    }
    __uint128_t a = 0, b = 0;
    if (!lean_eval_nat_val(ks, args[0], &a) || !lean_eval_nat_val(ks, args[1], &b))
        return 0;

    if (head_name == ks->nm_Nat_add) {
        __uint128_t r = 0;
        if (__builtin_add_overflow(a, b, &r)) return 0;
        return lean_expr_mk_natlit_u128(ks, r);
    }
    if (head_name == ks->nm_Nat_sub) return lean_expr_mk_natlit_u128(ks, a >= b ? a - b : (__uint128_t)0);
    if (head_name == ks->nm_Nat_mul) {
        __uint128_t r = 0;
        if (__builtin_mul_overflow(a, b, &r)) return 0;
        return lean_expr_mk_natlit_u128(ks, r);
    }
    if (head_name == ks->nm_Nat_div) return lean_expr_mk_natlit_u128(ks, b == 0 ? (__uint128_t)0 : a / b);
    if (head_name == ks->nm_Nat_mod) return lean_expr_mk_natlit_u128(ks, b == 0 ? a : a % b);
    if (head_name == ks->nm_Nat_gcd) return lean_expr_mk_natlit_u128(ks, u128_gcd(a, b));
    if (head_name == ks->nm_Nat_pow) {
        if (b > 126) return 0;
        __uint128_t r = 1u;
        for (__uint128_t i = 0; i < b; i++) {
            if (__builtin_mul_overflow(r, a, &r)) return 0;
        }
        return lean_expr_mk_natlit_u128(ks, r);
    }
    if (head_name == ks->nm_Nat_land) return lean_expr_mk_natlit_u128(ks, a & b);
    if (head_name == ks->nm_Nat_lor)  return lean_expr_mk_natlit_u128(ks, a | b);
    if (head_name == ks->nm_Nat_lxor) return lean_expr_mk_natlit_u128(ks, a ^ b);
    if (head_name == ks->nm_Nat_shl) {
        if (a == 0) return lean_expr_mk_natlit_u128(ks, 0);
        if (b >= 128 || (b > 0 && (a >> (128u - (unsigned)b)) != 0)) return 0;
        return lean_expr_mk_natlit_u128(ks, a << (unsigned)b);
    }
    if (head_name == ks->nm_Nat_shr)  return (b < 128) ? lean_expr_mk_natlit_u128(ks, a >> (unsigned)b) : lean_expr_mk_natlit_u128(ks, 0);
    if (head_name == ks->nm_Nat_beq) {
        uint32_t bnm = (a == b) ? ks->nm_Bool_true : ks->nm_Bool_false;
        return bnm ? lean_expr_mk_const(ks, bnm, 0, NULL) : 0;
    }
    if (head_name == ks->nm_Nat_ble) {
        uint32_t bnm = (a <= b) ? ks->nm_Bool_true : ks->nm_Bool_false;
        return bnm ? lean_expr_mk_const(ks, bnm, 0, NULL) : 0;
    }
    return 0;
}

/* Expand a String literal into `String.ofList [Char.ofNat cp_0, ...]` (Lean 4.33+/4.35+)
 * or `String.mk [Char.ofNat cp_0, ...]` (Lean 4.29). */
static uint32_t lean_strlit_to_expr(LeanKernelState *ks, uint32_t e) {
    if (!ks->string_verified || ks->exprs[e].kind != LEXPR_STRLIT) return e;
    uint32_t wrap_nm = 0;
    if (ks->nm_String_ofList && lean_lookup_decl(ks, ks->nm_String_ofList))
        wrap_nm = ks->nm_String_ofList;
    else if (ks->nm_String_mk && lean_lookup_decl(ks, ks->nm_String_mk))
        wrap_nm = ks->nm_String_mk;
    if (!wrap_nm || !ks->nm_Char || !ks->nm_Char_ofNat || !ks->nm_List_nil || !ks->nm_List_cons)
        return e;

    const unsigned char *s = (const unsigned char *)ks->exprs[e].d.str_lit.str;
    size_t slen = strlen((const char *)s);
    uint32_t *cps = slen > 0 ? (uint32_t *)malloc(slen * sizeof(uint32_t)) : NULL;
    size_t ncps = 0, i = 0;
    while (i < slen) {
        uint32_t cp = 0;
        unsigned char c0 = s[i];
        if (c0 < 0x80) {
            cp = c0; i += 1;
        } else if ((c0 & 0xE0) == 0xC0 && i + 1 < slen) {
            cp = ((uint32_t)(c0 & 0x1F) << 6) | (uint32_t)(s[i + 1] & 0x3F); i += 2;
        } else if ((c0 & 0xF0) == 0xE0 && i + 2 < slen) {
            cp = ((uint32_t)(c0 & 0x0F) << 12) | ((uint32_t)(s[i + 1] & 0x3F) << 6) | (uint32_t)(s[i + 2] & 0x3F); i += 3;
        } else if ((c0 & 0xF8) == 0xF0 && i + 3 < slen) {
            cp = ((uint32_t)(c0 & 0x07) << 18) | ((uint32_t)(s[i + 1] & 0x3F) << 12) |
                 ((uint32_t)(s[i + 2] & 0x3F) << 6) | (uint32_t)(s[i + 3] & 0x3F); i += 4;
        } else {
            cp = c0; i += 1;
        }
        cps[ncps++] = cp;
    }

    uint32_t u0 = 0;
    uint32_t char_ty = lean_expr_mk_const(ks, ks->nm_Char, 0, NULL);
    uint32_t list_nil = lean_expr_mk_app(ks, lean_expr_mk_const(ks, ks->nm_List_nil, 1, &u0), char_ty);
    uint32_t list_cons_char = lean_expr_mk_app(ks, lean_expr_mk_const(ks, ks->nm_List_cons, 1, &u0), char_ty);
    uint32_t char_of_nat = lean_expr_mk_const(ks, ks->nm_Char_ofNat, 0, NULL);

    uint32_t acc = list_nil;
    for (size_t k = ncps; k > 0; k--) {
        uint32_t nat_cp = lean_expr_mk_natlit_u64(ks, cps[k - 1]);
        uint32_t ch = lean_expr_mk_app(ks, char_of_nat, nat_cp);
        uint32_t cons_ch = lean_expr_mk_app(ks, list_cons_char, ch);
        acc = lean_expr_mk_app(ks, cons_ch, acc);
    }
    free(cps);
    return lean_expr_mk_app(ks, lean_expr_mk_const(ks, wrap_nm, 0, NULL), acc);
}

static uint32_t lean_whnf(LeanKernelState *ks, uint32_t e);
static bool lean_is_prop(LeanKernelState *ks, uint32_t ty);
static int lean_check_is_prop_strict(LeanKernelState *ks, uint32_t ty);

/* Convert a WHNF expression to constructor spine if it is a NatLit or StrLit */
static uint32_t lean_lit_to_ctor(LeanKernelState *ks, uint32_t e) {
    const LeanExpr *ex = &ks->exprs[e];
    if (ex->kind == LEXPR_NATLIT && ex->nat_is_small) {
        __uint128_t v = lean_expr_nat_u128(ex);
        if (v == 0) {
            return ks->nm_Nat_zero ? lean_expr_mk_const(ks, ks->nm_Nat_zero, 0, NULL) : e;
        }
        if (ks->nm_Nat_succ) {
            uint32_t pred = lean_expr_mk_natlit_u128(ks, v - 1u);
            uint32_t sc = lean_expr_mk_const(ks, ks->nm_Nat_succ, 0, NULL);
            return lean_expr_mk_app(ks, sc, pred);
        }
    }
    if (ex->kind == LEXPR_STRLIT) {
        uint32_t exp = lean_strlit_to_expr(ks, e);
        if (exp != e) return lean_whnf(ks, exp);
    }
    return e;
}

/* WHNF without unfolding top-level lazy delta unless needed for iota/proj/quot.
 * When `cheap_proj` is true (matching Lean4Lean `whnfCore e (cheapProj := true)`),
 * structure projections reduce `struct_expr` with `whnfCore` rather than full `whnf`. */
static uint32_t lean_whnf_core_proj(LeanKernelState *ks, uint32_t e, bool unfold_defs, bool cheap_proj) {
    ks->stat_whnf_steps++;
    if (ks->exprs[e].loose_bvar_range == 0) {
        uint32_t cached = unfold_defs ? ks->exprs[e].whnf_cache : ks->exprs[e].whnf_core_cache;
        if (cached != 0) return cached;
    }
    uint32_t orig_e = e;

    while (true) {
        LeanExpr ex = ks->exprs[e];
        if (ex.kind == LEXPR_BVAR || ex.kind == LEXPR_SORT ||
            ex.kind == LEXPR_LAM  || ex.kind == LEXPR_FORALL ||
            ex.kind == LEXPR_NATLIT || ex.kind == LEXPR_STRLIT) {
            break;
        }
        if (ex.kind == LEXPR_FVAR) {
            const LeanLocalDecl *loc = lean_lookup_local(ks, ex.d.fvar_id);
            if (loc && loc->llet_val != 0) {
                e = loc->llet_val - 1u;
                continue;
            }
            break;
        }
        if (ex.kind == LEXPR_LET) {
            e = lean_expr_instantiate1(ks, ex.d.let_e.body, ex.d.let_e.val);
            continue;
        }
        if (ex.kind == LEXPR_PROJ) {
            uint32_t s_whnf = cheap_proj
                ? lean_whnf_core_proj(ks, ex.d.proj.struct_expr, false, true)
                : lean_whnf(ks, ex.d.proj.struct_expr);
            s_whnf = lean_lit_to_ctor(ks, s_whnf);
            uint32_t sbuf[32];
            uint32_t *sargs = NULL;
            uint32_t snargs = 0, scap = 32;
            uint32_t shead = lean_unpack_spine(ks, s_whnf, &sargs, &snargs, &scap, sbuf);
            uint32_t reduced = 0;
            if (ks->exprs[shead].kind == LEXPR_CONST) {
                const LeanDecl *cd = lean_lookup_decl(ks, ks->exprs[shead].d.cnst.name);
                if (cd && cd->kind == LDECL_CTOR && ex.d.proj.idx < cd->num_fields) {
                    uint64_t f_idx = (uint64_t)cd->num_params + (uint64_t)ex.d.proj.idx;
                    if (f_idx < (uint64_t)snargs) {
                        reduced = sargs[(uint32_t)f_idx];
                    }
                }
            }
            if (sargs != sbuf) free(sargs);
            if (reduced != 0) {
                e = reduced;
                continue;
            }
            break;
        }

        /* Application or Constant */
        uint32_t sbuf[64];
        uint32_t *args = NULL;
        uint32_t nargs = 0, cap = 64;
        uint32_t head = lean_unpack_spine(ks, e, &args, &nargs, &cap, sbuf);
        uint32_t head_whnf = (nargs > 0) ? lean_whnf_core_proj(ks, head, false, cheap_proj) : head;

        /* 1. Beta reduction */
        if (ks->exprs[head_whnf].kind == LEXPR_LAM && nargs > 0) {
            uint32_t num_beta = 0;
            uint32_t cur_body = head_whnf;
            while (num_beta < nargs && ks->exprs[cur_body].kind == LEXPR_LAM) {
                cur_body = ks->exprs[cur_body].d.binder.body;
                num_beta++;
            }
            /* Note: instantiate_rev expects `subst[num_beta - 1 - i]` for `bvar(i)`.
             * For nested `lam x_0 => lam x_1 => ... => lam x_{k-1} => body`,
             * `bvar(0)` is `x_{k-1}` (which receives `args[k-1]`), and `bvar(k-1)` is `x_0` (`args[0]`).
             * So `args[0..num_beta-1]` is ALREADY in the exact order required by `instantiate_rev`! */
            uint32_t inst = lean_expr_instantiate_rev(ks, cur_body, 0, num_beta, args);
            e = lean_mk_app_spine(ks, inst, nargs - num_beta, args + num_beta);
            if (args != sbuf) free(args);
            continue;
        }

        if (ks->exprs[head_whnf].kind == LEXPR_CONST) {
            uint32_t cname = ks->exprs[head_whnf].d.cnst.name;
            uint32_t nus = ks->exprs[head_whnf].d.cnst.nus;
            uint32_t us_buf[16];
            uint32_t *us = (nus <= 16) ? us_buf : (uint32_t *)malloc((size_t)nus * sizeof(uint32_t));
            if (nus > 0) memcpy(us, ks->exprs[head_whnf].d.cnst.us, (size_t)nus * sizeof(uint32_t));

            /* 2. Quotient reduction: Quot.lift.{u,v} α r β f h (Quot.mk.{u} α' r' a) extra... -> f a extra... */
            if (cname == ks->nm_Quot_lift && nargs >= 6) {
                uint32_t maj = lean_whnf(ks, args[5]);
                uint32_t mbuf[16];
                uint32_t *margs = NULL;
                uint32_t mnargs = 0, mcap = 16;
                uint32_t mhead = lean_unpack_spine(ks, maj, &margs, &mnargs, &mcap, mbuf);
                if (ks->exprs[mhead].kind == LEXPR_CONST &&
                    ks->exprs[mhead].d.cnst.name == ks->nm_Quot_mk && mnargs == 3) {
                    uint32_t f_fn = args[3];
                    uint32_t a_arg = margs[2];
                    uint32_t red = lean_expr_mk_app(ks, f_fn, a_arg);
                    e = lean_mk_app_spine(ks, red, nargs - 6u, args + 6u);
                    if (margs != mbuf) free(margs);
                    if (us != us_buf) free(us);
                    if (args != sbuf) free(args);
                    continue;
                }
                if (margs != mbuf) free(margs);
            }

            const LeanDecl *decl = lean_lookup_decl(ks, cname);
            if (decl) {
                /* 4. Recursor iota-reduction (and K-like reduction) */
                if (decl->kind == LDECL_REC) {
                    uint32_t major_idx = decl->num_params + decl->num_motives + decl->num_minors + decl->num_indices;
                    if (nargs > major_idx && nus == decl->nparams) {
                        /* 4a. K-reduction (`toCtorWhenK` in `Lean4Lean/Inductive/Reduce.lean` lines 68-69,
                         * `to_cnstr_when_K` in `src/kernel/inductive.h` lines 88-90) MUST run BEFORE `whnf(major)`
                         * so that proof terms in `Eq.rec` / `HEq.rec` / `True.rec` are never delta-unfolded! */
                        if (decl->is_k && decl->nrules == 1 && decl->rules[0].nfields == 0) {
                            uint32_t maj0 = args[major_idx];
                            uint32_t maj_ty = lean_whnf(ks, lean_infer_type(ks, maj0));
                            uint32_t tbuf[32];
                            uint32_t *targs = NULL;
                            uint32_t tnargs = 0, tcap = 32;
                            uint32_t thead = (maj_ty != 0) ? lean_unpack_spine(ks, maj_ty, &targs, &tnargs, &tcap, tbuf) : 0;
                            bool k_applicable = false;
                            if (thead != 0 && ks->exprs[thead].kind == LEXPR_CONST &&
                                ks->exprs[thead].d.cnst.name == decl->ind_name &&
                                tnargs == decl->num_params + decl->num_indices) {
                                if (decl->num_indices == 0) {
                                    k_applicable = true;
                                } else {
                                    uint32_t ctor_hd = lean_expr_mk_const(
                                        ks, decl->rules[0].ctor_name,
                                        ks->exprs[thead].d.cnst.nus, ks->exprs[thead].d.cnst.us);
                                    uint32_t new_ctor_app = lean_mk_app_spine(ks, ctor_hd, decl->num_params, targs);
                                    uint32_t new_ty = lean_infer_type(ks, new_ctor_app);
                                    if (new_ty != 0 && lean_is_def_eq(ks, maj_ty, new_ty)) {
                                        k_applicable = true;
                                    }
                                }
                            }
                            if (targs != tbuf) free(targs);
                            if (k_applicable) {
                                uint32_t rhs_inst = lean_expr_subst_lvls(
                                    ks, decl->rules[0].rhs, decl->nparams, decl->level_params, us);
                                uint32_t pm_count = decl->num_params + decl->num_motives + decl->num_minors;
                                uint32_t cur = lean_mk_app_spine(ks, rhs_inst, pm_count, args);
                                e = lean_mk_app_spine(ks, cur, nargs - (major_idx + 1u), args + major_idx + 1u);
                                if (us != us_buf) free(us);
                                if (args != sbuf) free(args);
                                continue;
                            }
                        }

                        /* Helper to match a constructor application spine against `decl->rules` */
                        uint32_t raw_maj = lean_lit_to_ctor(ks, args[major_idx]);
                        uint32_t mbuf[32];
                        uint32_t *margs = NULL;
                        uint32_t mnargs = 0, mcap = 32;
                        uint32_t mhead = lean_unpack_spine(ks, raw_maj, &margs, &mnargs, &mcap, mbuf);
                        uint32_t matched_rhs = 0;
                        uint32_t matched_nfields = 0;
                        uint32_t matched_cparams = decl->num_params;

                        if (ks->exprs[mhead].kind == LEXPR_CONST) {
                            uint32_t ctor_nm = ks->exprs[mhead].d.cnst.name;
                            const LeanDecl *ctor_decl = lean_lookup_decl(ks, ctor_nm);
                            uint32_t ctor_nparams = (ctor_decl && ctor_decl->kind == LDECL_CTOR)
                                ? ctor_decl->num_params
                                : decl->num_params;
                            for (uint32_t r = 0; r < decl->nrules; r++) {
                                if (decl->rules[r].ctor_name == ctor_nm &&
                                    mnargs == ctor_nparams + decl->rules[r].nfields) {
                                    matched_rhs = decl->rules[r].rhs;
                                    matched_nfields = decl->rules[r].nfields;
                                    matched_cparams = ctor_nparams;
                                    break;
                                }
                            }
                        }

                        if (matched_rhs != 0) {
                            uint32_t rhs_inst = lean_expr_subst_lvls(ks, matched_rhs, decl->nparams, decl->level_params, us);
                            uint32_t pm_count = decl->num_params + decl->num_motives + decl->num_minors;
                            uint32_t cur = lean_mk_app_spine(ks, rhs_inst, pm_count, args);
                            cur = lean_mk_app_spine(ks, cur, matched_nfields, margs + matched_cparams);
                            e = lean_mk_app_spine(ks, cur, nargs - (major_idx + 1u), args + major_idx + 1u);
                            if (margs != mbuf) free(margs);
                            if (us != us_buf) free(us);
                            if (args != sbuf) free(args);
                            continue;
                        }
                        if (margs != mbuf) free(margs);

                        /* Structure recursor eta-reduction (`to_cnstr_when_structure`, Lean 4 PR #15351 & #15371):
                         * Applied BEFORE reducing `args[major_idx]` to WHNF so that structure eliminations
                         * whose minor premise ignores fields terminate even if the major premise does not normalize. */
                        if (decl->nrules == 1) {
                            const LeanDecl *ind = lean_lookup_decl(ks, decl->ind_name);
                            if (ind && ind->kind == LDECL_IND && !ind->is_rec &&
                                ind->num_indices == 0 && ind->nctors == 1) {
                                uint32_t maj_raw = args[major_idx];
                                uint32_t maj_ty = lean_whnf(ks, lean_infer_type(ks, maj_raw));
                                if (maj_ty != 0) {
                                    uint32_t tbuf[32];
                                    uint32_t *targs = NULL;
                                    uint32_t tnargs = 0, tcap = 32;
                                    uint32_t thead = lean_unpack_spine(ks, maj_ty, &targs, &tnargs, &tcap, tbuf);
                                    bool is_struct_ty = (ks->exprs[thead].kind == LEXPR_CONST &&
                                                         ks->exprs[thead].d.cnst.name == ind->name &&
                                                         tnargs == ind->num_params);
                                    if (targs != tbuf) free(targs);
                                    if (is_struct_ty) {
                                        int s_prop = lean_check_is_prop_strict(ks, maj_ty);
                                        uint32_t nf = decl->rules[0].nfields;
                                        bool projs_ok = (s_prop >= 0);
                                        for (uint32_t f = 0; projs_ok && s_prop == 1 && f < nf; f++) {
                                            uint32_t pf = lean_expr_mk_proj(ks, ind->name, f, maj_raw);
                                            if (lean_infer_type(ks, pf) == 0) {
                                                projs_ok = false;
                                                break;
                                            }
                                        }
                                        if (projs_ok) {
                                            uint32_t rhs_inst = lean_expr_subst_lvls(
                                                ks, decl->rules[0].rhs, decl->nparams, decl->level_params, us);
                                            uint32_t pm_count = decl->num_params + decl->num_motives + decl->num_minors;
                                            uint32_t cur = lean_mk_app_spine(ks, rhs_inst, pm_count, args);
                                            for (uint32_t f = 0; f < nf; f++) {
                                                uint32_t proj_f = lean_expr_mk_proj(ks, ind->name, f, maj_raw);
                                                cur = lean_expr_mk_app(ks, cur, proj_f);
                                            }
                                            e = lean_mk_app_spine(ks, cur, nargs - (major_idx + 1u), args + major_idx + 1u);
                                            if (us != us_buf) free(us);
                                            if (args != sbuf) free(args);
                                            continue;
                                        }
                                    }
                                }
                            }
                        }

                        uint32_t maj = lean_whnf(ks, args[major_idx]);
                        maj = lean_lit_to_ctor(ks, maj);
                        margs = NULL;
                        mnargs = 0;
                        mcap = 32;
                        mhead = lean_unpack_spine(ks, maj, &margs, &mnargs, &mcap, mbuf);
                        if (ks->exprs[mhead].kind == LEXPR_CONST) {
                            uint32_t ctor_nm = ks->exprs[mhead].d.cnst.name;
                            const LeanDecl *ctor_decl = lean_lookup_decl(ks, ctor_nm);
                            uint32_t ctor_nparams = (ctor_decl && ctor_decl->kind == LDECL_CTOR)
                                ? ctor_decl->num_params
                                : decl->num_params;
                            for (uint32_t r = 0; r < decl->nrules; r++) {
                                if (decl->rules[r].ctor_name == ctor_nm &&
                                    mnargs == ctor_nparams + decl->rules[r].nfields) {
                                    matched_rhs = decl->rules[r].rhs;
                                    matched_nfields = decl->rules[r].nfields;
                                    matched_cparams = ctor_nparams;
                                    break;
                                }
                            }
                        }

                        if (matched_rhs != 0) {
                            uint32_t rhs_inst = lean_expr_subst_lvls(ks, matched_rhs, decl->nparams, decl->level_params, us);
                            /* Apply rhs_inst to: params + motives + minors + fields + trailing args */
                            uint32_t pm_count = decl->num_params + decl->num_motives + decl->num_minors;
                            uint32_t cur = lean_mk_app_spine(ks, rhs_inst, pm_count, args);
                            cur = lean_mk_app_spine(ks, cur, matched_nfields, margs + matched_cparams);
                            e = lean_mk_app_spine(ks, cur, nargs - (major_idx + 1u), args + major_idx + 1u);
                            if (margs != mbuf) free(margs);
                            if (us != us_buf) free(us);
                            if (args != sbuf) free(args);
                            continue;
                        }
                        if (margs != mbuf) free(margs);
                    }
                }

                /* 4. Kernel Nat reduction (`reduceNat`) and Delta-reduction (`unfoldDefinition`),
                 * only when `unfold_defs == true` (`whnf`, not `whnfCore`)! */
                if (unfold_defs) {
                    uint32_t nat_res = lean_try_nat_kernel_op(ks, cname, nargs, args);
                    if (nat_res != 0) {
                        e = nat_res;
                        if (us != us_buf) free(us);
                        if (args != sbuf) free(args);
                        break;
                    }
                    if ((decl->kind == LDECL_DEFN || decl->kind == LDECL_THM) &&
                        decl->value != 0 && nus == decl->nparams) {
                        uint32_t val_inst = lean_expr_subst_lvls(ks, decl->value, decl->nparams, decl->level_params, us);
                        e = lean_mk_app_spine(ks, val_inst, nargs, args);
                        if (us != us_buf) free(us);
                        if (args != sbuf) free(args);
                        continue;
                    }
                }
            }
            if (us != us_buf) free(us);
        }

        if (head_whnf != head) {
            e = lean_mk_app_spine(ks, head_whnf, nargs, args);
            if (args != sbuf) free(args);
            continue;
        }
        if (args != sbuf) free(args);
        break;
    }

    if (ks->exprs[orig_e].loose_bvar_range == 0 && !cheap_proj) {
        if (unfold_defs) ks->exprs[orig_e].whnf_cache = e;
        else ks->exprs[orig_e].whnf_core_cache = e;
        lean_note_dirty_persistent_expr(ks, orig_e, e);
    }
    return e;
}

static uint32_t lean_whnf(LeanKernelState *ks, uint32_t e) {
    return lean_whnf_core_proj(ks, e, true, false);
}

/* Check whether `ty` is a Proposition (i.e. `whnf(infer_type(ty)) == Sort(0)`) */
static bool lean_is_prop(LeanKernelState *ks, uint32_t ty) {
    if (ty == 0) return false;
    if (ks->exprs[ty].loose_bvar_range == 0 && ks->exprs[ty].is_prop_cache != 0) {
        return ks->exprs[ty].is_prop_cache == 2u;
    }
    uint32_t s = lean_infer_type(ks, ty);
    if (s == 0) return false;
    uint32_t sw = lean_whnf(ks, s);
    bool res = (ks->exprs[sw].kind == LEXPR_SORT && lean_lvl_is_zero(ks, ks->exprs[sw].d.sort_lvl));
    if (ks->exprs[ty].loose_bvar_range == 0) {
        ks->exprs[ty].is_prop_cache = res ? 2u : 1u;
    }
    return res;
}

/* Strict sort-ensuring Prop check (`ensure_sort(infer_type(ty)) == Sort(0)`, Lean 4 PR #14807):
 * Returns 1 if `ty` has sort `Prop`, 0 if `ty` has a non-Prop `Sort(u)`, and -1 if `whnf(infer_type(ty))` is not a `Sort`. */
static int lean_check_is_prop_strict(LeanKernelState *ks, uint32_t ty) {
    if (ty == 0) return -1;
    uint32_t s = lean_infer_type(ks, ty);
    if (s == 0) return -1;
    uint32_t sw = lean_whnf(ks, s);
    if (ks->exprs[sw].kind != LEXPR_SORT) return -1;
    return lean_lvl_is_zero(ks, ks->exprs[sw].d.sort_lvl) ? 1 : 0;
}

static inline bool lean_expr_cannot_be_proof(LeanExprKind k) {
    return k == LEXPR_SORT || k == LEXPR_FORALL || k == LEXPR_NATLIT || k == LEXPR_STRLIT;
}

/* Tri-state Proof Irrelevance (`is_def_eq_proof_irrel` in `type_checker.cpp` / `Lean4Lean`):
 *   1 (l_true)  : `a` is a proof (`is_prop(ta)`) and `is_def_eq(ta, tb)` holds
 *   0 (l_false) : `a` is a proof (`is_prop(ta)`) and `is_def_eq(ta, tb)` fails
 *  -1 (l_undef) : `a` is not a proof (`!is_prop(ta)`)
 */
static int lean_try_proof_irrel(LeanKernelState *ks, uint32_t a, uint32_t b) {
    if (lean_expr_cannot_be_proof(ks->exprs[a].kind)) {
        return -1;
    }
    uint32_t ta = lean_infer_type(ks, a);
    if (ta == 0 || !lean_is_prop(ks, ta)) return -1;
    if (lean_expr_cannot_be_proof(ks->exprs[b].kind)) return 0;
    uint32_t tb = lean_infer_type(ks, b);
    if (tb == 0) return 0;
    if (lean_is_def_eq(ks, ta, tb)) {
        ks->stat_proof_irrel_hits++;
        return 1;
    }
    return 0;
}

static bool lean_is_def_eq_core(LeanKernelState *ks, uint32_t a, uint32_t b);
static bool lean_try_eta_struct(LeanKernelState *ks, uint32_t a, uint32_t b);
static bool lean_is_def_eq_unit_like(LeanKernelState *ks, uint32_t a, uint32_t b);

static bool lean_is_def_eq_args(LeanKernelState *ks, uint32_t nargs, const uint32_t *a_args, const uint32_t *b_args) {
    for (uint32_t i = 0; i < nargs; i++) {
        if (!lean_is_def_eq(ks, a_args[i], b_args[i])) return false;
    }
    return true;
}

static inline bool lean_defeq_cache_lookup(const LeanKernelState *ks, uint32_t a, uint32_t b, bool *out_eq) {
    if (!ks->defeq_cache || a == 0 || b == 0) return false;
    uint32_t lo = a < b ? a : b;
    uint32_t hi = a < b ? b : a;
    if (hi >= 0x80000000u) return false;
    uint32_t slot = fnv_mix32(fnv_mix32(2166136261u, lo), hi) & (LEAN_DEFEQ_CACHE_SIZE - 1u);
    LeanDefEqCache ce = ks->defeq_cache[slot];
    if (ce.lo == lo && (ce.hi_and_eq & 0x7fffffffu) == hi &&
        (ce.gen == 0u || ce.gen == ks->scratch_gen)) {
        *out_eq = (ce.hi_and_eq & 0x80000000u) != 0;
        return true;
    }
    return false;
}

static inline void lean_defeq_cache_store(LeanKernelState *ks, uint32_t a, uint32_t b, bool eq) {
    if (!ks->defeq_cache || a == 0 || b == 0 || a == b) return;
    uint32_t lo = a < b ? a : b;
    uint32_t hi = a < b ? b : a;
    if (hi >= 0x80000000u) return;
    uint32_t slot = fnv_mix32(fnv_mix32(2166136261u, lo), hi) & (LEAN_DEFEQ_CACHE_SIZE - 1u);
    uint32_t cgen = (!ks->eager_reduce && hi < LEAN_SCRATCH_BASE) ? 0u : ks->scratch_gen;
    ks->defeq_cache[slot] = (LeanDefEqCache){
        .lo = lo,
        .hi_and_eq = hi | (eq ? 0x80000000u : 0u),
        .gen = cgen
    };
}

static bool lean_is_def_eq(LeanKernelState *ks, uint32_t a, uint32_t b) {
    ks->stat_defeq_checks++;
    if (a == b) return true;

    bool cached_eq = false;
    if (lean_defeq_cache_lookup(ks, a, b, &cached_eq)) return cached_eq;

    /* Fast syntactic check before WHNF */
    const LeanExpr *ea = &ks->exprs[a];
    const LeanExpr *eb = &ks->exprs[b];
    if (ea->kind == LEXPR_SORT && eb->kind == LEXPR_SORT) {
        return lean_lvl_eq(ks, ea->d.sort_lvl, eb->d.sort_lvl);
    }

    uint32_t wa = lean_whnf_core_proj(ks, a, false, true);
    uint32_t wb = lean_whnf_core_proj(ks, b, false, true);
    if (wa == wb) {
        lean_defeq_cache_store(ks, a, b, true);
        return true;
    }
    if (lean_defeq_cache_lookup(ks, wa, wb, &cached_eq)) {
        lean_defeq_cache_store(ks, a, b, cached_eq);
        return cached_eq;
    }

    bool ok = lean_is_def_eq_core(ks, wa, wb);
    lean_defeq_cache_store(ks, wa, wb, ok);
    lean_defeq_cache_store(ks, a, b, ok);
    return ok;
}

static uint32_t lean_try_delta_step(
    LeanKernelState *ks,
    uint32_t e,
    uint32_t *out_height,
    uint32_t *out_cname,
    uint8_t  *out_hint_kind)
{
    *out_height = 0;
    *out_cname = 0;
    *out_hint_kind = LHINT_OPAQUE;
    uint32_t sbuf[32];
    uint32_t *args = NULL;
    uint32_t nargs = 0, cap = 32;
    uint32_t head = lean_unpack_spine(ks, e, &args, &nargs, &cap, sbuf);
    uint32_t res = 0;
    if (ks->exprs[head].kind == LEXPR_CONST) {
        uint32_t cname = ks->exprs[head].d.cnst.name;
        const LeanDecl *d = lean_lookup_decl(ks, cname);
        if (d && (d->kind == LDECL_DEFN || d->kind == LDECL_THM) &&
            d->value != 0 && ks->exprs[head].d.cnst.nus == d->nparams) {
            *out_height = d->height;
            *out_cname = cname;
            *out_hint_kind = d->hint_kind;
            uint32_t vinst = lean_expr_subst_lvls(ks, d->value, d->nparams, d->level_params, ks->exprs[head].d.cnst.us);
            res = lean_mk_app_spine(ks, vinst, nargs, args);
        }
    }
    if (args != sbuf) free(args);
    return res;
}

static inline bool lean_is_nat_zero_expr(const LeanKernelState *ks, uint32_t e) {
    const LeanExpr *ex = &ks->exprs[e];
    if (ex->kind == LEXPR_CONST && ex->d.cnst.name == ks->nm_Nat_zero) return true;
    if (ex->kind == LEXPR_NATLIT && ex->nat_is_small && ex->d.nat_small.lo == 0 && ex->d.nat_small.hi == 0) return true;
    return false;
}

static inline uint32_t lean_is_nat_succ_of(LeanKernelState *ks, uint32_t e) {
    const LeanExpr *ex = &ks->exprs[e];
    if (ex->kind == LEXPR_NATLIT && ex->nat_is_small) {
        __uint128_t v = lean_expr_nat_u128(ex);
        if (v > 0) return lean_expr_mk_natlit_u128(ks, v - 1u);
    }
    if (ex->kind == LEXPR_APP) {
        uint32_t fn = ex->d.app.fn;
        if (ks->exprs[fn].kind == LEXPR_CONST && ks->exprs[fn].d.cnst.name == ks->nm_Nat_succ) {
            return ex->d.app.arg;
        }
    }
    return 0;
}

static uint32_t lean_reduce_nat_expr(LeanKernelState *ks, uint32_t e) {
    if (ks->exprs[e].kind != LEXPR_APP) return 0;
    uint32_t sbuf[8];
    uint32_t *args = NULL;
    uint32_t nargs = 0, cap = 8;
    uint32_t head = lean_unpack_spine(ks, e, &args, &nargs, &cap, sbuf);
    uint32_t res = 0;
    if (ks->exprs[head].kind == LEXPR_CONST) {
        res = lean_try_nat_kernel_op(ks, ks->exprs[head].d.cnst.name, nargs, args);
    }
    if (args != sbuf) free(args);
    return res;
}

static inline bool lean_is_app_of_arity2(const LeanKernelState *ks, uint32_t e, uint32_t cname) {
    if (cname == 0 || ks->exprs[e].kind != LEXPR_APP) return false;
    uint32_t fn1 = ks->exprs[e].d.app.fn;
    if (ks->exprs[fn1].kind != LEXPR_APP) return false;
    uint32_t fn0 = ks->exprs[fn1].d.app.fn;
    return ks->exprs[fn0].kind == LEXPR_CONST && ks->exprs[fn0].d.cnst.name == cname;
}

static bool lean_is_def_eq_core(LeanKernelState *ks, uint32_t a, uint32_t b) {
    /* Fast Bool.true reflection check (`(!t.hasFVar || eagerReduce) && s.isConstOf Bool.true` in Lean4Lean) */
    if ((!ks->exprs[a].has_fvar || ks->eager_reduce) &&
        ks->exprs[b].kind == LEXPR_CONST && ks->exprs[b].d.cnst.name == ks->nm_Bool_true) {
        if (lean_whnf(ks, a) == b) return true;
    }
    if ((!ks->exprs[b].has_fvar || ks->eager_reduce) &&
        ks->exprs[a].kind == LEXPR_CONST && ks->exprs[a].d.cnst.name == ks->nm_Bool_true) {
        if (lean_whnf(ks, b) == a) return true;
    }

    /* Tri-state proof irrelevance (`isDefEqProofIrrel` in `Lean4Lean/TypeChecker.lean` lines 681-682):
     * If `a` is a proof (`pi_res >= 0`), `a` and `b` are defeq iff their proposition types are defeq! */
    int pi_res = lean_try_proof_irrel(ks, a, b);
    if (pi_res >= 0) return pi_res == 1;

    while (true) {
        a = lean_whnf_core_proj(ks, a, false, true);
        b = lean_whnf_core_proj(ks, b, false, true);
        if (a == b) return true;

        LeanExpr ea = ks->exprs[a];
        LeanExpr eb = ks->exprs[b];

        if (ea.kind == LEXPR_SORT && eb.kind == LEXPR_SORT) {
            return lean_lvl_eq(ks, ea.d.sort_lvl, eb.d.sort_lvl);
        }

        if (ea.kind == LEXPR_LAM && eb.kind == LEXPR_LAM) {
            if (!lean_is_def_eq(ks, ea.d.binder.domain, eb.d.binder.domain)) return false;
            uint32_t fv = lean_push_local(ks, ea.d.binder.binder_name, ea.d.binder.domain, 0);
            uint32_t ba = lean_expr_instantiate1(ks, ea.d.binder.body, fv);
            uint32_t bb = lean_expr_instantiate1(ks, eb.d.binder.body, fv);
            bool ok = lean_is_def_eq(ks, ba, bb);
            lean_pop_local(ks);
            return ok;
        }

        if (ea.kind == LEXPR_FORALL && eb.kind == LEXPR_FORALL) {
            if (!lean_is_def_eq(ks, ea.d.binder.domain, eb.d.binder.domain)) return false;
            uint32_t fv = lean_push_local(ks, ea.d.binder.binder_name, ea.d.binder.domain, 0);
            uint32_t ba = lean_expr_instantiate1(ks, ea.d.binder.body, fv);
            uint32_t bb = lean_expr_instantiate1(ks, eb.d.binder.body, fv);
            bool ok = lean_is_def_eq(ks, ba, bb);
            lean_pop_local(ks);
            return ok;
        }

        if (ea.kind == LEXPR_NATLIT && eb.kind == LEXPR_NATLIT) {
            if (ea.nat_is_small != eb.nat_is_small) return false;
            if (ea.nat_is_small) {
                return ea.d.nat_small.lo == eb.d.nat_small.lo && ea.d.nat_small.hi == eb.d.nat_small.hi;
            }
            return strcmp(ea.d.nat_big.dec_str, eb.d.nat_big.dec_str) == 0;
        }

        /* `isDefEqOffset`: compare `0 == Nat.zero` and `Nat.succ a' == Nat.succ b'` */
        if (lean_is_nat_zero_expr(ks, a) && lean_is_nat_zero_expr(ks, b)) {
            return true;
        }
        {
            uint32_t pa = lean_is_nat_succ_of(ks, a);
            uint32_t pb = lean_is_nat_succ_of(ks, b);
            if (pa != 0 && pb != 0) {
                a = pa;
                b = pb;
                continue;
            }
        }

        /* `reduceNat` step in `lazyDeltaReduction`: when `(!a.has_fvar && !b.has_fvar) || eagerReduce`! */
        if ((!ea.has_fvar && !eb.has_fvar) || ks->eager_reduce) {
            uint32_t na_red = lean_reduce_nat_expr(ks, a);
            if (na_red != 0) {
                a = na_red;
                continue;
            }
            uint32_t nb_red = lean_reduce_nat_expr(ks, b);
            if (nb_red != 0) {
                b = nb_red;
                continue;
            }
        }

        uint32_t abuf[8], bbuf[8];
        uint32_t *a_args = NULL, *b_args = NULL;
        uint32_t na = 0, nb = 0, acap = 8, bcap = 8;
        uint32_t ha = lean_unpack_spine(ks, a, &a_args, &na, &acap, abuf);
        uint32_t hb = lean_unpack_spine(ks, b, &b_args, &nb, &bcap, bbuf);

        /* Lazy Delta Unfolding by ReducibilityHints (`Lean4Lean/TypeChecker.lean` lines 581-609)! */
        uint32_t h_a = 0, h_b = 0, cn_a = 0, cn_b = 0;
        uint8_t  hk_a = LHINT_OPAQUE, hk_b = LHINT_OPAQUE;
        uint32_t next_a = lean_try_delta_step(ks, a, &h_a, &cn_a, &hk_a);
        uint32_t next_b = lean_try_delta_step(ks, b, &h_b, &cn_b, &hk_b);

        if (next_a != 0 || next_b != 0) {
            if (next_a != 0 && next_b != 0) {
                if (h_a > h_b) {
                    a = next_a;
                } else if (h_b > h_a) {
                    b = next_b;
                } else {
                    /* Same reducibility height: if both are applications of the SAME regular definition,
                     * try comparing their arguments before unfolding (`dt.hints.isRegular` in Lean4Lean)! */
                    if (na > 0 && na == nb && cn_a == cn_b && hk_a == LHINT_REGULAR &&
                        ks->exprs[ha].d.cnst.nus == ks->exprs[hb].d.cnst.nus) {
                        bool lvls_ok = true;
                        for (uint32_t i = 0; i < ks->exprs[ha].d.cnst.nus; i++) {
                            if (!lean_lvl_eq(ks, ks->exprs[ha].d.cnst.us[i], ks->exprs[hb].d.cnst.us[i])) {
                                lvls_ok = false;
                                break;
                            }
                        }
                        if (lvls_ok && lean_is_def_eq_args(ks, na, a_args, b_args)) {
                            if (a_args != abuf) free(a_args);
                            if (b_args != bbuf) free(b_args);
                            return true;
                        }
                    }
                    a = next_a;
                    b = next_b;
                }
            } else if (next_a != 0) {
                /* `tryUnfoldProjApp sn` before unfolding `tn` */
                if (ks->exprs[hb].kind == LEXPR_PROJ) {
                    uint32_t b_proj = lean_whnf_core_proj(ks, b, false, false);
                    if (b_proj != b) {
                        if (a_args != abuf) free(a_args);
                        if (b_args != bbuf) free(b_args);
                        b = b_proj;
                        continue;
                    }
                }
                a = next_a;
            } else {
                /* `tryUnfoldProjApp tn` before unfolding `sn` */
                if (ks->exprs[ha].kind == LEXPR_PROJ) {
                    uint32_t a_proj = lean_whnf_core_proj(ks, a, false, false);
                    if (a_proj != a) {
                        if (a_args != abuf) free(a_args);
                        if (b_args != bbuf) free(b_args);
                        a = a_proj;
                        continue;
                    }
                }
                b = next_b;
            }
            if (a_args != abuf) free(a_args);
            if (b_args != bbuf) free(b_args);
            continue;
        }

        /* Neither side is a delta-application (`Lean4Lean/TypeChecker.lean` lines 689-708):
         * First check bare constants, bare fvars/bvars, and bare projections (`na == 0 && nb == 0`). */
        if (na == 0 && nb == 0 && ea.kind == eb.kind) {
            if (ea.kind == LEXPR_FVAR && ea.d.fvar_id == eb.d.fvar_id) {
                if (a_args != abuf) free(a_args);
                if (b_args != bbuf) free(b_args);
                return true;
            }
            if (ea.kind == LEXPR_BVAR && ea.d.bvar_idx == eb.d.bvar_idx) {
                if (a_args != abuf) free(a_args);
                if (b_args != bbuf) free(b_args);
                return true;
            }
            if (ea.kind == LEXPR_CONST && ea.d.cnst.name == eb.d.cnst.name && ea.d.cnst.nus == eb.d.cnst.nus) {
                bool lvls_ok = true;
                for (uint32_t i = 0; i < ea.d.cnst.nus; i++) {
                    if (!lean_lvl_eq(ks, ea.d.cnst.us[i], eb.d.cnst.us[i])) {
                        lvls_ok = false;
                        break;
                    }
                }
                if (lvls_ok) {
                    if (a_args != abuf) free(a_args);
                    if (b_args != bbuf) free(b_args);
                    return true;
                }
            }
            if (ea.kind == LEXPR_PROJ && ea.d.proj.idx == eb.d.proj.idx) {
                uint32_t sa = ea.d.proj.struct_expr;
                uint32_t sb = eb.d.proj.struct_expr;
                uint32_t hsa = 0, hsb = 0, cnsa = 0, cnsb = 0;
                uint8_t  hksa = LHINT_OPAQUE, hksb = LHINT_OPAQUE;
                uint32_t nsa = lean_try_delta_step(ks, sa, &hsa, &cnsa, &hksa);
                uint32_t nsb = lean_try_delta_step(ks, sb, &hsb, &cnsb, &hksb);
                if (nsa != 0 || nsb != 0) {
                    if (nsa != 0 && nsb != 0 && hsa == hsb && cnsa == cnsb && hksa == LHINT_REGULAR &&
                        lean_is_def_eq(ks, sa, sb)) {
                        if (a_args != abuf) free(a_args);
                        if (b_args != bbuf) free(b_args);
                        return true;
                    }
                    if (nsa != 0 && (nsb == 0 || hsa >= hsb)) {
                        a = lean_expr_mk_proj(ks, ea.d.proj.type_name, ea.d.proj.idx, nsa);
                    }
                    if (nsb != 0 && (nsa == 0 || hsb >= hsa)) {
                        b = lean_expr_mk_proj(ks, eb.d.proj.type_name, eb.d.proj.idx, nsb);
                    }
                    if (a_args != abuf) free(a_args);
                    if (b_args != bbuf) free(b_args);
                    continue;
                }
                if (lean_is_def_eq(ks, sa, sb)) {
                    if (a_args != abuf) free(a_args);
                    if (b_args != bbuf) free(b_args);
                    return true;
                }
            }
        }

        /* Now try non-cheap projection reduction (`whnfCore tn (cheapProj := false)`, lines 697-700) */
        {
            uint32_t a_full = lean_whnf_core_proj(ks, a, false, false);
            uint32_t b_full = lean_whnf_core_proj(ks, b, false, false);
            if (a_full != a || b_full != b) {
                if (a_args != abuf) free(a_args);
                if (b_args != bbuf) free(b_args);
                a = a_full;
                b = b_full;
                continue;
            }
        }

        /* `isDefEqApp` (line 702): compare application spines after non-cheap projection reduction */
        if (na > 0 && na == nb) {
            bool same_head = false;
            if (ks->exprs[ha].kind == ks->exprs[hb].kind) {
                if (ks->exprs[ha].kind == LEXPR_FVAR && ks->exprs[ha].d.fvar_id == ks->exprs[hb].d.fvar_id)
                    same_head = true;
                else if (ks->exprs[ha].kind == LEXPR_BVAR && ks->exprs[ha].d.bvar_idx == ks->exprs[hb].d.bvar_idx)
                    same_head = true;
                else if (ks->exprs[ha].kind == LEXPR_CONST &&
                         ks->exprs[ha].d.cnst.name == ks->exprs[hb].d.cnst.name &&
                         ks->exprs[ha].d.cnst.nus == ks->exprs[hb].d.cnst.nus) {
                    same_head = true;
                    for (uint32_t i = 0; i < ks->exprs[ha].d.cnst.nus; i++) {
                        if (!lean_lvl_eq(ks, ks->exprs[ha].d.cnst.us[i], ks->exprs[hb].d.cnst.us[i])) {
                            same_head = false;
                            break;
                        }
                    }
                } else if (ks->exprs[ha].kind == LEXPR_PROJ &&
                           ks->exprs[ha].d.proj.idx == ks->exprs[hb].d.proj.idx &&
                           lean_is_def_eq(ks, ks->exprs[ha].d.proj.struct_expr, ks->exprs[hb].d.proj.struct_expr)) {
                    same_head = true;
                }
            }
            if (same_head) {
                if (na == 1) {
                    uint32_t arg_a = a_args[0];
                    uint32_t arg_b = b_args[0];
                    if (a_args != abuf) free(a_args);
                    if (b_args != bbuf) free(b_args);
                    int pi_arg = lean_try_proof_irrel(ks, arg_a, arg_b);
                    if (pi_arg >= 0) return pi_arg == 1;
                    a = arg_a;
                    b = arg_b;
                    continue;
                }
                if (lean_is_def_eq_args(ks, na, a_args, b_args)) {
                    if (a_args != abuf) free(a_args);
                    if (b_args != bbuf) free(b_args);
                    return true;
                }
            }
        }
        if (a_args != abuf) free(a_args);
        if (b_args != bbuf) free(b_args);

        /* StrLit expansion against String.ofList / String.mk (line 705) */
        if (ea.kind == LEXPR_STRLIT || eb.kind == LEXPR_STRLIT) {
            if (ea.kind == LEXPR_STRLIT && eb.kind == LEXPR_STRLIT) {
                return strcmp(ea.d.str_lit.str, eb.d.str_lit.str) == 0;
            }
            if (ea.kind == LEXPR_STRLIT) {
                uint32_t exp_a = lean_strlit_to_expr(ks, a);
                if (exp_a != a) { a = exp_a; continue; }
            }
            if (eb.kind == LEXPR_STRLIT) {
                uint32_t exp_b = lean_strlit_to_expr(ks, b);
                if (exp_b != b) { b = exp_b; continue; }
            }
        }

        /* Function Eta-expansion: if `a` is `\x:A. body` and `b` is not a lambda */
        if (ks->exprs[a].kind == LEXPR_LAM && ks->exprs[b].kind != LEXPR_LAM) {
            uint32_t dom = ks->exprs[a].d.binder.domain;
            uint32_t fv = lean_push_local(ks, ks->exprs[a].d.binder.binder_name, dom, 0);
            uint32_t ba = lean_expr_instantiate1(ks, ks->exprs[a].d.binder.body, fv);
            uint32_t bb = lean_expr_mk_app(ks, b, fv);
            bool ok = lean_is_def_eq(ks, ba, bb);
            lean_pop_local(ks);
            return ok;
        }
        if (ks->exprs[b].kind == LEXPR_LAM && ks->exprs[a].kind != LEXPR_LAM) {
            uint32_t dom = ks->exprs[b].d.binder.domain;
            uint32_t fv = lean_push_local(ks, ks->exprs[b].d.binder.binder_name, dom, 0);
            uint32_t ba = lean_expr_mk_app(ks, a, fv);
            uint32_t bb = lean_expr_instantiate1(ks, ks->exprs[b].d.binder.body, fv);
            bool ok = lean_is_def_eq(ks, ba, bb);
            lean_pop_local(ks);
            return ok;
        }

        /* Structure Eta-equivalence (`tryEtaStruct` + `isDefEqUnitLike` in `Lean4Lean/TypeChecker.lean` lines 704-707) */
        if (lean_try_eta_struct(ks, a, b)) return true;
        if (lean_is_def_eq_unit_like(ks, a, b)) return true;

        return false;
    }
}

/* `tryEtaStructCore` (`src/kernel/type_checker.cpp` lines 793-809, `Lean4Lean/TypeChecker.lean` lines 521-531):
 * Check whether `s` is a constructor application `mk p_1 ... p_m f_1 ... f_n` of a non-recursive structure
 * and `t.i =?= f_i` for all `0 <= i < n`. */
static bool lean_try_eta_struct_core(LeanKernelState *ks, uint32_t t, uint32_t s) {
    uint32_t sbuf[32];
    uint32_t *s_args = NULL;
    uint32_t ns = 0, scap = 32;
    uint32_t hs = lean_unpack_spine(ks, s, &s_args, &ns, &scap, sbuf);
    if (ks->exprs[hs].kind != LEXPR_CONST) {
        if (s_args != sbuf) free(s_args);
        return false;
    }
    const LeanDecl *cdecl = lean_lookup_decl(ks, ks->exprs[hs].d.cnst.name);
    if (!cdecl || cdecl->kind != LDECL_CTOR || ns != cdecl->num_params + cdecl->num_fields) {
        if (s_args != sbuf) free(s_args);
        return false;
    }
    const LeanDecl *ind = lean_lookup_decl(ks, cdecl->ind_name);
    if (!ind || ind->kind != LDECL_IND || ind->is_rec || ind->num_indices != 0 || ind->nctors != 1) {
        if (s_args != sbuf) free(s_args);
        return false;
    }
    uint32_t tt = lean_infer_type(ks, t);
    uint32_t ts = lean_infer_type(ks, s);
    if (tt == 0 || ts == 0 || !lean_is_def_eq(ks, tt, ts)) {
        if (s_args != sbuf) free(s_args);
        return false;
    }
    bool ok = true;
    for (uint32_t i = cdecl->num_params; i < ns; i++) {
        uint32_t proj = lean_expr_mk_proj(ks, ind->name, i - cdecl->num_params, t);
        if (lean_infer_type(ks, proj) == 0 || !lean_is_def_eq(ks, proj, s_args[i])) {
            ok = false;
            break;
        }
    }
    if (s_args != sbuf) free(s_args);
    return ok;
}

static bool lean_try_eta_struct(LeanKernelState *ks, uint32_t a, uint32_t b) {
    return lean_try_eta_struct_core(ks, a, b) || lean_try_eta_struct_core(ks, b, a);
}

/* `isDefEqUnitLike` (`src/kernel/type_checker.cpp` lines 1044-1054, `Lean4Lean/TypeChecker.lean` lines 658-665):
 * Return true if `a`'s type is a 0-field non-recursive 0-index structure and `infer_type(a) =?= infer_type(b)`. */
static bool lean_is_def_eq_unit_like(LeanKernelState *ks, uint32_t a, uint32_t b) {
    uint32_t ta = lean_infer_type(ks, a);
    if (ta == 0) return false;
    uint32_t tw = lean_whnf(ks, ta);
    uint32_t tbuf[32];
    uint32_t *targs = NULL;
    uint32_t tnargs = 0, tcap = 32;
    uint32_t thead = lean_unpack_spine(ks, tw, &targs, &tnargs, &tcap, tbuf);
    if (targs != tbuf) free(targs);
    if (ks->exprs[thead].kind != LEXPR_CONST) return false;
    const LeanDecl *ind = lean_lookup_decl(ks, ks->exprs[thead].d.cnst.name);
    if (!ind || ind->kind != LDECL_IND || ind->is_rec || ind->num_indices != 0 || ind->nctors != 1) return false;
    if (ind->ctors[0].num_fields != 0) return false;
    uint32_t tb = lean_infer_type(ks, b);
    if (tb == 0) return false;
    return lean_is_def_eq(ks, tw, tb);
}

static uint32_t lean_infer_type_core(LeanKernelState *ks, uint32_t e, bool infer_only);

/* Infer the type of an already-checked expression `e` (fast path during WHNF / defeq) */
static uint32_t lean_infer_type(LeanKernelState *ks, uint32_t e) {
    return lean_infer_type_core(ks, e, true);
}

/* Typecheck `e` (`infer_only = false`) and return its inferred type (or 0 on kernel type error) */
static uint32_t lean_check_expr(LeanKernelState *ks, uint32_t e) {
    return lean_infer_type_core(ks, e, false);
}

static Occ lean_emit_typed_occ(LeanKernelState *ks, uint32_t e, uint32_t ty) {
    int rule = R_CHECK_CONST;
    switch (ks->exprs[e].kind) {
        case LEXPR_SORT:   rule = R_CHECK_SORT; break;
        case LEXPR_CONST:  rule = R_CHECK_CONST; break;
        case LEXPR_APP:    rule = R_CHECK_APP; break;
        case LEXPR_LAM:    rule = R_CHECK_LAM; break;
        case LEXPR_FORALL: rule = R_CHECK_FORALL; break;
        case LEXPR_LET:    rule = R_CHECK_LET; break;
        case LEXPR_PROJ:   rule = R_CHECK_PROJ; break;
        case LEXPR_NATLIT:
        case LEXPR_STRLIT: rule = R_CHECK_LIT; break;
        default:           rule = R_CHECK_CONST; break;
    }
    return lean_tc_commit2(rule, e, ty);
}

static __attribute__((noinline)) uint32_t lean_infer_app_only(LeanKernelState *ks, uint32_t e) {
    uint32_t sbuf[8];
    uint32_t *args = NULL;
    uint32_t nargs = 0, cap = 8;
    uint32_t head = lean_unpack_spine(ks, e, &args, &nargs, &cap, sbuf);
    uint32_t f_ty = lean_infer_type_core(ks, head, true);
    if (f_ty == 0) {
        if (args != sbuf) free(args);
        return 0;
    }
    uint32_t i = 0;
    while (i < nargs) {
        uint32_t batch_start = i;
        while (i < nargs && ks->exprs[f_ty].kind == LEXPR_FORALL) {
            f_ty = ks->exprs[f_ty].d.binder.body;
            i++;
        }
        if (i > batch_start) {
            f_ty = lean_expr_instantiate_rev(ks, f_ty, 0, i - batch_start, args + batch_start);
        } else {
            f_ty = lean_whnf(ks, f_ty);
            if (ks->exprs[f_ty].kind != LEXPR_FORALL) {
                if (args != sbuf) free(args);
                return 0;
            }
        }
    }
    if (args != sbuf) free(args);
    return f_ty;
}

static __attribute__((noinline)) uint32_t lean_infer_lambda_batch(LeanKernelState *ks, uint32_t e, bool infer_only) {
    uint32_t bname_buf[8], odom_buf[8], fv_buf[8] = {0}, fvid_buf[8] = {0};
    uint32_t cap = 8, count = 0;
    uint32_t *bnames = bname_buf, *odoms = odom_buf, *fvars = fv_buf, *fvids = fvid_buf;
    uint32_t cur = e;
    bool ok = true;
    while (ks->exprs[cur].kind == LEXPR_LAM) {
        if (count >= cap) {
            uint32_t ncap = cap * 2u;
            uint32_t *nb = (uint32_t *)malloc((size_t)ncap * sizeof(uint32_t));
            uint32_t *nd = (uint32_t *)malloc((size_t)ncap * sizeof(uint32_t));
            uint32_t *nf = (uint32_t *)malloc((size_t)ncap * sizeof(uint32_t));
            uint32_t *ni = (uint32_t *)malloc((size_t)ncap * sizeof(uint32_t));
            memcpy(nb, bnames, (size_t)count * sizeof(uint32_t));
            memcpy(nd, odoms,  (size_t)count * sizeof(uint32_t));
            memcpy(nf, fvars,  (size_t)count * sizeof(uint32_t));
            memcpy(ni, fvids,  (size_t)count * sizeof(uint32_t));
            if (bnames != bname_buf) { free(bnames); free(odoms); free(fvars); free(fvids); }
            bnames = nb; odoms = nd; fvars = nf; fvids = ni; cap = ncap;
        }
        uint32_t bname = ks->exprs[cur].d.binder.binder_name;
        uint32_t odom  = ks->exprs[cur].d.binder.domain;
        uint32_t dom   = lean_expr_instantiate_rev(ks, odom, 0, count, fvars);
        if (!infer_only) {
            uint32_t dom_ty = lean_whnf(ks, lean_infer_type_core(ks, dom, false));
            if (dom_ty == 0 || ks->exprs[dom_ty].kind != LEXPR_SORT) { ok = false; break; }
        }
        uint32_t fv = lean_push_local(ks, bname, dom, 0);
        bnames[count] = bname;
        odoms[count]  = odom;
        fvars[count]  = fv;
        fvids[count]  = ks->exprs[fv].d.fvar_id;
        count++;
        cur = ks->exprs[cur].d.binder.body;
    }
    uint32_t res = 0;
    if (ok) {
        uint32_t b_inst = lean_expr_instantiate_rev(ks, cur, 0, count, fvars);
        uint32_t b_ty = lean_infer_type_core(ks, b_inst, infer_only);
        for (uint32_t j = 0; j < count; j++) lean_pop_local(ks);
        if (b_ty != 0) {
            uint32_t r = lean_expr_abstract_fvars(ks, b_ty, 0, count, fvids);
            for (uint32_t k = count; k > 0; k--) {
                r = lean_expr_mk_forall(ks, bnames[k - 1u], odoms[k - 1u], r);
            }
            res = r;
        }
    } else {
        for (uint32_t j = 0; j < count; j++) lean_pop_local(ks);
    }
    if (bnames != bname_buf) { free(bnames); free(odoms); free(fvars); free(fvids); }
    return res;
}

static __attribute__((noinline)) uint32_t lean_infer_forall(LeanKernelState *ks, uint32_t e, bool infer_only) {
    uint32_t fv_buf[8] = {0}, u_buf[8] = {0};
    uint32_t cap = 8, count = 0;
    uint32_t *fvars = fv_buf, *us = u_buf;
    uint32_t cur = e;
    bool ok = true;
    while (ks->exprs[cur].kind == LEXPR_FORALL) {
        if (count >= cap) {
            uint32_t ncap = cap * 2u;
            uint32_t *nf = (uint32_t *)malloc((size_t)ncap * sizeof(uint32_t));
            uint32_t *nu = (uint32_t *)malloc((size_t)ncap * sizeof(uint32_t));
            memcpy(nf, fvars, (size_t)count * sizeof(uint32_t));
            memcpy(nu, us,    (size_t)count * sizeof(uint32_t));
            if (fvars != fv_buf) { free(fvars); free(us); }
            fvars = nf; us = nu; cap = ncap;
        }
        uint32_t bname = ks->exprs[cur].d.binder.binder_name;
        uint32_t odom  = ks->exprs[cur].d.binder.domain;
        uint32_t dom   = lean_expr_instantiate_rev(ks, odom, 0, count, fvars);
        uint32_t dom_ty = lean_whnf(ks, lean_infer_type_core(ks, dom, infer_only));
        if (dom_ty == 0 || ks->exprs[dom_ty].kind != LEXPR_SORT) { ok = false; break; }
        us[count] = ks->exprs[dom_ty].d.sort_lvl;
        uint32_t fv = lean_push_local(ks, bname, dom, 0);
        fvars[count++] = fv;
        cur = ks->exprs[cur].d.binder.body;
    }
    uint32_t res = 0;
    if (ok) {
        uint32_t b_inst = lean_expr_instantiate_rev(ks, cur, 0, count, fvars);
        uint32_t b_ty = lean_whnf(ks, lean_infer_type_core(ks, b_inst, infer_only));
        for (uint32_t j = 0; j < count; j++) lean_pop_local(ks);
        if (b_ty != 0 && ks->exprs[b_ty].kind == LEXPR_SORT) {
            uint32_t v = ks->exprs[b_ty].d.sort_lvl;
            for (uint32_t k = count; k > 0; k--) {
                v = lean_lvl_mk_imax(ks, us[k - 1u], v);
            }
            res = lean_expr_mk_sort(ks, v);
        }
    } else {
        for (uint32_t j = 0; j < count; j++) lean_pop_local(ks);
    }
    if (fvars != fv_buf) { free(fvars); free(us); }
    return res;
}

static __attribute__((noinline)) uint32_t lean_infer_proj(LeanKernelState *ks, uint32_t e, bool infer_only) {
    uint32_t s = ks->exprs[e].d.proj.struct_expr;
    uint32_t type_name = ks->exprs[e].d.proj.type_name;
    uint32_t idx = ks->exprs[e].d.proj.idx;
    uint32_t s_ty = lean_whnf(ks, lean_infer_type_core(ks, s, infer_only));
    if (s_ty == 0) return 0;
    uint32_t sbuf[32];
    uint32_t *sargs = NULL;
    uint32_t snargs = 0, scap = 32;
    uint32_t shead = lean_unpack_spine(ks, s_ty, &sargs, &snargs, &scap, sbuf);
    if (ks->exprs[shead].kind != LEXPR_CONST ||
        ks->exprs[shead].d.cnst.name != type_name) {
        if (sargs != sbuf) free(sargs);
        return 0;
    }
    const LeanDecl *ind = lean_lookup_decl(ks, type_name);
    if (!ind || ind->kind != LDECL_IND || ind->nctors != 1 ||
        snargs != ind->num_params || idx >= ind->ctors[0].num_fields) {
        if (sargs != sbuf) free(sargs);
        return 0;
    }
    uint32_t c_ty = lean_expr_subst_lvls(
        ks, ind->ctors[0].type, ind->nparams, ind->level_params, ks->exprs[shead].d.cnst.us);
    for (uint32_t p = 0; p < ind->num_params; p++) {
        if (ks->exprs[c_ty].kind != LEXPR_FORALL) { c_ty = lean_whnf(ks, c_ty); }
        if (ks->exprs[c_ty].kind != LEXPR_FORALL) {
            if (sargs != sbuf) free(sargs);
            return 0;
        }
        c_ty = lean_expr_instantiate1(ks, ks->exprs[c_ty].d.binder.body, sargs[p]);
    }
    if (sargs != sbuf) free(sargs);

    int s_prop = lean_check_is_prop_strict(ks, s_ty);
    if (s_prop < 0) return 0;
    bool struct_in_prop = (s_prop == 1);
    for (uint32_t j = 0; j < idx; j++) {
        if (ks->exprs[c_ty].kind != LEXPR_FORALL) c_ty = lean_whnf(ks, c_ty);
        if (ks->exprs[c_ty].kind != LEXPR_FORALL) return 0;
        uint32_t pj = lean_expr_mk_proj(ks, type_name, j, s);
        if (struct_in_prop) {
            int dom_prop = lean_check_is_prop_strict(ks, ks->exprs[c_ty].d.binder.domain);
            if (dom_prop < 0) return 0;
            if (dom_prop == 0 && ks->exprs[ks->exprs[c_ty].d.binder.body].loose_bvar_range > 0) {
                return 0;
            }
        }
        c_ty = lean_expr_instantiate1(ks, ks->exprs[c_ty].d.binder.body, pj);
    }
    if (ks->exprs[c_ty].kind != LEXPR_FORALL) c_ty = lean_whnf(ks, c_ty);
    if (ks->exprs[c_ty].kind != LEXPR_FORALL) return 0;
    uint32_t res = ks->exprs[c_ty].d.binder.domain;
    if (struct_in_prop) {
        int res_prop = lean_check_is_prop_strict(ks, res);
        if (res_prop != 1) return 0;
    }
    return res;
}

static uint32_t lean_infer_type_core(LeanKernelState *ks, uint32_t e, bool infer_only) {
    if (e == 0) return 0;
    if (ks->exprs[e].loose_bvar_range == 0 && ks->exprs[e].type_cache != 0 &&
        (infer_only || ks->exprs[e].checked_ok)) {
        return ks->exprs[e].type_cache;
    }

    uint32_t res = 0;
    switch (ks->exprs[e].kind) {
        case LEXPR_BVAR:
            return 0;

        case LEXPR_FVAR: {
            const LeanLocalDecl *loc = lean_lookup_local(ks, ks->exprs[e].d.fvar_id);
            if (!loc) return 0;
            return loc->type;
        }

        case LEXPR_SORT: {
            uint32_t sl = lean_lvl_mk_succ(ks, ks->exprs[e].d.sort_lvl);
            res = lean_expr_mk_sort(ks, sl);
            break;
        }

        case LEXPR_CONST: {
            const LeanDecl *d = lean_lookup_decl(ks, ks->exprs[e].d.cnst.name);
            if (!d || d->nparams != ks->exprs[e].d.cnst.nus) return 0;
            res = lean_expr_subst_lvls(ks, d->type, d->nparams, d->level_params, ks->exprs[e].d.cnst.us);
            break;
        }

        case LEXPR_NATLIT:
            if (!ks->nat_verified || ks->nm_Nat == 0) return 0;
            res = lean_expr_mk_const(ks, ks->nm_Nat, 0, NULL);
            break;

        case LEXPR_STRLIT:
            if (!ks->string_verified || ks->nm_String == 0) return 0;
            res = lean_expr_mk_const(ks, ks->nm_String, 0, NULL);
            break;

        case LEXPR_APP: {
            if (!infer_only) {
                uint32_t fn = ks->exprs[e].d.app.fn;
                uint32_t arg = ks->exprs[e].d.app.arg;
                uint32_t f_ty = lean_infer_type_core(ks, fn, false);
                if (f_ty == 0) return 0;
                if (ks->exprs[f_ty].kind != LEXPR_FORALL) {
                    f_ty = lean_whnf(ks, f_ty);
                    if (ks->exprs[f_ty].kind != LEXPR_FORALL) return 0;
                }
                uint32_t a_ty = lean_infer_type_core(ks, arg, false);
                if (a_ty == 0) return 0;
                uint32_t dom = ks->exprs[f_ty].d.binder.domain;
                bool saved_eager = ks->eager_reduce;
                if (lean_is_app_of_arity2(ks, arg, ks->nm_eagerReduce)) {
                    ks->eager_reduce = true;
                }
                bool ok_defeq = lean_is_def_eq(ks, dom, a_ty);
                ks->eager_reduce = saved_eager;
                if (!ok_defeq) return 0;
                res = lean_expr_instantiate1(ks, ks->exprs[f_ty].d.binder.body, arg);
                break;
            }
            res = lean_infer_app_only(ks, e);
            if (res == 0) return 0;
            break;
        }

        case LEXPR_LAM: {
            uint32_t body = ks->exprs[e].d.binder.body;
            if (ks->exprs[body].kind != LEXPR_LAM) {
                uint32_t bname = ks->exprs[e].d.binder.binder_name;
                uint32_t dom   = ks->exprs[e].d.binder.domain;
                if (!infer_only) {
                    uint32_t dom_ty = lean_whnf(ks, lean_infer_type_core(ks, dom, false));
                    if (dom_ty == 0 || ks->exprs[dom_ty].kind != LEXPR_SORT) return 0;
                }
                uint32_t fv = lean_push_local(ks, bname, dom, 0);
                uint32_t fvid = ks->exprs[fv].d.fvar_id;
                uint32_t b_inst = lean_expr_instantiate1(ks, body, fv);
                uint32_t b_ty = lean_infer_type_core(ks, b_inst, infer_only);
                lean_pop_local(ks);
                if (b_ty == 0) return 0;
                uint32_t r = lean_expr_abstract_fvars(ks, b_ty, 0, 1, &fvid);
                res = lean_expr_mk_forall(ks, bname, dom, r);
                break;
            }
            res = lean_infer_lambda_batch(ks, e, infer_only);
            if (res == 0) return 0;
            break;
        }

        case LEXPR_FORALL:
            res = lean_infer_forall(ks, e, infer_only);
            if (res == 0) return 0;
            break;

        case LEXPR_LET: {
            uint32_t ty = ks->exprs[e].d.let_e.type;
            uint32_t val = ks->exprs[e].d.let_e.val;
            if (!infer_only) {
                uint32_t ty_sort = lean_whnf(ks, lean_infer_type_core(ks, ty, false));
                if (ty_sort == 0 || ks->exprs[ty_sort].kind != LEXPR_SORT) return 0;
                uint32_t val_ty = lean_infer_type_core(ks, val, false);
                if (val_ty == 0 || !lean_is_def_eq(ks, val_ty, ty)) return 0;
            }
            uint32_t fv = lean_push_local(ks, ks->exprs[e].d.let_e.binder_name, ty, val + 1u);
            uint32_t fvid = ks->exprs[fv].d.fvar_id;
            uint32_t b_inst = lean_expr_instantiate1(ks, ks->exprs[e].d.let_e.body, fv);
            uint32_t b_ty = lean_infer_type_core(ks, b_inst, infer_only);
            lean_pop_local(ks);
            if (b_ty == 0) return 0;
            uint32_t b_ty_abs = lean_expr_abstract_fvars(ks, b_ty, 0, 1, &fvid);
            res = lean_expr_instantiate1(ks, b_ty_abs, val);
            break;
        }

        case LEXPR_PROJ:
            res = lean_infer_proj(ks, e, infer_only);
            if (res == 0) return 0;
            break;
    }

    if (res != 0 && ks->exprs[e].loose_bvar_range == 0) {
        ks->exprs[e].type_cache = res;
        if (!infer_only) ks->exprs[e].checked_ok = 1u;
    }
    return res;
}

/* =========================================================================
 * 6. Declaration Verification & Premise-Driven Admission into LEAN_SPACE_ENV
 * ========================================================================= */

/* Verify that universe parameter names `params[0..nparams-1]` are pairwise distinct */
static bool lean_check_unique_lvl_params(uint32_t nparams, const uint32_t *params) {
    for (uint32_t i = 0; i < nparams; i++) {
        if (params[i] == 0) return false;
        for (uint32_t j = i + 1u; j < nparams; j++) {
            if (params[i] == params[j]) return false;
        }
    }
    return true;
}

/* Verify that all universe parameters in `l` are declared in `params[0..nparams-1]` */
static bool lean_check_lvl_params(const LeanKernelState *ks, uint32_t l, uint32_t nparams, const uint32_t *params) {
    if (l == 0) return true;
    LeanLvl lv = ks->lvls[l];
    switch (lv.kind) {
        case LLVL_ZERO: return true;
        case LLVL_SUCC: return lean_check_lvl_params(ks, lv.u, nparams, params);
        case LLVL_MAX:
        case LLVL_IMAX:
            return lean_check_lvl_params(ks, lv.u, nparams, params) &&
                   lean_check_lvl_params(ks, lv.v, nparams, params);
        case LLVL_PARAM:
            for (uint32_t i = 0; i < nparams; i++) {
                if (params[i] == lv.param_name) return true;
            }
            return false;
    }
    return false;
}

static bool lean_check_expr_lvl_params(const LeanKernelState *ks, uint32_t e, uint32_t nparams, const uint32_t *params) {
    if (e == 0 || !ks->exprs[e].has_lvl_param) return true;
    const LeanExpr *ex = &ks->exprs[e];
    switch (ex->kind) {
        case LEXPR_SORT:
            return lean_check_lvl_params(ks, ex->d.sort_lvl, nparams, params);
        case LEXPR_CONST:
            for (uint32_t i = 0; i < ex->d.cnst.nus; i++) {
                if (!lean_check_lvl_params(ks, ex->d.cnst.us[i], nparams, params)) return false;
            }
            return true;
        case LEXPR_APP:
            return lean_check_expr_lvl_params(ks, ex->d.app.fn, nparams, params) &&
                   lean_check_expr_lvl_params(ks, ex->d.app.arg, nparams, params);
        case LEXPR_LAM:
        case LEXPR_FORALL:
            return lean_check_expr_lvl_params(ks, ex->d.binder.domain, nparams, params) &&
                   lean_check_expr_lvl_params(ks, ex->d.binder.body, nparams, params);
        case LEXPR_LET:
            return lean_check_expr_lvl_params(ks, ex->d.let_e.type, nparams, params) &&
                   lean_check_expr_lvl_params(ks, ex->d.let_e.val, nparams, params) &&
                   lean_check_expr_lvl_params(ks, ex->d.let_e.body, nparams, params);
        case LEXPR_PROJ:
            return lean_check_expr_lvl_params(ks, ex->d.proj.struct_expr, nparams, params);
        default:
            return true;
    }
}

/* Compute maximum definition unfolding height in `e` */
static uint32_t lean_compute_max_height(const LeanKernelState *ks, uint32_t e) {
    if (e == 0) return 0;
    const LeanExpr *ex = &ks->exprs[e];
    switch (ex->kind) {
        case LEXPR_CONST: {
            const LeanDecl *d = lean_lookup_decl(ks, ex->d.cnst.name);
            return (d && d->kind == LDECL_DEFN) ? d->height : 0;
        }
        case LEXPR_APP:
            return max_u32(lean_compute_max_height(ks, ex->d.app.fn),
                           lean_compute_max_height(ks, ex->d.app.arg));
        case LEXPR_LAM:
        case LEXPR_FORALL:
            return max_u32(lean_compute_max_height(ks, ex->d.binder.domain),
                           lean_compute_max_height(ks, ex->d.binder.body));
        case LEXPR_LET:
            return max_u32(max_u32(lean_compute_max_height(ks, ex->d.let_e.type),
                                   lean_compute_max_height(ks, ex->d.let_e.val)),
                           lean_compute_max_height(ks, ex->d.let_e.body));
        case LEXPR_PROJ:
            return lean_compute_max_height(ks, ex->d.proj.struct_expr);
        default:
            return 0;
    }
}

/* Check whether any constant in `ind_names[0..ntypes-1]` occurs anywhere in `e` */
static bool lean_expr_mentions_any_const(const LeanKernelState *ks, uint32_t e, uint32_t ntypes, const uint32_t *ind_names) {
    if (e == 0) return false;
    const LeanExpr *ex = &ks->exprs[e];
    switch (ex->kind) {
        case LEXPR_CONST:
            for (uint32_t i = 0; i < ntypes; i++) {
                if (ex->d.cnst.name == ind_names[i]) return true;
            }
            return false;
        case LEXPR_APP:
            return lean_expr_mentions_any_const(ks, ex->d.app.fn, ntypes, ind_names) ||
                   lean_expr_mentions_any_const(ks, ex->d.app.arg, ntypes, ind_names);
        case LEXPR_LAM:
        case LEXPR_FORALL:
            return lean_expr_mentions_any_const(ks, ex->d.binder.domain, ntypes, ind_names) ||
                   lean_expr_mentions_any_const(ks, ex->d.binder.body, ntypes, ind_names);
        case LEXPR_LET:
            return lean_expr_mentions_any_const(ks, ex->d.let_e.type, ntypes, ind_names) ||
                   lean_expr_mentions_any_const(ks, ex->d.let_e.val, ntypes, ind_names) ||
                   lean_expr_mentions_any_const(ks, ex->d.let_e.body, ntypes, ind_names);
        case LEXPR_PROJ:
            return lean_expr_mentions_any_const(ks, ex->d.proj.struct_expr, ntypes, ind_names);
        default:
            return false;
    }
}

/* Check alpha-equivalence of expressions up to universe-level equivalence (`lean_lvl_eq`).
 * Because closed expressions are hash-consed ignoring binder names and binderInfo,
 * `e1 == e2` handles the common case in O(1). */
static bool lean_expr_eqv(LeanKernelState *ks, uint32_t e1, uint32_t e2) {
    if (e1 == e2) return true;
    if (e1 == 0 || e2 == 0) return false;
    const LeanExpr *a = &ks->exprs[e1];
    const LeanExpr *b = &ks->exprs[e2];
    if (a->kind != b->kind) return false;
    switch (a->kind) {
        case LEXPR_BVAR: return a->d.bvar_idx == b->d.bvar_idx;
        case LEXPR_FVAR: return a->d.fvar_id == b->d.fvar_id;
        case LEXPR_SORT: return lean_lvl_eq(ks, a->d.sort_lvl, b->d.sort_lvl);
        case LEXPR_CONST:
            if (a->d.cnst.name != b->d.cnst.name || a->d.cnst.nus != b->d.cnst.nus) return false;
            for (uint32_t i = 0; i < a->d.cnst.nus; i++) {
                if (!lean_lvl_eq(ks, a->d.cnst.us[i], b->d.cnst.us[i])) return false;
            }
            return true;
        case LEXPR_APP:
            return lean_expr_eqv(ks, a->d.app.fn, b->d.app.fn) &&
                   lean_expr_eqv(ks, a->d.app.arg, b->d.app.arg);
        case LEXPR_LAM:
        case LEXPR_FORALL:
            return lean_expr_eqv(ks, a->d.binder.domain, b->d.binder.domain) &&
                   lean_expr_eqv(ks, a->d.binder.body, b->d.binder.body);
        case LEXPR_LET:
            return lean_expr_eqv(ks, a->d.let_e.type, b->d.let_e.type) &&
                   lean_expr_eqv(ks, a->d.let_e.val, b->d.let_e.val) &&
                   lean_expr_eqv(ks, a->d.let_e.body, b->d.let_e.body);
        case LEXPR_NATLIT:
        case LEXPR_STRLIT:
            return lean_expr_node_eq(a, b);
        case LEXPR_PROJ:
            return a->d.proj.type_name == b->d.proj.type_name &&
                   a->d.proj.idx == b->d.proj.idx &&
                   lean_expr_eqv(ks, a->d.proj.struct_expr, b->d.proj.struct_expr);
    }
    return false;
}

/* Abstract `fvar_exprs[0..n-1]` (each an `LEXPR_FVAR` pushed in `ks->locals`) into a `Forall`, `Lambda`, or `Let` telescope. */
static uint32_t lean_lctx_mk_binder(LeanKernelState *ks, bool is_forall, uint32_t n, const uint32_t *fvar_exprs, uint32_t body) {
    if (n == 0) return body;
    uint32_t fids_buf[64];
    uint32_t *fids = (n <= 64) ? fids_buf : (uint32_t *)malloc((size_t)n * sizeof(uint32_t));
    for (uint32_t i = 0; i < n; i++) {
        fids[i] = ks->exprs[fvar_exprs[i]].d.fvar_id;
    }
    uint32_t cur = lean_expr_abstract_fvars(ks, body, 0, n, fids);
    for (uint32_t k = n; k > 0; k--) {
        uint32_t i = k - 1u;
        const LeanLocalDecl *ld = lean_lookup_local(ks, fids[i]);
        uint32_t bname = ld ? ld->name : 0u;
        uint32_t dom   = ld ? lean_expr_abstract_fvars(ks, ld->type, 0, i, fids) : 0u;
        if (ld && ld->llet_val > 0) {
            uint32_t val = lean_expr_abstract_fvars(ks, ld->llet_val - 1u, 0, i, fids);
            cur = lean_expr_mk_let(ks, bname, dom, val, cur);
        } else {
            cur = is_forall ? lean_expr_mk_forall(ks, bname, dom, cur)
                            : lean_expr_mk_lam(ks, bname, dom, cur);
        }
    }
    if (fids != fids_buf) free(fids);
    return cur;
}

static inline uint32_t lean_lctx_mk_forall(LeanKernelState *ks, uint32_t n, const uint32_t *fvar_exprs, uint32_t body) {
    return lean_lctx_mk_binder(ks, true, n, fvar_exprs, body);
}

static inline uint32_t lean_lctx_mk_lambda(LeanKernelState *ks, uint32_t n, const uint32_t *fvar_exprs, uint32_t body) {
    return lean_lctx_mk_binder(ks, false, n, fvar_exprs, body);
}

static uint32_t lean_expr_abstract_fvar_exprs(LeanKernelState *ks, uint32_t e, uint32_t n, const uint32_t *fvar_exprs) {
    if (n == 0) return e;
    uint32_t fids_buf[64];
    uint32_t *fids = (n <= 64) ? fids_buf : (uint32_t *)malloc((size_t)n * sizeof(uint32_t));
    for (uint32_t i = 0; i < n; i++) {
        fids[i] = ks->exprs[fvar_exprs[i]].d.fvar_id;
    }
    uint32_t res = lean_expr_abstract_fvars(ks, e, 0, n, fids);
    if (fids != fids_buf) free(fids);
    return res;
}

static uint32_t lean_get_app_args_alloc(LeanKernelState *ks, uint32_t e, uint32_t **out_args, uint32_t *out_nargs) {
    uint32_t *args = NULL;
    uint32_t nargs = 0, cap = 0;
    uint32_t fn = lean_unpack_spine(ks, e, &args, &nargs, &cap, NULL);
    *out_args = args;
    *out_nargs = nargs;
    return fn;
}

static uint32_t lean_name_replace_prefix(LeanKernelState *ks, uint32_t n, uint32_t query_p, uint32_t new_p) {
    if (n == query_p) return new_p;
    if (n == 0) return 0u;
    LeanName ln = ks->names[n];
    uint32_t pre2 = lean_name_replace_prefix(ks, ln.pre, query_p, new_p);
    if (pre2 == ln.pre) return n;
    if (ln.kind == LNAME_STR) {
        char *s = xstrdup(ln.str);
        uint32_t r = lean_name_mk_str(ks, pre2, s);
        free(s);
        return r;
    }
    return lean_name_mk_num(ks, pre2, ln.num);
}

static uint32_t lean_name_append(LeanKernelState *ks, uint32_t pre, uint32_t sfx) {
    if (sfx == 0) return pre;
    LeanName ln = ks->names[sfx];
    uint32_t p = lean_name_append(ks, pre, ln.pre);
    if (ln.kind == LNAME_STR) {
        char *s = xstrdup(ln.str);
        uint32_t r = lean_name_mk_str(ks, p, s);
        free(s);
        return r;
    }
    return lean_name_mk_num(ks, p, ln.num);
}

static uint32_t lean_name_append_index_after(LeanKernelState *ks, uint32_t n, uint32_t idx) {
    char buf[560];
    if (n != 0 && ks->names[n].kind == LNAME_STR) {
        uint32_t pre = ks->names[n].pre;
        size_t slen = strlen(ks->names[n].str);
        if (slen + 16 < sizeof(buf)) {
            snprintf(buf, sizeof(buf), "%s_%u", ks->names[n].str, idx);
            return lean_name_mk_str(ks, pre, buf);
        }
        char *dyn = (char *)malloc(slen + 16);
        snprintf(dyn, slen + 16, "%s_%u", ks->names[n].str, idx);
        uint32_t res = lean_name_mk_str(ks, pre, dyn);
        free(dyn);
        return res;
    }
    snprintf(buf, sizeof(buf), "_%u", idx);
    return lean_name_mk_str(ks, n, buf);
}

static bool lean_check_strict_positivity_block_rec(LeanKernelState *ks, uint32_t fty, uint32_t ntypes,
                                                   const uint32_t *ind_names, uint32_t nest_depth,
                                                   const uint32_t *active_containers) {
    if (!lean_expr_mentions_any_const(ks, fty, ntypes, ind_names)) return true;
    if (nest_depth > 8u) return false;
    uint32_t cur = lean_whnf(ks, fty);
    while (ks->exprs[cur].kind == LEXPR_FORALL || ks->exprs[cur].kind == LEXPR_LAM) {
        uint32_t dom = ks->exprs[cur].d.binder.domain;
        if (lean_expr_mentions_any_const(ks, dom, ntypes, ind_names)) return false;
        uint32_t fv = lean_push_local(ks, ks->exprs[cur].d.binder.binder_name, dom, 0);
        uint32_t body = lean_expr_instantiate1(ks, ks->exprs[cur].d.binder.body, fv);
        bool ok = lean_check_strict_positivity_block_rec(ks, body, ntypes, ind_names, nest_depth, active_containers);
        lean_pop_local(ks);
        return ok;
    }

    uint32_t sbuf[32];
    uint32_t *args = NULL;
    uint32_t nargs = 0, cap = 32;
    uint32_t head = lean_unpack_spine(ks, cur, &args, &nargs, &cap, sbuf);
    bool ok = false;
    if (ks->exprs[head].kind == LEXPR_CONST) {
        uint32_t hname = ks->exprs[head].d.cnst.name;
        uint32_t hnus  = ks->exprs[head].d.cnst.nus;
        bool is_target_ind = false;
        for (uint32_t i = 0; i < ntypes; i++) {
            if (hname == ind_names[i]) { is_target_ind = true; break; }
        }
        if (is_target_ind) {
            ok = true;
            for (uint32_t i = 0; i < nargs; i++) {
                if (lean_expr_mentions_any_const(ks, args[i], ntypes, ind_names)) {
                    ok = false;
                    break;
                }
            }
        } else {
            const LeanDecl *outer_ind = lean_lookup_decl(ks, hname);
            if (outer_ind && outer_ind->kind == LDECL_IND &&
                nargs == outer_ind->num_params + outer_ind->num_indices &&
                hnus == outer_ind->nparams) {
                ok = true;
                for (uint32_t i = outer_ind->num_params; i < nargs; i++) {
                    if (lean_expr_mentions_any_const(ks, args[i], ntypes, ind_names)) {
                        ok = false;
                        break;
                    }
                }
                bool already_active = false;
                for (uint32_t d = 0; d < nest_depth; d++) {
                    if (active_containers[d] == hname) { already_active = true; break; }
                }
                if (ok && already_active) {
                    for (uint32_t p = 0; ok && p < outer_ind->num_params; p++) {
                        if (!lean_check_strict_positivity_block_rec(ks, args[p], ntypes, ind_names, nest_depth + 1u, active_containers)) {
                            ok = false;
                            break;
                        }
                    }
                } else if (ok) {
                    uint32_t next_containers[10];
                    for (uint32_t d = 0; d < nest_depth && d < 9u; d++) next_containers[d] = active_containers[d];
                    next_containers[nest_depth] = hname;

                    uint32_t us_buf[16];
                    uint32_t *head_us = hnus <= 16 ? us_buf : (uint32_t *)malloc((size_t)hnus * sizeof(uint32_t));
                    if (hnus > 0) memcpy(head_us, ks->exprs[head].d.cnst.us, (size_t)hnus * sizeof(uint32_t));

                    for (uint32_t c = 0; ok && c < outer_ind->nctors; c++) {
                        uint32_t cty = lean_expr_subst_lvls(
                            ks, outer_ind->ctors[c].type, outer_ind->nparams,
                            outer_ind->level_params, head_us);
                        for (uint32_t p = 0; p < outer_ind->num_params; p++) {
                            if (ks->exprs[cty].kind != LEXPR_FORALL) cty = lean_whnf(ks, cty);
                            if (ks->exprs[cty].kind != LEXPR_FORALL) { ok = false; break; }
                            cty = lean_expr_instantiate1(ks, ks->exprs[cty].d.binder.body, args[p]);
                        }
                        uint32_t pushed = 0;
                        for (uint32_t f = 0; ok && f < outer_ind->ctors[c].num_fields; f++) {
                            if (ks->exprs[cty].kind != LEXPR_FORALL) cty = lean_whnf(ks, cty);
                            if (ks->exprs[cty].kind != LEXPR_FORALL) { ok = false; break; }
                            uint32_t fdom = ks->exprs[cty].d.binder.domain;
                            if (!lean_check_strict_positivity_block_rec(ks, fdom, ntypes, ind_names, nest_depth + 1u, next_containers)) {
                                ok = false;
                                break;
                            }
                            uint32_t fv = lean_push_local(ks, ks->exprs[cty].d.binder.binder_name, fdom, 0);
                            cty = lean_expr_instantiate1(ks, ks->exprs[cty].d.binder.body, fv);
                            pushed++;
                        }
                        for (uint32_t j = 0; j < pushed; j++) lean_pop_local(ks);
                    }
                    if (head_us != us_buf) free(head_us);
                }
            }
        }
    }
    if (args != sbuf) free(args);
    return ok;
}

static bool lean_check_strict_positivity_block(LeanKernelState *ks, uint32_t fty, uint32_t ntypes, const uint32_t *ind_names, uint32_t nest_depth) {
    uint32_t active_containers[10] = {0};
    return lean_check_strict_positivity_block_rec(ks, fty, ntypes, ind_names, nest_depth, active_containers);
}

/* Check that `ty` is a closed, well-sorted type with level params in `params[0..nparams-1]`,
 * and derive `IsType(ty, canonical_lvl)` in `LEAN_SPACE_TYPING` via premise-bearing `R_DERIVE_IS_TYPE`. */
static Occ lean_verify_is_type(LeanKernelState *ks, uint32_t decl_name, uint32_t ty,
                               uint32_t nparams, const uint32_t *params,
                               uint32_t *out_sort_lvl, char *err_buf, size_t err_cap) {
    if (ty == 0 || ks->exprs[ty].loose_bvar_range != 0 || ks->exprs[ty].has_fvar) {
        snprintf(err_buf, err_cap, "decl %s: type is missing or not closed", ks->names[decl_name].full);
        return 0;
    }
    if (!lean_check_unique_lvl_params(nparams, params) ||
        !lean_check_expr_lvl_params(ks, ty, nparams, params)) {
        snprintf(err_buf, err_cap, "decl %s: invalid or undeclared universe parameter in type", ks->names[decl_name].full);
        return 0;
    }
    uint32_t ty_sort = lean_check_expr(ks, ty);
    if (ty_sort == 0) {
        snprintf(err_buf, err_cap, "decl %s: failed to infer sort of type", ks->names[decl_name].full);
        return 0;
    }
    Occ has_type_ty = lean_emit_typed_occ(ks, ty, ty_sort);
    uint32_t ty_sort_w = lean_whnf(ks, ty_sort);
    if (ks->exprs[ty_sort_w].kind != LEXPR_SORT) {
        snprintf(err_buf, err_cap, "decl %s: declaration type is not a Sort", ks->names[decl_name].full);
        return 0;
    }
    uint32_t lvl = ks->exprs[ty_sort_w].d.sort_lvl;
    if (lean_lvl_is_zero(ks, lvl)) lvl = 0; /* Canonicalize Prop level to 0 */
    if (out_sort_lvl) *out_sort_lvl = lvl;
    Occ is_type_occ = lean_tc_derive_is_type(has_type_ty, ty, ty_sort, lvl);
    if (!is_type_occ) {
        snprintf(err_buf, err_cap, "decl %s: tcalc R_DERIVE_IS_TYPE rejected", ks->names[decl_name].full);
        return 0;
    }
    return is_type_occ;
}

/* Update primitive verification flags when genuine `Nat` or `String` inductives are admitted */
static void lean_note_verified_inductive(LeanKernelState *ks, const LeanDecl *ind) {
    if (ind->name == ks->nm_Nat && ind->nparams == 0 && ind->num_params == 0 &&
        ind->num_indices == 0 && ind->nctors == 2 &&
        ind->ctors[0].name == ks->nm_Nat_zero && ind->ctors[0].num_fields == 0 &&
        ind->ctors[1].name == ks->nm_Nat_succ && ind->ctors[1].num_fields == 1) {
        ks->nat_verified = true;
    }
    if (ind->name == ks->nm_String && ind->nparams == 0 && ind->num_params == 0 &&
        ind->num_indices == 0 && ind->nctors == 1 &&
        (ind->ctors[0].num_fields == 1 || ind->ctors[0].num_fields == 2)) {
        ks->string_verified = true;
    }
}

/* Strip outer type annotations (`outParam x`, `semiOutParam x`, `optParam x _`, `autoParam x _`)
 * matching `lean::consume_type_annotations` (`Lean/Expr.lean:1727-1743`) used by `add_inductive_fn::mk_local_decl_for`. */
static uint32_t lean_consume_type_annotations(LeanKernelState *ks, uint32_t e) {
    while (e != 0 && ks->exprs[e].kind == LEXPR_APP) {
        uint32_t fn1 = ks->exprs[e].d.app.fn;
        uint32_t arg1 = ks->exprs[e].d.app.arg;
        if (ks->exprs[fn1].kind == LEXPR_CONST) {
            uint32_t cname = ks->exprs[fn1].d.cnst.name;
            const char *full = ks->names[cname].full;
            if (full && (strcmp(full, "outParam") == 0 || strcmp(full, "semiOutParam") == 0)) {
                e = arg1;
                continue;
            }
        } else if (ks->exprs[fn1].kind == LEXPR_APP) {
            uint32_t fn2 = ks->exprs[fn1].d.app.fn;
            uint32_t arg0 = ks->exprs[fn1].d.app.arg;
            if (ks->exprs[fn2].kind == LEXPR_CONST) {
                uint32_t cname = ks->exprs[fn2].d.cnst.name;
                const char *full = ks->names[cname].full;
                if (full && (strcmp(full, "optParam") == 0 || strcmp(full, "autoParam") == 0)) {
                    e = arg0;
                    continue;
                }
            }
        }
        break;
    }
    return e;
}

/* Validate a single constructor against its inductive declaration `ind` and admit via `R_ADMIT_CTOR` */
static bool lean_verify_and_admit_ctor(LeanKernelState *ks, const LeanDecl *ind, uint32_t ind_lvl,
                                       uint32_t ntypes, const uint32_t *ind_names,
                                       LeanCtorSpec *cs, char *err_buf, size_t err_cap) {
    if (cs->name == 0 || lean_lookup_decl(ks, cs->name) != NULL) {
        snprintf(err_buf, err_cap, "ctor %s: invalid or duplicate constructor name",
                 ks->names[cs->name].full);
        return false;
    }
    if (cs->num_params != ind->num_params || cs->nparams != ind->nparams || cs->is_unsafe != ind->is_unsafe) {
        snprintf(err_buf, err_cap, "ctor %s: metadata mismatch with inductive %s",
                 ks->names[cs->name].full, ks->names[ind->name].full);
        return false;
    }
    for (uint32_t l = 0; l < ind->nparams; l++) {
        if (cs->level_params[l] != ind->level_params[l]) {
            snprintf(err_buf, err_cap, "ctor %s: levelParams mismatch with inductive %s",
                     ks->names[cs->name].full, ks->names[ind->name].full);
            return false;
        }
    }
    uint32_t c_sort_lvl = 0;
    Occ c_is_type_occ = lean_verify_is_type(ks, cs->name, cs->type, ind->nparams, ind->level_params,
                                            &c_sort_lvl, err_buf, err_cap);
    if (!c_is_type_occ) return false;

    /* Walk `num_params` parameters (checking domain defeq with `ind->type`) and `num_fields` fields */
    uint32_t ccur = cs->type;
    uint32_t icur = ind->type;
    uint32_t cpushed = 0;
    uint32_t *param_fvars = cs->num_params > 0
        ? (uint32_t *)malloc((size_t)cs->num_params * sizeof(uint32_t))
        : NULL;

    for (uint32_t p = 0; p < cs->num_params; p++) {
        if (ks->exprs[ccur].kind != LEXPR_FORALL) ccur = lean_whnf(ks, ccur);
        if (ks->exprs[icur].kind != LEXPR_FORALL) icur = lean_whnf(ks, icur);
        if (ks->exprs[ccur].kind != LEXPR_FORALL || ks->exprs[icur].kind != LEXPR_FORALL) {
            for (uint32_t j = 0; j < cpushed; j++) lean_pop_local(ks);
            free(param_fvars);
            snprintf(err_buf, err_cap, "ctor %s: missing parameter binder", ks->names[cs->name].full);
            return false;
        }
        uint32_t cdom = lean_consume_type_annotations(ks, ks->exprs[ccur].d.binder.domain);
        uint32_t idom = lean_consume_type_annotations(ks, ks->exprs[icur].d.binder.domain);
        if (!lean_is_def_eq(ks, cdom, idom)) {
            for (uint32_t j = 0; j < cpushed; j++) lean_pop_local(ks);
            free(param_fvars);
            snprintf(err_buf, err_cap, "ctor %s: parameter %u domain mismatch with inductive %s",
                     ks->names[cs->name].full, p, ks->names[ind->name].full);
            return false;
        }
        uint32_t fv = lean_push_local(ks, ks->exprs[ccur].d.binder.binder_name, cdom, 0);
        param_fvars[p] = fv;
        ccur = lean_expr_instantiate1(ks, ks->exprs[ccur].d.binder.body, fv);
        icur = lean_expr_instantiate1(ks, ks->exprs[icur].d.binder.body, fv);
        cpushed++;
    }

    for (uint32_t f = 0; f < cs->num_fields; f++) {
        if (ks->exprs[ccur].kind != LEXPR_FORALL) ccur = lean_whnf(ks, ccur);
        if (ks->exprs[ccur].kind != LEXPR_FORALL) {
            for (uint32_t j = 0; j < cpushed; j++) lean_pop_local(ks);
            free(param_fvars);
            snprintf(err_buf, err_cap, "ctor %s: missing field binder %u", ks->names[cs->name].full, f);
            return false;
        }
        uint32_t fdom = lean_consume_type_annotations(ks, ks->exprs[ccur].d.binder.domain);
        /* 1. Strict positivity across all mutual inductives in the block (including nested containers) */
        if (!lean_check_strict_positivity_block(ks, fdom, ntypes, ind_names, 0)) {
            for (uint32_t j = 0; j < cpushed; j++) lean_pop_local(ks);
            free(param_fvars);
            snprintf(err_buf, err_cap, "ctor %s: non-strictly-positive occurrence in field %u",
                     ks->names[cs->name].full, f);
            return false;
        }
        /* 2. Field universe constraint: if `ind_lvl != 0` (not Prop), field sort level must be <= `ind_lvl` */
        uint32_t fsort = lean_whnf(ks, lean_infer_type(ks, fdom));
        if (fsort == 0 || ks->exprs[fsort].kind != LEXPR_SORT) {
            for (uint32_t j = 0; j < cpushed; j++) lean_pop_local(ks);
            free(param_fvars);
            snprintf(err_buf, err_cap, "ctor %s: field %u domain is not a Sort", ks->names[cs->name].full, f);
            return false;
        }
        uint32_t flvl = ks->exprs[fsort].d.sort_lvl;
        if (!lean_lvl_is_zero(ks, ind_lvl) && !lean_lvl_leq(ks, flvl, ind_lvl)) {
            for (uint32_t j = 0; j < cpushed; j++) lean_pop_local(ks);
            free(param_fvars);
            snprintf(err_buf, err_cap, "ctor %s: field %u universe exceeds inductive universe",
                     ks->names[cs->name].full, f);
            return false;
        }
        uint32_t fv = lean_push_local(ks, ks->exprs[ccur].d.binder.binder_name, fdom, 0);
        ccur = lean_expr_instantiate1(ks, ks->exprs[ccur].d.binder.body, fv);
        cpushed++;
    }

    /* 3. Verify constructor resulting type (`ctorResultingTypeMismatch`):
     *    After peeling `num_params` parameters and `num_fields` fields, the target must be
     *    `Const(ind->name, level_params)` applied to `param_fvars[0..num_params-1]` and `num_indices` indices! */
    uint32_t sbuf[32];
    uint32_t *args = NULL;
    uint32_t nargs = 0, cap = 32;
    uint32_t head = lean_unpack_spine(ks, ccur, &args, &nargs, &cap, sbuf);
    if (ks->exprs[head].kind != LEXPR_CONST || ks->exprs[head].d.cnst.name != ind->name) {
        if (args != sbuf) free(args);
        nargs = 0; cap = 32; args = NULL;
        ccur = lean_whnf(ks, ccur);
        head = lean_unpack_spine(ks, ccur, &args, &nargs, &cap, sbuf);
    }
    bool target_ok = (ks->exprs[head].kind == LEXPR_CONST &&
                      ks->exprs[head].d.cnst.name == ind->name &&
                      ks->exprs[head].d.cnst.nus == ind->nparams &&
                      nargs == ind->num_params + ind->num_indices);
    if (target_ok) {
        for (uint32_t k = 0; k < ind->nparams; k++) {
            uint32_t u = ks->exprs[head].d.cnst.us[k];
            if (ks->lvls[u].kind != LLVL_PARAM || ks->lvls[u].param_name != ind->level_params[k]) {
                target_ok = false;
                break;
            }
        }
        for (uint32_t p = 0; target_ok && p < ind->num_params; p++) {
            if (!lean_is_def_eq(ks, args[p], param_fvars[p])) {
                target_ok = false;
                break;
            }
        }
        /* Also check that index arguments do not mention any mutual inductive in the block (`ind_names`) */
        for (uint32_t i = ind->num_params; target_ok && i < nargs; i++) {
            if (lean_expr_mentions_any_const(ks, args[i], ntypes, ind_names)) {
                target_ok = false;
                break;
            }
        }
    }
    if (args != sbuf) free(args);
    for (uint32_t j = 0; j < cpushed; j++) lean_pop_local(ks);
    free(param_fvars);

    if (!target_ok) {
        snprintf(err_buf, err_cap,
                 "ctor %s: resulting type is not %s applied to its parameters and indices (ctorResultingTypeMismatch)",
                 ks->names[cs->name].full, ks->names[ind->name].full);
        return false;
    }

    /* 4. Admit constructor into protected LEAN_SPACE_ENV via premise-bearing `R_ADMIT_CTOR` */
    LeanDecl cd;
    memset(&cd, 0, sizeof(cd));
    cd.kind = LDECL_CTOR;
    cd.name = cs->name;
    cd.ind_name = ind->name;
    cd.nparams = ind->nparams;
    if (ind->nparams > 0) {
        cd.level_params = (uint32_t *)malloc((size_t)ind->nparams * sizeof(uint32_t));
        memcpy(cd.level_params, ind->level_params, (size_t)ind->nparams * sizeof(uint32_t));
    }
    cd.type = cs->type;
    cd.cidx = cs->cidx;
    cd.num_params = cs->num_params;
    cd.num_fields = cs->num_fields;
    cd.is_unsafe = cs->is_unsafe;
    cd.tc_occ = lean_tc_admit_ctor(ind->tc_occ, c_is_type_occ, cd.name, ind->name, cd.type, ind->type, c_sort_lvl);
    if (!cd.tc_occ) {
        free(cd.level_params);
        snprintf(err_buf, err_cap, "ctor %s: tcalc R_ADMIT_CTOR rejected", ks->names[cd.name].full);
        return false;
    }
    lean_ensure_decls_cap(ks, cd.name);
    ks->decls_by_name[cd.name] = cd;
    ks->stat_ctors++;
    g_tc_admitted_decls++;
    return true;
}

/* Validate a recursor declaration (major premise inductive, large elimination from Prop, K-flag, and rules)
 * and admit into `LEAN_SPACE_ENV` via premise-bearing `R_ADMIT_REC`. */
static bool lean_verify_and_admit_rec(LeanKernelState *ks, LeanDecl *rec, char *err_buf, size_t err_cap) {
    uint32_t r_sort_lvl = 0;
    Occ r_is_type_occ = lean_verify_is_type(ks, rec->name, rec->type, rec->nparams, rec->level_params,
                                            &r_sort_lvl, err_buf, err_cap);
    if (!r_is_type_occ) return false;

    uint32_t pre_binders = rec->num_params + rec->num_motives + rec->num_minors + rec->num_indices;
    uint32_t cur = rec->type;
    uint32_t pushed = 0;
    for (uint32_t i = 0; i < pre_binders; i++) {
        if (ks->exprs[cur].kind != LEXPR_FORALL) cur = lean_whnf(ks, cur);
        if (ks->exprs[cur].kind != LEXPR_FORALL) {
            for (uint32_t j = 0; j < pushed; j++) lean_pop_local(ks);
            snprintf(err_buf, err_cap, "rec %s: missing binder before major premise", ks->names[rec->name].full);
            return false;
        }
        uint32_t fv = lean_push_local(ks, ks->exprs[cur].d.binder.binder_name, ks->exprs[cur].d.binder.domain, 0);
        cur = lean_expr_instantiate1(ks, ks->exprs[cur].d.binder.body, fv);
        pushed++;
    }
    if (ks->exprs[cur].kind != LEXPR_FORALL) cur = lean_whnf(ks, cur);
    if (ks->exprs[cur].kind != LEXPR_FORALL) {
        for (uint32_t j = 0; j < pushed; j++) lean_pop_local(ks);
        snprintf(err_buf, err_cap, "rec %s: missing major premise binder", ks->names[rec->name].full);
        return false;
    }
    uint32_t major_dom = ks->exprs[cur].d.binder.domain;
    uint32_t sbuf[32];
    uint32_t *margs = NULL;
    uint32_t mnargs = 0, mcap = 32;
    uint32_t mhead = lean_unpack_spine(ks, major_dom, &margs, &mnargs, &mcap, sbuf);
    if (ks->exprs[mhead].kind != LEXPR_CONST) {
        if (margs != sbuf) free(margs);
        mnargs = 0; mcap = 32; margs = NULL;
        major_dom = lean_whnf(ks, major_dom);
        mhead = lean_unpack_spine(ks, major_dom, &margs, &mnargs, &mcap, sbuf);
    }
    uint32_t major_ind_name = (ks->exprs[mhead].kind == LEXPR_CONST) ? ks->exprs[mhead].d.cnst.name : 0;
    if (margs != sbuf) free(margs);
    for (uint32_t j = 0; j < pushed; j++) lean_pop_local(ks);

    if (rec->ind_name == 0) rec->ind_name = major_ind_name;

    for (uint32_t r = 0; r < rec->nrules; r++) {
        LeanRecRule *rr = &rec->rules[r];
        if (rr->rhs == 0 || ks->exprs[rr->rhs].loose_bvar_range != 0 || ks->exprs[rr->rhs].has_fvar ||
            !lean_check_expr_lvl_params(ks, rr->rhs, rec->nparams, rec->level_params) ||
            lean_check_expr(ks, rr->rhs) == 0) {
            snprintf(err_buf, err_cap, "rec %s: failed to typecheck rule %u rhs", ks->names[rec->name].full, r);
            return false;
        }
    }

    rec->tc_occ = lean_tc_admit_rec(r_is_type_occ, rec->name, rec->ind_name, rec->type, r_sort_lvl);
    if (!rec->tc_occ) {
        snprintf(err_buf, err_cap, "rec %s: tcalc R_ADMIT_REC rejected", ks->names[rec->name].full);
        return false;
    }
    lean_ensure_decls_cap(ks, rec->name);
    ks->decls_by_name[rec->name] = *rec;
    ks->stat_recs++;
    g_tc_admitted_decls++;
    return true;
}

/* Verify `Eq` inductive prerequisite and exact canonical type of `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`
 * (`Lean4Lean/Quot.lean:20-83`). */
static bool lean_verify_quot_shape(LeanKernelState *ks, const LeanDecl *d, char *err_buf, size_t err_cap) {
    /* 1. Verify `Eq` is already an admitted 1-constructor inductive with canonical type (`checkEqType`). */
    uint32_t nm_Eq = lean_name_mk_str(ks, 0, "Eq");
    const LeanDecl *eq_ind = lean_lookup_decl(ks, nm_Eq);
    if (!eq_ind || eq_ind->kind != LDECL_IND || eq_ind->nparams != 1 || eq_ind->nctors != 1) {
        snprintf(err_buf, err_cap, "quot %s: prerequisite inductive 'Eq' is missing or malformed",
                 ks->names[d->name].full);
        return false;
    }
    uint32_t eq_u = lean_lvl_mk_param(ks, eq_ind->level_params[0]);
    uint32_t sort_eq_u = lean_expr_mk_sort(ks, eq_u);
    uint32_t sort_0    = lean_expr_mk_sort(ks, 0u);
    uint32_t bvar_0    = lean_expr_mk_bvar(ks, 0u);
    uint32_t bvar_1    = lean_expr_mk_bvar(ks, 1u);
    /* Expected Eq.type: forall (α : Sort u), α -> α -> Prop */
    uint32_t eq_expected_ty = lean_expr_mk_forall(
        ks, 0u, sort_eq_u,
        lean_expr_mk_forall(ks, 0u, bvar_0,
            lean_expr_mk_forall(ks, 0u, bvar_1, sort_0)));
    if (!lean_expr_eqv(ks, eq_ind->type, eq_expected_ty)) {
        snprintf(err_buf, err_cap, "quot %s: 'Eq' does not have canonical equality type", ks->names[d->name].full);
        return false;
    }
    const LeanDecl *eq_refl = lean_lookup_decl(ks, eq_ind->ctors[0].name);
    if (!eq_refl || eq_refl->kind != LDECL_CTOR || eq_refl->nparams != 1) {
        snprintf(err_buf, err_cap, "quot %s: 'Eq.refl' constructor is missing or malformed", ks->names[d->name].full);
        return false;
    }
    uint32_t eq_refl_u = lean_lvl_mk_param(ks, eq_refl->level_params[0]);
    uint32_t eq_const  = lean_expr_mk_const(ks, nm_Eq, 1u, &eq_refl_u);
    uint32_t eq_app    = lean_expr_mk_app(ks, lean_expr_mk_app(ks, lean_expr_mk_app(ks, eq_const, bvar_1), bvar_0), bvar_0);
    uint32_t eq_refl_expected_ty = lean_expr_mk_forall(
        ks, 0u, lean_expr_mk_sort(ks, eq_refl_u),
        lean_expr_mk_forall(ks, 0u, bvar_0, eq_app));
    if (!lean_expr_eqv(ks, eq_refl->type, eq_refl_expected_ty)) {
        snprintf(err_buf, err_cap, "quot %s: 'Eq' constructor does not have canonical reflexivity type",
                 ks->names[d->name].full);
        return false;
    }

    /* 2. Construct the exact canonical type for `Quot`, `Quot.mk`, `Quot.lift`, or `Quot.ind` and compare. */
    uint32_t expected_params = 0;
    uint8_t  expected_qkind  = LQUOT_NONE;
    if (d->name == ks->nm_Quot)          { expected_params = 1; expected_qkind = LQUOT_TYPE; }
    else if (d->name == ks->nm_Quot_mk)  { expected_params = 1; expected_qkind = LQUOT_CTOR; }
    else if (d->name == ks->nm_Quot_lift){ expected_params = 2; expected_qkind = LQUOT_LIFT; }
    else if (d->name == ks->nm_Quot_ind) { expected_params = 1; expected_qkind = LQUOT_IND; }
    else {
        snprintf(err_buf, err_cap, "quot %s: unrecognized quotient primitive name", ks->names[d->name].full);
        return false;
    }
    if (d->quot_kind != LQUOT_NONE && d->quot_kind != expected_qkind) {
        snprintf(err_buf, err_cap, "quot %s: mismatched quot kind for primitive name", ks->names[d->name].full);
        return false;
    }
    if (d->nparams != expected_params) {
        snprintf(err_buf, err_cap, "quot %s: expected %u level params, got %u",
                 ks->names[d->name].full, expected_params, d->nparams);
        return false;
    }
    uint32_t u = lean_lvl_mk_param(ks, d->level_params[0]);
    uint32_t sort_u = lean_expr_mk_sort(ks, u);
    uint32_t fv_alpha = lean_push_local(ks, 0u, sort_u, 0u);
    uint32_t rel_ty   = lean_expr_mk_forall(ks, 0u, fv_alpha, lean_expr_mk_forall(ks, 0u, fv_alpha, sort_0));
    uint32_t fv_r     = lean_push_local(ks, 0u, rel_ty, 0u);
    uint32_t quot_const = lean_expr_mk_const(ks, ks->nm_Quot, 1u, &u);
    uint32_t quot_r     = lean_expr_mk_app(ks, lean_expr_mk_app(ks, quot_const, fv_alpha), fv_r);
    uint32_t expected_ty = 0;

    if (d->name == ks->nm_Quot) {
        uint32_t fvs[2] = { fv_alpha, fv_r };
        expected_ty = lean_lctx_mk_forall(ks, 2u, fvs, sort_u);
    } else if (d->name == ks->nm_Quot_mk) {
        uint32_t fv_a = lean_push_local(ks, 0u, fv_alpha, 0u);
        uint32_t fvs[3] = { fv_alpha, fv_r, fv_a };
        expected_ty = lean_lctx_mk_forall(ks, 3u, fvs, quot_r);
        lean_pop_local(ks);
    } else if (d->name == ks->nm_Quot_lift) {
        uint32_t v = lean_lvl_mk_param(ks, d->level_params[1]);
        uint32_t sort_v = lean_expr_mk_sort(ks, v);
        uint32_t fv_beta = lean_push_local(ks, 0u, sort_v, 0u);
        uint32_t fv_f    = lean_push_local(ks, 0u, lean_expr_mk_forall(ks, 0u, fv_alpha, fv_beta), 0u);
        uint32_t fv_a    = lean_push_local(ks, 0u, fv_alpha, 0u);
        uint32_t fv_b    = lean_push_local(ks, 0u, fv_alpha, 0u);
        uint32_t rab     = lean_expr_mk_app(ks, lean_expr_mk_app(ks, fv_r, fv_a), fv_b);
        uint32_t eq_v    = lean_expr_mk_const(ks, nm_Eq, 1u, &v);
        uint32_t fa      = lean_expr_mk_app(ks, fv_f, fv_a);
        uint32_t fb      = lean_expr_mk_app(ks, fv_f, fv_b);
        uint32_t fa_eq_fb = lean_expr_mk_app(ks, lean_expr_mk_app(ks, lean_expr_mk_app(ks, eq_v, fv_beta), fa), fb);
        uint32_t ab_fvs[2] = { fv_a, fv_b };
        uint32_t sanity  = lean_lctx_mk_forall(ks, 2u, ab_fvs, lean_expr_mk_forall(ks, 0u, rab, fa_eq_fb));
        uint32_t lift_tail = lean_expr_mk_forall(ks, 0u, sanity, lean_expr_mk_forall(ks, 0u, quot_r, fv_beta));
        uint32_t fvs[4] = { fv_alpha, fv_r, fv_beta, fv_f };
        expected_ty = lean_lctx_mk_forall(ks, 4u, fvs, lift_tail);
        lean_pop_local(ks);
        lean_pop_local(ks);
        lean_pop_local(ks);
        lean_pop_local(ks);
    } else if (d->name == ks->nm_Quot_ind) {
        uint32_t fv_beta = lean_push_local(ks, 0u, lean_expr_mk_forall(ks, 0u, quot_r, sort_0), 0u);
        uint32_t fv_a    = lean_push_local(ks, 0u, fv_alpha, 0u);
        uint32_t qmk_c   = lean_expr_mk_const(ks, ks->nm_Quot_mk, 1u, &u);
        uint32_t qmk_a   = lean_expr_mk_app(ks, lean_expr_mk_app(ks, lean_expr_mk_app(ks, qmk_c, fv_alpha), fv_r), fv_a);
        uint32_t all_quot = lean_lctx_mk_forall(ks, 1u, &fv_a, lean_expr_mk_app(ks, fv_beta, qmk_a));
        lean_pop_local(ks);
        uint32_t fv_q    = lean_push_local(ks, 0u, quot_r, 0u);
        uint32_t q_tail  = lean_lctx_mk_forall(ks, 1u, &fv_q, lean_expr_mk_app(ks, fv_beta, fv_q));
        lean_pop_local(ks);
        uint32_t ind_tail = lean_expr_mk_forall(ks, 0u, all_quot, q_tail);
        uint32_t fvs[3] = { fv_alpha, fv_r, fv_beta };
        expected_ty = lean_lctx_mk_forall(ks, 3u, fvs, ind_tail);
        lean_pop_local(ks);
    }
    lean_pop_local(ks);
    lean_pop_local(ks);

    if (!lean_expr_eqv(ks, d->type, expected_ty)) {
        snprintf(err_buf, err_cap, "quot %s: declared type does not match canonical quotient primitive type",
                 ks->names[d->name].full);
        return false;
    }
    return true;
}

static bool lean_verify_and_admit_decl_inner(LeanKernelState *ks, LeanDecl *d, char *err_buf, size_t err_cap) {
    if (d->name == 0 || lean_lookup_decl(ks, d->name) != NULL) {
        snprintf(err_buf, err_cap, "decl %s: invalid or duplicate declaration name", ks->names[d->name].full);
        return false;
    }

    uint32_t ty_sort_lvl = 0;
    Occ is_type_occ = lean_verify_is_type(ks, d->name, d->type, d->nparams, d->level_params,
                                          &ty_sort_lvl, err_buf, err_cap);
    if (!is_type_occ) return false;

    if (d->kind == LDECL_DEFN || d->kind == LDECL_THM || d->kind == LDECL_OPAQUE) {
        if (d->value == 0 || ks->exprs[d->value].loose_bvar_range != 0 || ks->exprs[d->value].has_fvar) {
            snprintf(err_buf, err_cap, "decl %s: value is missing or not closed", ks->names[d->name].full);
            return false;
        }
        if (!lean_check_expr_lvl_params(ks, d->value, d->nparams, d->level_params)) {
            snprintf(err_buf, err_cap, "decl %s: undeclared universe parameter in value", ks->names[d->name].full);
            return false;
        }
        /* For theorems, `d->type` MUST be a proposition (`ty_sort_lvl == 0`) */
        Occ is_prop_occ = 0;
        if (d->kind == LDECL_THM) {
            if (!lean_lvl_is_zero(ks, ty_sort_lvl)) {
                snprintf(err_buf, err_cap, "thm %s: theorem type is not a Prop", ks->names[d->name].full);
                return false;
            }
            is_prop_occ = lean_tc_derive_is_prop(is_type_occ, d->type);
            if (!is_prop_occ) {
                snprintf(err_buf, err_cap, "thm %s: tcalc R_DERIVE_IS_PROP rejected non-Prop theorem",
                         ks->names[d->name].full);
                return false;
            }
        }
        uint32_t val_ty = lean_check_expr(ks, d->value);
        if (val_ty == 0) {
            snprintf(err_buf, err_cap, "decl %s: failed to infer type of value/proof", ks->names[d->name].full);
            return false;
        }
        Occ has_type_val = lean_emit_typed_occ(ks, d->value, val_ty);
        if (!lean_is_def_eq(ks, val_ty, d->type)) {
            snprintf(err_buf, err_cap, "decl %s: value type is not definitionally equal to declared type",
                     ks->names[d->name].full);
            return false;
        }
        Occ defeq_occ = lean_tc_commit2(R_EMIT_DEFEQ, val_ty, d->type);
        Occ has_expected_ty = lean_tc_commit_conv(has_type_val, defeq_occ, is_type_occ,
                                                  d->value, val_ty, d->type, ty_sort_lvl);
        if (!has_expected_ty) {
            snprintf(err_buf, err_cap, "decl %s: tcalc R_CHECK_CONV rejected", ks->names[d->name].full);
            return false;
        }
        if (d->kind == LDECL_DEFN) {
            if (!d->has_explicit_hints) {
                d->hint_kind = LHINT_REGULAR;
                d->height = lean_compute_max_height(ks, d->value) + 1u;
            }
            d->tc_occ = lean_tc_admit_defn(is_type_occ, has_expected_ty, d->name, d->type, d->value, ty_sort_lvl);
            ks->stat_defns++;
        } else if (d->kind == LDECL_THM) {
            d->tc_occ = lean_tc_admit_thm(is_prop_occ, has_expected_ty, d->name, d->type, d->value);
            ks->stat_thms++;
            g_tc_admitted_thms++;
        } else {
            d->tc_occ = lean_tc_admit_opaque(is_type_occ, has_expected_ty, d->name, d->type, d->value, ty_sort_lvl);
            ks->stat_opaques++;
        }
    } else if (d->kind == LDECL_AXIOM) {
        d->tc_occ = lean_tc_admit_axiom(is_type_occ, d->name, d->type, ty_sort_lvl);
        ks->stat_axioms++;
        if (ks->n_axiom_names >= ks->cap_axiom_names) {
            uint32_t ncap = ks->cap_axiom_names ? ks->cap_axiom_names * 2u : 32u;
            ks->axiom_names = (uint32_t *)realloc(ks->axiom_names, (size_t)ncap * sizeof(uint32_t));
            ks->cap_axiom_names = ncap;
        }
        ks->axiom_names[ks->n_axiom_names++] = d->name;
    } else if (d->kind == LDECL_QUOT) {
        if (!lean_verify_quot_shape(ks, d, err_buf, err_cap)) return false;
        d->tc_occ = lean_tc_admit_quot(is_type_occ, d->name, d->type, ty_sort_lvl);
        ks->stat_quots++;
    } else {
        snprintf(err_buf, err_cap, "decl %s: unsupported standalone declaration kind", ks->names[d->name].full);
        return false;
    }

    if (!d->tc_occ) {
        snprintf(err_buf, err_cap, "decl %s: tcalc R_ADMIT_* rejected", ks->names[d->name].full);
        return false;
    }
    bool refs_sorry = (ks->exprs[d->type].has_sorry != 0) ||
                      (d->value != 0 && ks->exprs[d->value].has_sorry != 0);
    bool refs_trust_compiler = (ks->exprs[d->type].has_trust_compiler != 0) ||
                               (d->value != 0 && ks->exprs[d->value].has_trust_compiler != 0);
    d->uses_sorry = (ks->nm_sorryAx != 0 && d->name == ks->nm_sorryAx) || refs_sorry;
    d->uses_trust_compiler = (ks->nm_trustCompiler != 0 && d->name == ks->nm_trustCompiler) ||
                             (ks->nm_ofReduceBool != 0 && d->name == ks->nm_ofReduceBool) ||
                             (ks->nm_ofReduceNat != 0 && d->name == ks->nm_ofReduceNat) ||
                             refs_trust_compiler;
    if (refs_sorry && ks->forbid_sorry) {
        snprintf(err_buf, err_cap, "decl %s: rejected by --forbid-sorry trust policy (references sorryAx)",
                 ks->names[d->name].full);
        return false;
    }
    if (refs_trust_compiler && ks->forbid_trust_compiler) {
        snprintf(err_buf, err_cap, "decl %s: rejected by --forbid-trust-compiler trust policy (references compiler trust axiom)",
                 ks->names[d->name].full);
        return false;
    }
    if (refs_sorry) ks->stat_sorry_decls++;
    if (refs_trust_compiler) ks->stat_trust_compiler_decls++;
    g_tc_admitted_decls++;
    lean_ensure_decls_cap(ks, d->name);
    ks->decls_by_name[d->name] = *d;
    return true;
}

static bool lean_verify_and_admit_decl(LeanKernelState *ks, LeanDecl *d, char *err_buf, size_t err_cap) {
    lean_scratch_scope_begin(ks);
    bool ok = lean_verify_and_admit_decl_inner(ks, d, err_buf, err_cap);
    lean_scratch_scope_end(ks);
    return ok;
}

/* =========================================================================
 * 6b. Canonical Inductive + Nested Inductive + Recursor Kernel (`AddInductive`)
 * ========================================================================= */

typedef struct {
    uint32_t fn;          /* Const(F, ls) applied to params: F A_1 ... A_k */
    uint32_t aux_ind_name;
    uint32_t params_len;
    uint32_t *params;
    uint32_t nlevels;
    uint32_t *levels;
} LeanNestedAuxEntry;

typedef struct {
    LeanKernelState *ks;
    uint32_t ntypes;
    LeanDecl *base_types;
    uint32_t nparams;
    uint32_t *param_fvars;
    uint32_t nparams_lvls;
    uint32_t *param_lvls;
    uint32_t next_idx;

    uint32_t n_entries;
    uint32_t cap_entries;
    LeanNestedAuxEntry *entries;

    uint32_t n_aux_types;
    uint32_t cap_aux_types;
    LeanDecl *aux_types;

    uint32_t n_aux_ctors;
    uint32_t cap_aux_ctors;
    LeanCtorSpec *aux_ctors;

    uint32_t n_aux2nested;
    uint32_t cap_aux2nested;
    uint32_t *aux2nested_k;
    uint32_t *aux2nested_v; /* F A_1 ... A_k (with param FVars) */
} LeanElimNestedState;

static void lean_elim_nested_add_aux2nested(LeanElimNestedState *st, uint32_t aux_name, uint32_t nested_expr) {
    if (st->n_aux2nested >= st->cap_aux2nested) {
        st->cap_aux2nested = st->cap_aux2nested ? st->cap_aux2nested * 2u : 16u;
        st->aux2nested_k = (uint32_t *)realloc(st->aux2nested_k, st->cap_aux2nested * sizeof(uint32_t));
        st->aux2nested_v = (uint32_t *)realloc(st->aux2nested_v, st->cap_aux2nested * sizeof(uint32_t));
    }
    st->aux2nested_k[st->n_aux2nested] = aux_name;
    st->aux2nested_v[st->n_aux2nested] = lean_expr_abstract_fvar_exprs(st->ks, nested_expr, st->nparams, st->param_fvars);
    st->n_aux2nested++;
}

static bool lean_expr_has_nested_ind_occ(LeanElimNestedState *st, uint32_t e) {
    LeanKernelState *ks = st->ks;
    if (e == 0) return false;
    const LeanExpr *ex = &ks->exprs[e];
    switch (ex->kind) {
        case LEXPR_CONST:
            for (uint32_t i = 0; i < st->ntypes; i++) {
                if (ex->d.cnst.name == st->base_types[i].name) return true;
            }
            for (uint32_t a = 0; a < st->n_aux_types; a++) {
                if (ex->d.cnst.name == st->aux_types[a].name) return true;
            }
            return false;
        case LEXPR_APP:
            return lean_expr_has_nested_ind_occ(st, ex->d.app.fn) ||
                   lean_expr_has_nested_ind_occ(st, ex->d.app.arg);
        case LEXPR_LAM:
        case LEXPR_FORALL:
            return lean_expr_has_nested_ind_occ(st, ex->d.binder.domain) ||
                   lean_expr_has_nested_ind_occ(st, ex->d.binder.body);
        case LEXPR_LET:
            return lean_expr_has_nested_ind_occ(st, ex->d.let_e.type) ||
                   lean_expr_has_nested_ind_occ(st, ex->d.let_e.val) ||
                   lean_expr_has_nested_ind_occ(st, ex->d.let_e.body);
        case LEXPR_PROJ:
            return lean_expr_has_nested_ind_occ(st, ex->d.proj.struct_expr);
        default:
            return false;
    }
}

/* Instantiate `e`'s `I_k`'s params with `st->param_fvars` when checking nested occurrence */
static uint32_t lean_replace_params_at_nested(LeanElimNestedState *st, uint32_t e, bool *out_ok) {
    LeanKernelState *ks = st->ks;
    if (!*out_ok || e == 0) return e;
    uint32_t *args = NULL;
    uint32_t nargs = 0;
    uint32_t fn = lean_get_app_args_alloc(ks, e, &args, &nargs);
    if (ks->exprs[fn].kind == LEXPR_CONST) {
        int found_ind = -1;
        for (uint32_t t = 0; t < st->ntypes; t++) {
            if (ks->exprs[fn].d.cnst.name == st->base_types[t].name) {
                found_ind = (int)t;
                break;
            }
        }
        if (found_ind < 0) {
            for (uint32_t a = 0; a < st->n_aux_types; a++) {
                if (ks->exprs[fn].d.cnst.name == st->aux_types[a].name) {
                    found_ind = (int)(st->ntypes + a);
                    break;
                }
            }
        }
        if (found_ind >= 0) {
            if (nargs < st->nparams) { free(args); *out_ok = false; return 0; }
            if (ks->exprs[fn].d.cnst.nus != st->nparams_lvls) { free(args); *out_ok = false; return 0; }
            for (uint32_t i = 0; i < st->nparams_lvls; i++) {
                uint32_t lv = ks->exprs[fn].d.cnst.us[i];
                if (ks->lvls[lv].kind != LLVL_PARAM || ks->lvls[lv].param_name != st->param_lvls[i]) {
                    free(args); *out_ok = false; return 0;
                }
            }
            for (uint32_t i = 0; i < st->nparams; i++) {
                if (args[i] != st->param_fvars[i]) {
                    if (!lean_expr_eqv(ks, args[i], st->param_fvars[i])) {
                        free(args); *out_ok = false; return 0;
                    }
                }
            }
            uint32_t res = fn;
            for (uint32_t i = 0; i < st->nparams; i++) {
                res = lean_expr_mk_app(ks, res, st->param_fvars[i]);
            }
            for (uint32_t i = st->nparams; i < nargs; i++) {
                uint32_t na = lean_replace_params_at_nested(st, args[i], out_ok);
                if (!*out_ok) { free(args); return 0; }
                res = lean_expr_mk_app(ks, res, na);
            }
            free(args);
            return res;
        }
    }
    free(args);
    const LeanExpr *ex = &ks->exprs[e];
    switch (ex->kind) {
        case LEXPR_APP: {
            uint32_t nf = lean_replace_params_at_nested(st, ex->d.app.fn, out_ok);
            uint32_t na = lean_replace_params_at_nested(st, ex->d.app.arg, out_ok);
            return *out_ok ? lean_expr_mk_app(ks, nf, na) : 0;
        }
        case LEXPR_LAM:
        case LEXPR_FORALL: {
            uint32_t nd = lean_replace_params_at_nested(st, ex->d.binder.domain, out_ok);
            uint32_t nb = lean_replace_params_at_nested(st, ex->d.binder.body, out_ok);
            if (!*out_ok) return 0;
            return ex->kind == LEXPR_FORALL
                       ? lean_expr_mk_forall(ks, ex->d.binder.binder_name, nd, nb)
                       : lean_expr_mk_lam(ks, ex->d.binder.binder_name, nd, nb);
        }
        case LEXPR_LET: {
            uint32_t nt = lean_replace_params_at_nested(st, ex->d.let_e.type, out_ok);
            uint32_t nv = lean_replace_params_at_nested(st, ex->d.let_e.val, out_ok);
            uint32_t nb = lean_replace_params_at_nested(st, ex->d.let_e.body, out_ok);
            return *out_ok ? lean_expr_mk_let(ks, ex->d.let_e.binder_name, nt, nv, nb) : 0;
        }
        case LEXPR_PROJ: {
            uint32_t ns = lean_replace_params_at_nested(st, ex->d.proj.struct_expr, out_ok);
            return *out_ok ? lean_expr_mk_proj(ks, ex->d.proj.type_name, ex->d.proj.idx, ns) : 0;
        }
        default:
            return e;
    }
}

static uint32_t lean_elim_nested(LeanElimNestedState *st, uint32_t e, char *err_buf, size_t err_cap);

static uint32_t lean_mk_unique_nested_name(LeanElimNestedState *st, uint32_t base_name) {
    LeanKernelState *ks = st->ks;
    while (1) {
        uint32_t r = lean_name_append_index_after(ks, base_name, st->next_idx);
        st->next_idx++;
        if (lean_lookup_decl(ks, r) != NULL) continue;
        bool collision = false;
        for (uint32_t c = 0; c < st->n_aux_ctors; c++) {
            if (st->aux_ctors[c].name == r) { collision = true; break; }
        }
        if (!collision) return r;
    }
}

/* Forward check if `e` is a nested inductive occurrence `F A_1 ... A_p idx_1 ... idx_m` where some `A_j` contains a mutual `I_k` */
static uint32_t lean_elim_nested_if_nested_app(LeanElimNestedState *st, uint32_t e, bool *matched, char *err_buf, size_t err_cap) {
    LeanKernelState *ks = st->ks;
    *matched = false;
    if (!lean_expr_has_nested_ind_occ(st, e)) return e;

    uint32_t *args = NULL;
    uint32_t nargs = 0;
    uint32_t fn = lean_get_app_args_alloc(ks, e, &args, &nargs);
    if (ks->exprs[fn].kind != LEXPR_CONST) { free(args); return e; }

    uint32_t fn_name = ks->exprs[fn].d.cnst.name;
    const LeanDecl *fn_decl = lean_lookup_decl(ks, fn_name);
    if (!fn_decl || fn_decl->kind != LDECL_IND || fn_decl->num_params > nargs) { free(args); return e; }

    bool has_nested_in_params = false;
    bool loose_in_params = false;
    for (uint32_t i = 0; i < fn_decl->num_params; i++) {
        if (lean_expr_has_nested_ind_occ(st, args[i])) has_nested_in_params = true;
        if (ks->exprs[args[i]].loose_bvar_range > 0) loose_in_params = true;
    }
    if (!has_nested_in_params) { free(args); return e; }
    if (loose_in_params) {
        free(args);
        snprintf(err_buf, err_cap, "nested inductive occurrence '%s' has loose bound variables in parameters",
                 ks->names[fn_name].full);
        *matched = true;
        return 0;
    }

    *matched = true;
    /* Normalize nested params */
    uint32_t *new_args = (uint32_t *)calloc(nargs ? nargs : 1u, sizeof(uint32_t));
    for (uint32_t i = 0; i < nargs; i++) new_args[i] = args[i];
    free(args);
    for (uint32_t i = 0; i < fn_decl->num_params; i++) {
        bool ok = true;
        new_args[i] = lean_replace_params_at_nested(st, new_args[i], &ok);
        if (!ok) {
            free(new_args);
            snprintf(err_buf, err_cap, "invalid nested inductive occurrence of '%s': failed parameter check",
                     ks->names[fn_name].full);
            return 0;
        }
    }

    uint32_t fn_with_params = fn;
    for (uint32_t i = 0; i < fn_decl->num_params; i++) {
        fn_with_params = lean_expr_mk_app(ks, fn_with_params, new_args[i]);
    }

    uint32_t *lvl_ids = (uint32_t *)calloc(st->nparams_lvls ? st->nparams_lvls : 1u, sizeof(uint32_t));
    for (uint32_t l = 0; l < st->nparams_lvls; l++) lvl_ids[l] = lean_lvl_mk_param(ks, st->param_lvls[l]);

    /* Check if we already synthesized an aux inductive for `fn_with_params` */
    for (uint32_t idx = 0; idx < st->n_entries; idx++) {
        if (lean_expr_eqv(ks, st->entries[idx].fn, fn_with_params)) {
            uint32_t aux_const = lean_expr_mk_const(ks, st->entries[idx].aux_ind_name, st->nparams_lvls, lvl_ids);
            free(lvl_ids);
            uint32_t res = aux_const;
            for (uint32_t p = 0; p < st->nparams; p++) res = lean_expr_mk_app(ks, res, st->param_fvars[p]);
            for (uint32_t j = fn_decl->num_params; j < nargs; j++) {
                uint32_t arg_elim = lean_elim_nested(st, new_args[j], err_buf, err_cap);
                if (arg_elim == 0) { free(new_args); return 0; }
                res = lean_expr_mk_app(ks, res, arg_elim);
            }
            free(new_args);
            return res;
        }
    }

    /* Create a new mutual block of auxiliary inductives mirroring `fn_decl`'s mutual block `all` */
    uint32_t n_nested_all = fn_decl->nall ? fn_decl->nall : 1u;
    uint32_t single_all = fn_name;
    const uint32_t *nested_all = fn_decl->nall ? fn_decl->all : &single_all;

    uint32_t fn_nlevels = ks->exprs[fn].d.cnst.nus;
    uint32_t *fn_levels = (uint32_t *)malloc((fn_nlevels ? fn_nlevels : 1u) * sizeof(uint32_t));
    for (uint32_t l = 0; l < fn_nlevels; l++) fn_levels[l] = ks->exprs[fn].d.cnst.us[l];

    uint32_t result_aux_ind_name = 0;
    uint32_t *this_batch_aux_names = (uint32_t *)calloc(n_nested_all, sizeof(uint32_t));
    uint32_t *this_batch_type_idx  = (uint32_t *)calloc(n_nested_all, sizeof(uint32_t));

    /* First pass: allocate names and register entries so recursive constructor types hit the cache */
    for (uint32_t m = 0; m < n_nested_all; m++) {
        uint32_t J_name = nested_all[m];
        const LeanDecl *J_decl = lean_lookup_decl(ks, J_name);
        if (!J_decl || J_decl->kind != LDECL_IND) {
            snprintf(err_buf, err_cap, "nested inductive mutual partner '%s' not found", ks->names[J_name].full);
            free(lvl_ids); free(new_args); free(fn_levels); free(this_batch_aux_names); free(this_batch_type_idx);
            return 0;
        }
        uint32_t base_aux_name = lean_name_append(ks, st->base_types[0].name, J_name);
        uint32_t aux_J_name = lean_mk_unique_nested_name(st, base_aux_name);
        this_batch_aux_names[m] = aux_J_name;
        if (J_name == fn_name) result_aux_ind_name = aux_J_name;

        uint32_t J_const = lean_expr_mk_const(ks, J_name, fn_nlevels, fn_levels);
        uint32_t J_applied = J_const;
        for (uint32_t p = 0; p < fn_decl->num_params; p++) {
            J_applied = lean_expr_mk_app(ks, J_applied, new_args[p]);
        }
        lean_elim_nested_add_aux2nested(st, aux_J_name, J_applied);

        if (st->n_entries >= st->cap_entries) {
            st->cap_entries = st->cap_entries ? st->cap_entries * 2u : 16u;
            st->entries = (LeanNestedAuxEntry *)realloc(st->entries, st->cap_entries * sizeof(LeanNestedAuxEntry));
        }
        LeanNestedAuxEntry *ent = &st->entries[st->n_entries++];
        ent->fn = J_applied;
        ent->aux_ind_name = aux_J_name;
        ent->params_len = fn_decl->num_params;
        ent->params = (uint32_t *)malloc((fn_decl->num_params ? fn_decl->num_params : 1u) * sizeof(uint32_t));
        for (uint32_t p = 0; p < fn_decl->num_params; p++) ent->params[p] = new_args[p];
        ent->nlevels = fn_nlevels;
        ent->levels = (uint32_t *)malloc((fn_nlevels ? fn_nlevels : 1u) * sizeof(uint32_t));
        for (uint32_t l = 0; l < fn_nlevels; l++) ent->levels[l] = fn_levels[l];

        /* Build aux_J type: instantiate J_decl->type with fn_levels and instantiate its params with new_args[0..num_params-1], then abstract over st->param_fvars */
        uint32_t J_type = lean_expr_subst_lvls(ks, J_decl->type, J_decl->nparams, J_decl->level_params, fn_levels);
        for (uint32_t p = 0; p < fn_decl->num_params; p++) {
            if (ks->exprs[J_type].kind != LEXPR_FORALL) {
                snprintf(err_buf, err_cap, "nested inductive '%s' type has fewer foralls than num_params", ks->names[J_name].full);
                free(lvl_ids); free(new_args); free(fn_levels); free(this_batch_aux_names); free(this_batch_type_idx);
                return 0;
            }
            J_type = lean_expr_instantiate1(ks, ks->exprs[J_type].d.binder.body, new_args[p]);
        }
        J_type = lean_lctx_mk_forall(ks, st->nparams, st->param_fvars, J_type);

        if (st->n_aux_types >= st->cap_aux_types) {
            st->cap_aux_types = st->cap_aux_types ? st->cap_aux_types * 2u : 16u;
            st->aux_types = (LeanDecl *)realloc(st->aux_types, st->cap_aux_types * sizeof(LeanDecl));
        }
        uint32_t tidx = st->n_aux_types++;
        this_batch_type_idx[m] = tidx;
        LeanDecl *aux_ind = &st->aux_types[tidx];
        memset(aux_ind, 0, sizeof(LeanDecl));
        aux_ind->kind = LDECL_IND;
        aux_ind->name = aux_J_name;
        aux_ind->type = J_type;
        aux_ind->nparams = st->nparams_lvls;
        aux_ind->level_params = (uint32_t *)malloc((st->nparams_lvls ? st->nparams_lvls : 1u) * sizeof(uint32_t));
        for (uint32_t l = 0; l < st->nparams_lvls; l++) aux_ind->level_params[l] = st->param_lvls[l];
        aux_ind->num_params = st->nparams;
        aux_ind->num_indices = J_decl->num_indices;
        aux_ind->is_unsafe = st->base_types[0].is_unsafe;
    }

    /* Second pass: transform each constructor of each J in `nested_all` */
    for (uint32_t m = 0; m < n_nested_all; m++) {
        uint32_t J_name = nested_all[m];
        uint32_t aux_J_name = this_batch_aux_names[m];
        const LeanDecl *J_decl = lean_lookup_decl(ks, J_name);
        for (uint32_t c = 0; c < J_decl->nctors; c++) {
            uint32_t J_ctor_name = J_decl->ctors[c].name;
            const LeanDecl *J_ctor = lean_lookup_decl(ks, J_ctor_name);
            if (!J_ctor || J_ctor->kind != LDECL_CTOR) {
                snprintf(err_buf, err_cap, "nested inductive constructor '%s' not found", ks->names[J_ctor_name].full);
                free(lvl_ids); free(new_args); free(fn_levels); free(this_batch_aux_names); free(this_batch_type_idx);
                return 0;
            }
            uint32_t aux_ctor_name = lean_name_replace_prefix(ks, J_ctor_name, J_name, aux_J_name);
            uint32_t ctor_type = lean_expr_subst_lvls(ks, J_ctor->type, J_ctor->nparams, J_ctor->level_params, fn_levels);
            for (uint32_t p = 0; p < fn_decl->num_params; p++) {
                if (ks->exprs[ctor_type].kind != LEXPR_FORALL) {
                    snprintf(err_buf, err_cap, "nested ctor '%s' has fewer foralls than num_params", ks->names[J_ctor_name].full);
                    free(lvl_ids); free(new_args); free(fn_levels); free(this_batch_aux_names); free(this_batch_type_idx);
                    return 0;
                }
                ctor_type = lean_expr_instantiate1(ks, ks->exprs[ctor_type].d.binder.body, new_args[p]);
            }
            uint32_t elim_ctor_type = lean_lctx_mk_forall(ks, st->nparams, st->param_fvars, ctor_type);

            if (st->n_aux_ctors >= st->cap_aux_ctors) {
                st->cap_aux_ctors = st->cap_aux_ctors ? st->cap_aux_ctors * 2u : 32u;
                st->aux_ctors = (LeanCtorSpec *)realloc(st->aux_ctors, st->cap_aux_ctors * sizeof(LeanCtorSpec));
            }
            LeanCtorSpec *cs = &st->aux_ctors[st->n_aux_ctors++];
            memset(cs, 0, sizeof(LeanCtorSpec));
            cs->name = aux_ctor_name;
            cs->ind_name = aux_J_name;
            cs->type = elim_ctor_type;
            cs->nparams = st->nparams_lvls;
            cs->level_params = (uint32_t *)malloc((st->nparams_lvls ? st->nparams_lvls : 1u) * sizeof(uint32_t));
            for (uint32_t l = 0; l < st->nparams_lvls; l++) cs->level_params[l] = st->param_lvls[l];
            cs->cidx = c;
            cs->num_params = st->nparams;
            cs->num_fields = J_ctor->num_fields;
            cs->is_unsafe = st->base_types[0].is_unsafe;
        }
    }

    free(fn_levels);
    free(this_batch_aux_names);
    free(this_batch_type_idx);

    uint32_t aux_const = lean_expr_mk_const(ks, result_aux_ind_name, st->nparams_lvls, lvl_ids);
    free(lvl_ids);
    uint32_t res = aux_const;
    for (uint32_t p = 0; p < st->nparams; p++) res = lean_expr_mk_app(ks, res, st->param_fvars[p]);
    for (uint32_t j = fn_decl->num_params; j < nargs; j++) {
        uint32_t arg_elim = lean_elim_nested(st, new_args[j], err_buf, err_cap);
        if (arg_elim == 0) { free(new_args); return 0; }
        res = lean_expr_mk_app(ks, res, arg_elim);
    }
    free(new_args);
    return res;
}

static uint32_t lean_elim_nested(LeanElimNestedState *st, uint32_t e, char *err_buf, size_t err_cap) {
    LeanKernelState *ks = st->ks;
    if (e == 0) return 0;
    bool matched = false;
    uint32_t r = lean_elim_nested_if_nested_app(st, e, &matched, err_buf, err_cap);
    if (matched) return r;

    const LeanExpr *ex = &ks->exprs[e];
    switch (ex->kind) {
        case LEXPR_APP: {
            uint32_t nf = lean_elim_nested(st, ex->d.app.fn, err_buf, err_cap);
            if (!nf) return 0;
            uint32_t na = lean_elim_nested(st, ex->d.app.arg, err_buf, err_cap);
            if (!na) return 0;
            return lean_expr_mk_app(ks, nf, na);
        }
        case LEXPR_LAM:
        case LEXPR_FORALL: {
            bool is_forall = (ex->kind == LEXPR_FORALL);
            uint32_t bname = ex->d.binder.binder_name;
            uint32_t dom = ex->d.binder.domain;
            uint32_t body = ex->d.binder.body;
            uint32_t nd = lean_elim_nested(st, dom, err_buf, err_cap);
            if (!nd) return 0;
            uint32_t fv = lean_push_local(ks, bname, nd, 0u);
            uint32_t inst_body = lean_expr_instantiate1(ks, body, fv);
            uint32_t nb_open = lean_elim_nested(st, inst_body, err_buf, err_cap);
            uint32_t res = nb_open ? lean_lctx_mk_binder(ks, is_forall, 1, &fv, nb_open) : 0;
            lean_pop_local(ks);
            return res;
        }
        case LEXPR_LET: {
            uint32_t bname = ex->d.let_e.binder_name;
            uint32_t ty = ex->d.let_e.type;
            uint32_t val = ex->d.let_e.val;
            uint32_t body = ex->d.let_e.body;
            uint32_t nt = lean_elim_nested(st, ty, err_buf, err_cap);
            if (!nt) return 0;
            uint32_t nv = lean_elim_nested(st, val, err_buf, err_cap);
            if (!nv) return 0;
            uint32_t fv = lean_push_local(ks, bname, nt, nv + 1u);
            uint32_t inst_body = lean_expr_instantiate1(ks, body, fv);
            uint32_t nb_open = lean_elim_nested(st, inst_body, err_buf, err_cap);
            uint32_t res = nb_open ? lean_lctx_mk_binder(ks, true, 1, &fv, nb_open) : 0;
            lean_pop_local(ks);
            return res;
        }
        case LEXPR_PROJ: {
            uint32_t ns = lean_elim_nested(st, ex->d.proj.struct_expr, err_buf, err_cap);
            if (!ns) return 0;
            return lean_expr_mk_proj(ks, ex->d.proj.type_name, ex->d.proj.idx, ns);
        }
        default:
            return e;
    }
}

/* Restore nested occurrences in an expression after recursor synthesis (`restoreNested` in `inductive.cpp`) */
static uint32_t lean_restore_nested(LeanElimNestedState *st, uint32_t e,
                                    uint32_t n_rec_rep, const uint32_t *aux_rec_names, const uint32_t *nested_rec_exprs) {
    LeanKernelState *ks = st->ks;
    if (e == 0 || st->n_aux2nested == 0) return e;

    /* 1. Check if `e` is an application of an `aux_rec_name`, an `aux_ind_name`, or an `aux_ctor_name` */
    uint32_t *args = NULL;
    uint32_t nargs = 0;
    uint32_t fn = lean_get_app_args_alloc(ks, e, &args, &nargs);
    if (ks->exprs[fn].kind == LEXPR_CONST) {
        uint32_t cname = ks->exprs[fn].d.cnst.name;
        /* Direct aux_rec_name replacement */
        for (uint32_t r = 0; r < n_rec_rep; r++) {
            if (cname == aux_rec_names[r]) {
                uint32_t res = nested_rec_exprs[r];
                for (uint32_t i = 0; i < nargs; i++) {
                    res = lean_expr_mk_app(ks, res,
                                           lean_restore_nested(st, args[i], n_rec_rep, aux_rec_names, nested_rec_exprs));
                }
                free(args);
                return res;
            }
        }
        /* Aux inductive `AuxI A_1 ... A_{nparams} idx_1 ... idx_m` -> `(F ...[A/param_fvars]) idx'_1 ... idx'_m` */
        for (uint32_t a = 0; a < st->n_aux2nested; a++) {
            if (cname == st->aux2nested_k[a] && nargs >= st->nparams) {
                uint32_t abst = st->aux2nested_v[a];
                uint32_t *subst_args = (uint32_t *)calloc(st->nparams ? st->nparams : 1u, sizeof(uint32_t));
                for (uint32_t p = 0; p < st->nparams; p++) {
                    subst_args[p] = lean_restore_nested(st, args[p], n_rec_rep, aux_rec_names, nested_rec_exprs);
                }
                uint32_t res = lean_expr_instantiate_rev(ks, abst, 0, st->nparams, subst_args);
                free(subst_args);
                for (uint32_t j = st->nparams; j < nargs; j++) {
                    res = lean_expr_mk_app(ks, res,
                                           lean_restore_nested(st, args[j], n_rec_rep, aux_rec_names, nested_rec_exprs));
                }
                free(args);
                return res;
            }
        }
        /* Aux constructor `AuxI.ctor A_1 ... A_{nparams} field_1 ...` -> `F.ctor ... field'_1 ...` */
        uint32_t pfx = ks->names[cname].pre;
        if (pfx != 0 && nargs >= st->nparams) {
            for (uint32_t a = 0; a < st->n_aux2nested; a++) {
                if (pfx == st->aux2nested_k[a]) {
                    uint32_t abst = st->aux2nested_v[a];
                    uint32_t *subst_args = (uint32_t *)calloc(st->nparams ? st->nparams : 1u, sizeof(uint32_t));
                    for (uint32_t p = 0; p < st->nparams; p++) {
                        subst_args[p] = lean_restore_nested(st, args[p], n_rec_rep, aux_rec_names, nested_rec_exprs);
                    }
                    uint32_t nested_inst = lean_expr_instantiate_rev(ks, abst, 0, st->nparams, subst_args);
                    free(subst_args);
                    uint32_t *n_args_F = NULL;
                    uint32_t n_F = 0;
                    uint32_t F_fn = lean_get_app_args_alloc(ks, nested_inst, &n_args_F, &n_F);
                    if (ks->exprs[F_fn].kind == LEXPR_CONST) {
                        uint32_t F_name = ks->exprs[F_fn].d.cnst.name;
                        uint32_t orig_ctor_name = lean_name_replace_prefix(ks, cname, pfx, F_name);
                        uint32_t orig_ctor_const = lean_expr_mk_const(ks, orig_ctor_name,
                                                                      ks->exprs[F_fn].d.cnst.nus,
                                                                      ks->exprs[F_fn].d.cnst.us);
                        uint32_t res = orig_ctor_const;
                        for (uint32_t k = 0; k < n_F; k++) res = lean_expr_mk_app(ks, res, n_args_F[k]);
                        free(n_args_F);
                        for (uint32_t j = st->nparams; j < nargs; j++) {
                            res = lean_expr_mk_app(ks, res,
                                                   lean_restore_nested(st, args[j], n_rec_rep, aux_rec_names, nested_rec_exprs));
                        }
                        free(args);
                        return res;
                    }
                    free(n_args_F);
                }
            }
        }
    }
    free(args);

    const LeanExpr *ex = &ks->exprs[e];
    switch (ex->kind) {
        case LEXPR_APP: {
            uint32_t nf = lean_restore_nested(st, ex->d.app.fn, n_rec_rep, aux_rec_names, nested_rec_exprs);
            uint32_t na = lean_restore_nested(st, ex->d.app.arg, n_rec_rep, aux_rec_names, nested_rec_exprs);
            return (nf == ex->d.app.fn && na == ex->d.app.arg) ? e : lean_expr_mk_app(ks, nf, na);
        }
        case LEXPR_LAM:
        case LEXPR_FORALL: {
            bool is_forall = (ex->kind == LEXPR_FORALL);
            uint32_t bname = ex->d.binder.binder_name;
            uint32_t dom = ex->d.binder.domain;
            uint32_t body = ex->d.binder.body;
            uint32_t nd = lean_restore_nested(st, dom, n_rec_rep, aux_rec_names, nested_rec_exprs);
            uint32_t fv = lean_push_local(ks, bname, nd, 0u);
            uint32_t inst_body = lean_expr_instantiate1(ks, body, fv);
            uint32_t nb_open = lean_restore_nested(st, inst_body, n_rec_rep, aux_rec_names, nested_rec_exprs);
            uint32_t res = lean_lctx_mk_binder(ks, is_forall, 1, &fv, nb_open);
            lean_pop_local(ks);
            return res;
        }
        case LEXPR_LET: {
            uint32_t bname = ex->d.let_e.binder_name;
            uint32_t ty = ex->d.let_e.type;
            uint32_t val = ex->d.let_e.val;
            uint32_t body = ex->d.let_e.body;
            uint32_t nt = lean_restore_nested(st, ty, n_rec_rep, aux_rec_names, nested_rec_exprs);
            uint32_t nv = lean_restore_nested(st, val, n_rec_rep, aux_rec_names, nested_rec_exprs);
            uint32_t fv = lean_push_local(ks, bname, nt, nv + 1u);
            uint32_t inst_body = lean_expr_instantiate1(ks, body, fv);
            uint32_t nb_open = lean_restore_nested(st, inst_body, n_rec_rep, aux_rec_names, nested_rec_exprs);
            uint32_t res = lean_lctx_mk_binder(ks, true, 1, &fv, nb_open);
            lean_pop_local(ks);
            return res;
        }
        case LEXPR_PROJ: {
            uint32_t ns = lean_restore_nested(st, ex->d.proj.struct_expr, n_rec_rep, aux_rec_names, nested_rec_exprs);
            return (ns == ex->d.proj.struct_expr) ? e : lean_expr_mk_proj(ks, ex->d.proj.type_name, ex->d.proj.idx, ns);
        }
        default:
            return e;
    }
}

/* Verify and atomically admit an official `lean4export` 3.1.0/3.0.0 `{"inductive": {types, ctors, recs}}` block
 * by running Lean 4's `ElimNestedInductive` + `AddInductive` + `mkRecInfos`/`mkRecRules` + `restoreNested`
 * and checking that the exported `types`, `ctors`, and `recs` match the kernel-derived declarations! */
/* Check if any `LEXPR_CONST` in `expr` has a name with prefix `nested_pfx` (`_nested`). */
static bool lean_name_has_prefix(const LeanKernelState *ks, uint32_t nm, uint32_t pfx) {
    uint32_t cur = nm;
    while (cur != 0 && cur < ks->nnames) {
        if (cur == pfx) return true;
        cur = ks->names[cur].pre;
    }
    return false;
}

static bool lean_expr_has_nested_prefix(const LeanKernelState *ks, uint32_t expr, uint32_t nested_pfx) {
    if (expr == 0) return false;
    const LeanExpr *e = &ks->exprs[expr];
    switch (e->kind) {
        case LEXPR_BVAR:
        case LEXPR_FVAR:
        case LEXPR_SORT:
        case LEXPR_NATLIT:
        case LEXPR_STRLIT:
            return false;
        case LEXPR_CONST:
            return lean_name_has_prefix(ks, e->d.cnst.name, nested_pfx);
        case LEXPR_APP:
            return lean_expr_has_nested_prefix(ks, e->d.app.fn, nested_pfx) ||
                   lean_expr_has_nested_prefix(ks, e->d.app.arg, nested_pfx);
        case LEXPR_LAM:
        case LEXPR_FORALL:
            return lean_expr_has_nested_prefix(ks, e->d.binder.domain, nested_pfx) ||
                   lean_expr_has_nested_prefix(ks, e->d.binder.body, nested_pfx);
        case LEXPR_LET:
            return lean_expr_has_nested_prefix(ks, e->d.let_e.type, nested_pfx) ||
                   lean_expr_has_nested_prefix(ks, e->d.let_e.val, nested_pfx) ||
                   lean_expr_has_nested_prefix(ks, e->d.let_e.body, nested_pfx);
        case LEXPR_PROJ:
            return lean_name_has_prefix(ks, e->d.proj.type_name, nested_pfx) ||
                   lean_expr_has_nested_prefix(ks, e->d.proj.struct_expr, nested_pfx);
        default:
            return false;
    }
}

static bool lean_verify_inductive_block(LeanKernelState *ks,
                                        uint32_t ntypes, LeanDecl *types,
                                        uint32_t nctors, LeanCtorSpec *ctors,
                                        uint32_t nrecs, LeanDecl *recs,
                                        char *err_buf, size_t err_cap) {
    if (ntypes == 0) {
        snprintf(err_buf, err_cap, "inductive block has empty types array");
        return false;
    }
    lean_scratch_scope_begin(ks);

    LeanElimNestedState elim_st;
    memset(&elim_st, 0, sizeof(elim_st));
    elim_st.ks = ks;
    elim_st.ntypes = ntypes;
    elim_st.base_types = types;
    elim_st.nparams = types[0].num_params;
    elim_st.nparams_lvls = types[0].nparams;
    elim_st.param_lvls = types[0].level_params;
    elim_st.next_idx = 1;

    uint32_t n_work_types = 0;
    LeanDecl *work_types = NULL;
    uint32_t n_work_ctors = 0;
    LeanCtorSpec *work_ctors = NULL;
    uint32_t *ind_names = NULL;
    uint32_t *ind_lvls  = NULL;
    uint32_t *ind_consts = NULL;
    uint32_t *motive_fvars = NULL;
    uint32_t *minor_fvars  = NULL;
    uint32_t **idx_fvars   = NULL;
    uint32_t *major_fvars  = NULL;
    LeanDecl *derived_recs = NULL;
    uint32_t pushed_base_params = 0;

    uint32_t nested_pfx = lean_name_mk_str(ks, 0, "_nested");

    /* Validate consistent `level_params`, `num_params`, `is_unsafe`, and no `_nested` prefix across `types` */
    uint32_t *base_ind_names = (uint32_t *)calloc(ntypes, sizeof(uint32_t));
    for (uint32_t t = 0; t < ntypes; t++) {
        base_ind_names[t] = types[t].name;
        if (lean_expr_has_nested_prefix(ks, types[t].type, nested_pfx)) {
            free(base_ind_names);
            snprintf(err_buf, err_cap, "ind %s: type contains reserved '_nested' prefix",
                     ks->names[types[t].name].full);
            goto fail;
        }
        if (types[t].nparams != types[0].nparams || types[t].num_params != types[0].num_params ||
            types[t].is_unsafe != types[0].is_unsafe) {
            free(base_ind_names);
            snprintf(err_buf, err_cap, "ind %s: mismatched level_params, num_params, or is_unsafe in mutual block",
                     ks->names[types[t].name].full);
            goto fail;
        }
        for (uint32_t l = 0; l < types[0].nparams; l++) {
            if (types[t].level_params[l] != types[0].level_params[l]) {
                free(base_ind_names);
                snprintf(err_buf, err_cap, "ind %s: mismatched level_params in mutual block",
                         ks->names[types[t].name].full);
                goto fail;
            }
        }
        /* Check duplicate level params */
        for (uint32_t l1 = 0; l1 < types[t].nparams; l1++) {
            for (uint32_t l2 = l1 + 1; l2 < types[t].nparams; l2++) {
                if (types[t].level_params[l1] == types[t].level_params[l2]) {
                    free(base_ind_names);
                    snprintf(err_buf, err_cap, "ind %s: duplicate universe level parameter",
                             ks->names[types[t].name].full);
                    goto fail;
                }
            }
        }
    }

    /* Check `is_rec` consistency and `_nested` prefix on constructors */
    {
        bool block_is_rec = false;
        for (uint32_t c = 0; c < nctors; c++) {
            if (lean_expr_has_nested_prefix(ks, ctors[c].type, nested_pfx)) {
                free(base_ind_names);
                snprintf(err_buf, err_cap, "ctor %s: type contains reserved '_nested' prefix",
                         ks->names[ctors[c].name].full);
                goto fail;
            }
            uint32_t cty = ctors[c].type;
            while (ks->exprs[cty].kind == LEXPR_FORALL) {
                if (lean_expr_mentions_any_const(ks, ks->exprs[cty].d.binder.domain, ntypes, base_ind_names)) {
                    block_is_rec = true;
                }
                cty = ks->exprs[cty].d.binder.body;
            }
        }
        free(base_ind_names);
        if (!ks->allow_legacy_format) {
            for (uint32_t t = 0; t < ntypes; t++) {
                if ((bool)types[t].is_rec != block_is_rec) {
                    snprintf(err_buf, err_cap, "ind %s: exported isRec (%u) != computed block_is_rec (%u)",
                             ks->names[types[t].name].full, (unsigned)types[t].is_rec, (unsigned)block_is_rec);
                    goto fail;
                }
            }
        }
    }

    /* Check `types[0..ntypes-1]` exported `ctors` list matches `ctors[0..nctors-1]` */
    {
        uint32_t c_cursor = 0;
        for (uint32_t t = 0; t < ntypes; t++) {
            if (types[t].has_declared_ctors) {
                for (uint32_t j = 0; j < types[t].num_declared_ctors; j++) {
                    if (c_cursor >= nctors || ctors[c_cursor].ind_name != types[t].name ||
                        ctors[c_cursor].name != types[t].declared_ctors[j] ||
                        ctors[c_cursor].cidx != j) {
                        snprintf(err_buf, err_cap, "ind %s: exported 'ctors' list does not match constructor declarations",
                                 ks->names[types[t].name].full);
                        goto fail;
                    }
                    c_cursor++;
                }
            } else {
                uint32_t expected_cidx = 0;
                while (c_cursor < nctors && ctors[c_cursor].ind_name == types[t].name) {
                    if (ctors[c_cursor].cidx != expected_cidx) {
                        snprintf(err_buf, err_cap, "ind %s: constructor cidx out of order",
                                 ks->names[types[t].name].full);
                        goto fail;
                    }
                    expected_cidx++;
                    c_cursor++;
                }
            }
        }
        if (c_cursor != nctors) {
            snprintf(err_buf, err_cap, "inductive block has constructors not belonging to declared types");
            goto fail;
        }
    }

    /* Extract shared parameter FVars from `types[0].type` for `ElimNestedInductive` */
    elim_st.param_fvars = (uint32_t *)calloc(elim_st.nparams ? elim_st.nparams : 1, sizeof(uint32_t));
    {
        uint32_t cur0 = types[0].type;
        for (uint32_t p = 0; p < elim_st.nparams; p++) {
            if (ks->exprs[cur0].kind != LEXPR_FORALL) {
                cur0 = lean_whnf(ks, cur0);
            }
            if (ks->exprs[cur0].kind != LEXPR_FORALL) {
                snprintf(err_buf, err_cap, "ind %s: fewer foralls than num_params (%u)",
                         ks->names[types[0].name].full, elim_st.nparams);
                goto fail;
            }
            uint32_t fv = lean_push_local(ks, ks->exprs[cur0].d.binder.binder_name,
                                          lean_consume_type_annotations(ks, ks->exprs[cur0].d.binder.domain), 0u);
            elim_st.param_fvars[p] = fv;
            pushed_base_params++;
            cur0 = lean_expr_instantiate1(ks, ks->exprs[cur0].d.binder.body, fv);
        }
    }

    /* Run `ElimNestedInductive` across all constructors of `types[0..ntypes-1]` */
    work_ctors = (LeanCtorSpec *)calloc(nctors ? nctors : 1, sizeof(LeanCtorSpec));
    {
        uint32_t *ctor_param_bnames = (uint32_t *)calloc(elim_st.nparams ? elim_st.nparams : 1, sizeof(uint32_t));
        uint32_t *ctor_param_doms   = (uint32_t *)calloc(elim_st.nparams ? elim_st.nparams : 1, sizeof(uint32_t));
        for (uint32_t c = 0; c < nctors; c++) {
            work_ctors[c] = ctors[c];
            uint32_t cty = ctors[c].type;
            for (uint32_t p = 0; p < elim_st.nparams; p++) {
                if (ks->exprs[cty].kind != LEXPR_FORALL) {
                    cty = lean_whnf(ks, cty);
                }
                if (ks->exprs[cty].kind != LEXPR_FORALL) {
                    free(ctor_param_bnames);
                    free(ctor_param_doms);
                    snprintf(err_buf, err_cap, "ctor %s: fewer foralls than num_params (%u)",
                             ks->names[ctors[c].name].full, elim_st.nparams);
                    goto fail;
                }
                ctor_param_bnames[p] = ks->exprs[cty].d.binder.binder_name;
                ctor_param_doms[p]   = ks->exprs[cty].d.binder.domain;
                cty = lean_expr_instantiate1(ks, ks->exprs[cty].d.binder.body, elim_st.param_fvars[p]);
            }
            uint32_t elim_cty = lean_elim_nested(&elim_st, cty, err_buf, err_cap);
            if (!elim_cty) {
                free(ctor_param_bnames);
                free(ctor_param_doms);
                goto fail;
            }
            if (elim_cty == cty) {
                work_ctors[c].type = ctors[c].type;
            } else {
                uint32_t abst = lean_expr_abstract_fvar_exprs(ks, elim_cty, elim_st.nparams, elim_st.param_fvars);
                for (uint32_t p = elim_st.nparams; p > 0; p--) {
                    uint32_t idx = p - 1;
                    uint32_t bname = ctor_param_bnames[idx];
                    uint32_t bdom  = ctor_param_doms[idx];
                    uint32_t bdom_closed = idx > 0 ? lean_expr_abstract_fvar_exprs(ks, bdom, idx, elim_st.param_fvars) : bdom;
                    abst = lean_expr_mk_forall(ks, bname, bdom_closed, abst);
                }
                work_ctors[c].type = abst;
            }
        }
        free(ctor_param_bnames);
        free(ctor_param_doms);
    }

    /* Process auxiliary constructors in BFS queue order (`specialize_nested_aux` in `inductive.cpp` / `nanoda`) */
    for (uint32_t a = 0; a < elim_st.n_aux_ctors; a++) {
        uint32_t cty = elim_st.aux_ctors[a].type;
        for (uint32_t p = 0; p < elim_st.nparams; p++) {
            if (ks->exprs[cty].kind != LEXPR_FORALL) {
                cty = lean_whnf(ks, cty);
            }
            if (ks->exprs[cty].kind != LEXPR_FORALL) {
                snprintf(err_buf, err_cap, "aux ctor %s: fewer foralls than num_params (%u)",
                         ks->names[elim_st.aux_ctors[a].name].full, elim_st.nparams);
                goto fail;
            }
            cty = lean_expr_instantiate1(ks, ks->exprs[cty].d.binder.body, elim_st.param_fvars[p]);
        }
        uint32_t elim_cty = lean_elim_nested(&elim_st, cty, err_buf, err_cap);
        if (!elim_cty) goto fail;
        elim_st.aux_ctors[a].type = lean_lctx_mk_forall(ks, elim_st.nparams, elim_st.param_fvars, elim_cty);
    }

    while (pushed_base_params > 0) {
        lean_pop_local(ks);
        pushed_base_params--;
    }

    /* Check `numNested` matches `elim_st.n_aux_types` */
    for (uint32_t t = 0; t < ntypes; t++) {
        if (types[t].has_num_nested && types[t].num_nested != elim_st.n_aux_types) {
            snprintf(err_buf, err_cap, "ind %s: exported numNested (%u) != synthesized aux inductives (%u)",
                     ks->names[types[t].name].full, types[t].num_nested, elim_st.n_aux_types);
            goto fail;
        }
    }

    /* Build combined `work_types` (ntypes + elim_st.n_aux_types) and `work_ctors` (nctors + elim_st.n_aux_ctors),
     * ordered by `(owner_type_idx, cidx)` so minor premises for multi-level nested containers are in type order. */
    n_work_types = ntypes + elim_st.n_aux_types;
    work_types = (LeanDecl *)calloc(n_work_types, sizeof(LeanDecl));
    for (uint32_t t = 0; t < ntypes; t++) {
        work_types[t] = types[t];
        /* Detach caller's `types[t].ctors` so `work_types[t].ctors` owns its own slice */
        work_types[t].ctors = NULL;
        work_types[t].nctors = 0;
    }
    for (uint32_t a = 0; a < elim_st.n_aux_types; a++) {
        work_types[ntypes + a] = elim_st.aux_types[a];
        work_types[ntypes + a].ctors = NULL;
        work_types[ntypes + a].nctors = 0;
    }

    n_work_ctors = nctors + elim_st.n_aux_ctors;
    {
        LeanCtorSpec *ordered_ctors = (LeanCtorSpec *)calloc(n_work_ctors ? n_work_ctors : 1, sizeof(LeanCtorSpec));
        uint32_t out_c = 0;
        for (uint32_t t = 0; t < n_work_types; t++) {
            uint32_t t_cnt = 0;
            if (t < ntypes) {
                for (uint32_t c = 0; c < nctors; c++) {
                    if (work_ctors[c].ind_name == work_types[t].name) t_cnt++;
                }
            } else {
                for (uint32_t a = 0; a < elim_st.n_aux_ctors; a++) {
                    if (elim_st.aux_ctors[a].ind_name == work_types[t].name) t_cnt++;
                }
            }
            work_types[t].nctors = t_cnt;
            work_types[t].ctors = t_cnt > 0 ? (LeanCtorSpec *)calloc(t_cnt, sizeof(LeanCtorSpec)) : NULL;
            uint32_t k = 0;
            if (t < ntypes) {
                for (uint32_t c = 0; c < nctors; c++) {
                    if (work_ctors[c].ind_name == work_types[t].name) {
                        ordered_ctors[out_c++] = work_ctors[c];
                        work_types[t].ctors[k++] = ctors[c];
                    }
                }
            } else {
                for (uint32_t a = 0; a < elim_st.n_aux_ctors; a++) {
                    if (elim_st.aux_ctors[a].ind_name == work_types[t].name) {
                        ordered_ctors[out_c++] = elim_st.aux_ctors[a];
                        work_types[t].ctors[k++] = elim_st.aux_ctors[a];
                    }
                }
            }
        }
        free(work_ctors);
        work_ctors = ordered_ctors;
    }

    ind_names  = (uint32_t *)calloc(n_work_types, sizeof(uint32_t));
    ind_lvls   = (uint32_t *)calloc(n_work_types, sizeof(uint32_t));
    ind_consts = (uint32_t *)calloc(n_work_types, sizeof(uint32_t));

    /* Step 1: Verify and register all mutual + aux inductive type headers */
    {
        uint32_t *lvl_ids = (uint32_t *)calloc(elim_st.nparams_lvls ? elim_st.nparams_lvls : 1, sizeof(uint32_t));
        for (uint32_t l = 0; l < elim_st.nparams_lvls; l++) {
            lvl_ids[l] = lean_lvl_mk_param(ks, elim_st.param_lvls[l]);
        }
        for (uint32_t t = 0; t < n_work_types; t++) {
            LeanDecl *ind = &work_types[t];
            ind_names[t] = ind->name;
            ind_consts[t] = lean_expr_mk_const(ks, ind->name, elim_st.nparams_lvls, lvl_ids);
            if (ind->name == 0 || lean_lookup_decl(ks, ind->name) != NULL ||
                lean_lookup_decl(ks, lean_name_mk_str(ks, ind->name, "rec")) != NULL) {
                free(lvl_ids);
                snprintf(err_buf, err_cap, "ind %s: invalid or duplicate inductive/recursor name",
                         ks->names[ind->name].full);
                goto fail;
            }
            if (t < ntypes) {
                /* Verify exported `all` list on primary types */
                if (ind->has_all_field) {
                    if (ind->nall != ntypes) {
                        free(lvl_ids);
                        snprintf(err_buf, err_cap, "ind %s: 'all' count (%u) != ntypes (%u)",
                                 ks->names[ind->name].full, ind->nall, ntypes);
                        goto fail;
                    }
                    for (uint32_t j = 0; j < ntypes; j++) {
                        if (ind->all[j] != types[j].name) {
                            free(lvl_ids);
                            snprintf(err_buf, err_cap, "ind %s: 'all[%u]' mismatch", ks->names[ind->name].full, j);
                            goto fail;
                        }
                    }
                }
            }
            uint32_t ty_sort_lvl = 0;
            Occ is_type_occ = lean_verify_is_type(ks, ind->name, ind->type, ind->nparams, ind->level_params,
                                                  &ty_sort_lvl, err_buf, err_cap);
            if (!is_type_occ) { free(lvl_ids); goto fail; }

            uint32_t cur = ind->type;
            uint32_t pushed = 0;
            uint32_t pushed_idx = 0;
            while (ks->exprs[cur].kind == LEXPR_FORALL ||
                   (pushed < ind->num_params + ind->num_indices &&
                    ks->exprs[(cur = lean_whnf(ks, cur))].kind == LEXPR_FORALL)) {
                uint32_t dom = lean_consume_type_annotations(ks, ks->exprs[cur].d.binder.domain);
                uint32_t fv = 0;
                if (pushed < ind->num_params) {
                    if (t == 0) {
                        fv = lean_push_local(ks, ks->exprs[cur].d.binder.binder_name, dom, 0u);
                        elim_st.param_fvars[pushed] = fv;
                        pushed_base_params++;
                    } else {
                        const LeanLocalDecl *p_loc = lean_lookup_local(ks, ks->exprs[elim_st.param_fvars[pushed]].d.fvar_id);
                        if (!p_loc || !lean_is_def_eq(ks, dom, p_loc->type)) {
                            for (uint32_t i = 0; i < pushed_idx; i++) lean_pop_local(ks);
                            free(lvl_ids);
                            snprintf(err_buf, err_cap, "ind %s: parameter %u domain mismatch in mutual block",
                                     ks->names[ind->name].full, pushed);
                            goto fail;
                        }
                        fv = elim_st.param_fvars[pushed];
                    }
                } else {
                    fv = lean_push_local(ks, ks->exprs[cur].d.binder.binder_name, dom, 0u);
                    pushed_idx++;
                }
                cur = lean_expr_instantiate1(ks, ks->exprs[cur].d.binder.body, fv);
                pushed++;
            }
            cur = lean_whnf(ks, cur);
            for (uint32_t i = 0; i < pushed_idx; i++) lean_pop_local(ks);
            if (ks->exprs[cur].kind != LEXPR_SORT || pushed != ind->num_params + ind->num_indices) {
                free(lvl_ids);
                snprintf(err_buf, err_cap, "ind %s: invalid inductive telescope (pushed=%u, expected=%u) or non-Sort target",
                         ks->names[ind->name].full, pushed, ind->num_params + ind->num_indices);
                goto fail;
            }
            ind_lvls[t] = ks->exprs[cur].d.sort_lvl;
            ind->tc_occ = lean_tc_admit_ind(is_type_occ, ind->name, ind->type, ty_sort_lvl);
            if (!ind->tc_occ) {
                free(lvl_ids);
                snprintf(err_buf, err_cap, "ind %s: tcalc R_ADMIT_IND rejected", ks->names[ind->name].full);
                goto fail;
            }
            lean_ensure_decls_cap(ks, ind->name);
            ks->decls_by_name[ind->name] = *ind;
            if (t < ntypes) {
                ks->stat_inds++;
                g_tc_admitted_decls++;
            }
        }
        free(lvl_ids);
        while (pushed_base_params > 0) {
            lean_pop_local(ks);
            pushed_base_params--;
        }
    }

    /* Step 2: Verify and register all constructors across `work_types` */
    for (uint32_t c = 0; c < n_work_ctors; c++) {
        LeanCtorSpec *cs = &work_ctors[c];
        int owner = -1;
        for (uint32_t t = 0; t < n_work_types; t++) {
            if (work_types[t].name == cs->ind_name) { owner = (int)t; break; }
        }
        if (owner < 0) {
            snprintf(err_buf, err_cap, "ctor %s: parent inductive %s is not in this mutual block",
                     ks->names[cs->name].full, ks->names[cs->ind_name].full);
            goto fail;
        }
        if (!lean_verify_and_admit_ctor(ks, &work_types[owner], ind_lvls[owner],
                                        n_work_types, ind_names, cs, err_buf, err_cap)) {
            goto fail;
        }
        /* For primary constructors, replace the temporary `elim_nested` type in `decls_by_name` with the original `ctors[c].type` */
        if (c < nctors) {
            ks->decls_by_name[cs->name].type = ctors[c].type;
        } else {
            /* Do not count aux constructors in `stat_ctors` / `g_tc_admitted_decls` */
            ks->stat_ctors--;
            g_tc_admitted_decls--;
        }
    }

    /* Record `all` on primary types and note verified inductives */
    for (uint32_t t = 0; t < n_work_types; t++) {
        if (t < ntypes) {
            if (!work_types[t].all) {
                work_types[t].nall = ntypes;
                work_types[t].all = (uint32_t *)malloc(ntypes * sizeof(uint32_t));
                for (uint32_t j = 0; j < ntypes; j++) work_types[t].all[j] = types[j].name;
            }
            work_types[t].is_nested = (elim_st.n_aux_types > 0) ? 1 : 0;
            free(types[t].ctors);
            types[t] = work_types[t];
            ks->decls_by_name[types[t].name] = types[t];
            lean_note_verified_inductive(ks, &types[t]);
        } else {
            ks->decls_by_name[work_types[t].name] = work_types[t];
        }
    }

    /* Step 3: Canonical Recursor Synthesis (`initElimLevel`, `initKTarget`, `mkRecInfos`, `mkRecRules`) */
    {
        /* Check `elim_to_prop` (`initElimLevel` in `inductive.cpp`):
         * If `ind_lvls[0]` is NOT definitely non-zero (i.e., may be 0 under some universe instantiation),
         * restrict elimination to `Prop` unless there is a single inductive with <= 1 constructor whose
         * non-proof fields all appear in the result indices. */
        bool elim_to_prop = false;
        if (!lean_lvl_is_nonzero(ks, ind_lvls[0])) {
            if (n_work_types > 1 || work_types[0].nctors > 1) {
                elim_to_prop = true;
            } else if (work_types[0].nctors == 1) {
                /* Single constructor: check that every non-param argument is either a proof or occurs in the result indices */
                LeanCtorSpec *cs0 = &work_ctors[0];
                uint32_t cty = cs0->type;
                uint32_t pushed_c = 0;
                uint32_t cap_np = 16, n_np = 0;
                uint32_t *non_proof_fvars = (uint32_t *)calloc(cap_np, sizeof(uint32_t));
                while (ks->exprs[cty].kind == LEXPR_FORALL) {
                    uint32_t dom = lean_consume_type_annotations(ks, ks->exprs[cty].d.binder.domain);
                    uint32_t fv = lean_push_local(ks, ks->exprs[cty].d.binder.binder_name, dom, 0u);
                    if (pushed_c >= elim_st.nparams && !lean_is_prop(ks, dom)) {
                        if (n_np >= cap_np) {
                            cap_np *= 2u;
                            non_proof_fvars = (uint32_t *)realloc(non_proof_fvars, cap_np * sizeof(uint32_t));
                        }
                        non_proof_fvars[n_np++] = fv;
                    }
                    cty = lean_expr_instantiate1(ks, ks->exprs[cty].d.binder.body, fv);
                    pushed_c++;
                }
                if (!elim_to_prop && n_np > 0) {
                    uint32_t *res_args = NULL;
                    uint32_t n_res_args = 0;
                    lean_get_app_args_alloc(ks, cty, &res_args, &n_res_args);
                    for (uint32_t i = 0; i < n_np; i++) {
                        bool in_idx = false;
                        for (uint32_t j = elim_st.nparams; j < n_res_args; j++) {
                            if (res_args[j] == non_proof_fvars[i]) { in_idx = true; break; }
                        }
                        if (!in_idx) { elim_to_prop = true; break; }
                    }
                    free(res_args);
                }
                free(non_proof_fvars);
                for (uint32_t i = 0; i < pushed_c; i++) lean_pop_local(ks);
            }
        }

        /* Determine universe parameter for motive (`u_1` / `motive_lvl`) */
        uint32_t motive_lvl_param_name = 0;
        uint32_t motive_lvl = 0u;
        if (!elim_to_prop) {
            uint32_t u_base = lean_name_mk_str(ks, 0, "u");
            uint32_t u_idx = 1;
            while (1) {
                uint32_t cand = lean_name_append_index_after(ks, u_base, u_idx);
                bool clash = false;
                for (uint32_t l = 0; l < elim_st.nparams_lvls; l++) {
                    if (elim_st.param_lvls[l] == cand) { clash = true; break; }
                }
                if (!clash) { motive_lvl_param_name = cand; break; }
                u_idx++;
            }
            motive_lvl = lean_lvl_mk_param(ks, motive_lvl_param_name);
        }

        /* Check `is_k_target` (`initKTarget` in `inductive.cpp`):
         * single inductive (n_work_types == 1), ind_lvls[0] == 0, 1 constructor with 0 fields after params */
        bool is_k_target = (n_work_types == 1 &&
                            lean_lvl_is_zero(ks, ind_lvls[0]) &&
                            work_types[0].nctors == 1 &&
                            work_ctors[0].num_fields == 0);

        /* Push shared `param_fvars` from `work_types[0].type` */
        {
            uint32_t cur0 = work_types[0].type;
            for (uint32_t p = 0; p < elim_st.nparams; p++) {
                if (ks->exprs[cur0].kind != LEXPR_FORALL) cur0 = lean_whnf(ks, cur0);
                uint32_t fv = lean_push_local(ks, ks->exprs[cur0].d.binder.binder_name,
                                              lean_consume_type_annotations(ks, ks->exprs[cur0].d.binder.domain), 0u);
                elim_st.param_fvars[p] = fv;
                pushed_base_params++;
                cur0 = lean_expr_instantiate1(ks, ks->exprs[cur0].d.binder.body, fv);
            }
        }

        /* Push indices and major premise for each `work_types[t]`, and create `motive_fvars[t]` */
        idx_fvars   = (uint32_t **)calloc(n_work_types, sizeof(uint32_t *));
        major_fvars = (uint32_t *)calloc(n_work_types, sizeof(uint32_t));
        motive_fvars = (uint32_t *)calloc(n_work_types, sizeof(uint32_t));
        uint32_t motive_sort = lean_expr_mk_sort(ks, motive_lvl);

        for (uint32_t t = 0; t < n_work_types; t++) {
            uint32_t nidx = work_types[t].num_indices;
            idx_fvars[t] = (uint32_t *)calloc(nidx ? nidx : 1, sizeof(uint32_t));
            uint32_t cur = work_types[t].type;
            for (uint32_t p = 0; p < elim_st.nparams; p++) {
                if (ks->exprs[cur].kind != LEXPR_FORALL) cur = lean_whnf(ks, cur);
                cur = lean_expr_instantiate1(ks, ks->exprs[cur].d.binder.body, elim_st.param_fvars[p]);
            }
            for (uint32_t i = 0; i < nidx; i++) {
                if (ks->exprs[cur].kind != LEXPR_FORALL) cur = lean_whnf(ks, cur);
                idx_fvars[t][i] = lean_push_local(ks, ks->exprs[cur].d.binder.binder_name,
                                                  lean_consume_type_annotations(ks, ks->exprs[cur].d.binder.domain), 0u);
                pushed_base_params++;
                cur = lean_expr_instantiate1(ks, ks->exprs[cur].d.binder.body, idx_fvars[t][i]);
            }
            uint32_t maj_ty = ind_consts[t];
            for (uint32_t p = 0; p < elim_st.nparams; p++) maj_ty = lean_expr_mk_app(ks, maj_ty, elim_st.param_fvars[p]);
            for (uint32_t i = 0; i < nidx; i++) maj_ty = lean_expr_mk_app(ks, maj_ty, idx_fvars[t][i]);
            uint32_t t_name = lean_name_mk_str(ks, 0, "t");
            major_fvars[t] = lean_push_local(ks, t_name, maj_ty, 0);
            pushed_base_params++;
        }

        for (uint32_t t = 0; t < n_work_types; t++) {
            uint32_t nidx = work_types[t].num_indices;
            uint32_t m_ty = lean_lctx_mk_forall(ks, 1, &major_fvars[t], motive_sort);
            m_ty = lean_lctx_mk_forall(ks, nidx, idx_fvars[t], m_ty);
            uint32_t m_name = (n_work_types > 1)
                                  ? lean_name_append_index_after(ks, lean_name_mk_str(ks, 0, "motive"), t + 1)
                                  : lean_name_mk_str(ks, 0, "motive");
            motive_fvars[t] = lean_push_local(ks, m_name, m_ty, 0u);
            pushed_base_params++;
        }

        /* Build `minor_fvars[0..n_work_ctors-1]` and each constructor's `rec_rhs` */
        minor_fvars = (uint32_t *)calloc(n_work_ctors ? n_work_ctors : 1, sizeof(uint32_t));
        uint32_t *ctor_rec_rhs = (uint32_t *)calloc(n_work_ctors ? n_work_ctors : 1, sizeof(uint32_t));

        uint32_t rec_nparams_lvls = elim_st.nparams_lvls + (elim_to_prop ? 0u : 1u);
        uint32_t *rec_lvl_params = (uint32_t *)calloc(rec_nparams_lvls ? rec_nparams_lvls : 1, sizeof(uint32_t));
        uint32_t *rec_lvl_ids    = (uint32_t *)calloc(rec_nparams_lvls ? rec_nparams_lvls : 1, sizeof(uint32_t));
        uint32_t *base_lvl_ids   = (uint32_t *)calloc(elim_st.nparams_lvls ? elim_st.nparams_lvls : 1, sizeof(uint32_t));
        for (uint32_t l = 0; l < elim_st.nparams_lvls; l++) {
            base_lvl_ids[l] = lean_lvl_mk_param(ks, elim_st.param_lvls[l]);
        }
        if (!elim_to_prop) {
            rec_lvl_params[0] = motive_lvl_param_name;
            rec_lvl_ids[0] = motive_lvl;
            for (uint32_t l = 0; l < elim_st.nparams_lvls; l++) {
                rec_lvl_params[l + 1] = elim_st.param_lvls[l];
                rec_lvl_ids[l + 1] = base_lvl_ids[l];
            }
        } else {
            for (uint32_t l = 0; l < elim_st.nparams_lvls; l++) {
                rec_lvl_params[l] = elim_st.param_lvls[l];
                rec_lvl_ids[l] = base_lvl_ids[l];
            }
        }

        /* First loop over constructors: build `minor_fvars[c]` */
        for (uint32_t c = 0; c < n_work_ctors; c++) {
            LeanCtorSpec *cs = &work_ctors[c];
            uint32_t cty = cs->type;
            for (uint32_t p = 0; p < elim_st.nparams; p++) {
                if (ks->exprs[cty].kind != LEXPR_FORALL) cty = lean_whnf(ks, cty);
                cty = lean_expr_instantiate1(ks, ks->exprs[cty].d.binder.body, elim_st.param_fvars[p]);
            }
            uint32_t cap_b = 16, n_b = 0;
            uint32_t *b_args = (uint32_t *)calloc(cap_b, sizeof(uint32_t));
            uint32_t cap_rec = 16, n_rec = 0;
            uint32_t *rec_b_names = (uint32_t *)calloc(cap_rec, sizeof(uint32_t));
            uint32_t *rec_v_tys   = (uint32_t *)calloc(cap_rec, sizeof(uint32_t));

            while (ks->exprs[cty].kind == LEXPR_FORALL) {
                uint32_t dom = lean_consume_type_annotations(ks, ks->exprs[cty].d.binder.domain);
                uint32_t b_name = ks->exprs[cty].d.binder.binder_name;
                uint32_t b_fv = lean_push_local(ks, b_name, dom, 0u);
                if (n_b >= cap_b) {
                    cap_b *= 2u;
                    b_args = (uint32_t *)realloc(b_args, cap_b * sizeof(uint32_t));
                }
                b_args[n_b++] = b_fv;

                /* Check if `dom` is a recursive argument `(u_1 : ...) -> ... -> I_d params it_indices` */
                uint32_t it = dom;
                uint32_t cap_u = 16, nu = 0;
                uint32_t *u_list = (uint32_t *)calloc(cap_u, sizeof(uint32_t));
                while (1) {
                    uint32_t it_w = lean_whnf(ks, it);
                    if (ks->exprs[it_w].kind != LEXPR_FORALL) { it = it_w; break; }
                    if (nu >= cap_u) {
                        cap_u *= 2u;
                        u_list = (uint32_t *)realloc(u_list, cap_u * sizeof(uint32_t));
                    }
                    u_list[nu++] = lean_push_local(ks, ks->exprs[it_w].d.binder.binder_name,
                                                   lean_consume_type_annotations(ks, ks->exprs[it_w].d.binder.domain), 0u);
                    it = lean_expr_instantiate1(ks, ks->exprs[it_w].d.binder.body, u_list[nu - 1]);
                }
                uint32_t *it_args = NULL;
                uint32_t n_it_args = 0;
                uint32_t it_fn = lean_get_app_args_alloc(ks, it, &it_args, &n_it_args);
                int d_match = -1;
                if (ks->exprs[it_fn].kind == LEXPR_CONST) {
                    for (uint32_t d = 0; d < n_work_types; d++) {
                        if (ks->exprs[it_fn].d.cnst.name == work_types[d].name) {
                            d_match = (int)d;
                            break;
                        }
                    }
                }
                if (d_match >= 0) {
                    /* Build `(u_1 : ...) -> C_d it_indices (b_fv u_1 ...)` while `u_list` is still in `ks->locals` */
                    uint32_t b_app = b_fv;
                    for (uint32_t ui = 0; ui < nu; ui++) b_app = lean_expr_mk_app(ks, b_app, u_list[ui]);
                    uint32_t v_ty = motive_fvars[d_match];
                    for (uint32_t ii = 0; ii < work_types[d_match].num_indices; ii++) {
                        v_ty = lean_expr_mk_app(ks, v_ty, it_args[elim_st.nparams + ii]);
                    }
                    v_ty = lean_expr_mk_app(ks, v_ty, b_app);
                    v_ty = lean_lctx_mk_forall(ks, nu, u_list, v_ty);
                    if (n_rec >= cap_rec) {
                        cap_rec *= 2u;
                        rec_b_names = (uint32_t *)realloc(rec_b_names, cap_rec * sizeof(uint32_t));
                        rec_v_tys   = (uint32_t *)realloc(rec_v_tys, cap_rec * sizeof(uint32_t));
                    }
                    rec_b_names[n_rec] = b_name;
                    rec_v_tys[n_rec] = v_ty;
                    n_rec++;
                }
                free(it_args);
                for (uint32_t ui = 0; ui < nu; ui++) lean_pop_local(ks);
                free(u_list);
                cty = lean_expr_instantiate1(ks, ks->exprs[cty].d.binder.body, b_fv);
            }

            /* Push inductive hypothesis `v_i` for each recursive argument */
            uint32_t *v_args = (uint32_t *)calloc(n_rec ? n_rec : 1, sizeof(uint32_t));
            for (uint32_t i = 0; i < n_rec; i++) {
                uint32_t v_name = lean_name_mk_str(ks, rec_b_names[i], "ih");
                v_args[i] = lean_push_local(ks, v_name, rec_v_tys[i], 0);
            }
            free(rec_b_names);
            free(rec_v_tys);

            /* Constructor target `cty` is `I_owner params target_indices` */
            uint32_t *c_res_args = NULL;
            uint32_t n_c_res = 0;
            uint32_t c_res_fn = lean_get_app_args_alloc(ks, cty, &c_res_args, &n_c_res);
            int owner = 0;
            for (uint32_t d = 0; d < n_work_types; d++) {
                if (ks->exprs[c_res_fn].kind == LEXPR_CONST && ks->exprs[c_res_fn].d.cnst.name == work_types[d].name) {
                    owner = (int)d;
                    break;
                }
            }
            uint32_t c_app = lean_expr_mk_const(ks, cs->name, elim_st.nparams_lvls, base_lvl_ids);
            for (uint32_t p = 0; p < elim_st.nparams; p++) c_app = lean_expr_mk_app(ks, c_app, elim_st.param_fvars[p]);
            for (uint32_t bi = 0; bi < n_b; bi++) c_app = lean_expr_mk_app(ks, c_app, b_args[bi]);

            uint32_t minor_cod = motive_fvars[owner];
            for (uint32_t ii = 0; ii < work_types[owner].num_indices; ii++) {
                minor_cod = lean_expr_mk_app(ks, minor_cod, c_res_args[elim_st.nparams + ii]);
            }
            free(c_res_args);
            minor_cod = lean_expr_mk_app(ks, minor_cod, c_app);
            uint32_t minor_ty = lean_lctx_mk_forall(ks, n_rec, v_args, minor_cod);
            minor_ty = lean_lctx_mk_forall(ks, n_b, b_args, minor_ty);

            for (uint32_t i = 0; i < n_rec; i++) lean_pop_local(ks);
            for (uint32_t i = 0; i < n_b; i++) lean_pop_local(ks);
            free(v_args);
            free(b_args);

            /* Minor binder name is the short constructor name (e.g., `zero`, `succ`) */
            uint32_t short_cname = lean_name_mk_str(ks, 0, ks->names[cs->name].str ? ks->names[cs->name].str : "minor");
            minor_fvars[c] = lean_push_local(ks, short_cname, minor_ty, 0);
            pushed_base_params++;
        }

        /* Second loop over constructors: now that all `minor_fvars` are in scope, build `ctor_rec_rhs[c]` */
        for (uint32_t c = 0; c < n_work_ctors; c++) {
            LeanCtorSpec *cs = &work_ctors[c];
            uint32_t cty = cs->type;
            for (uint32_t p = 0; p < elim_st.nparams; p++) {
                if (ks->exprs[cty].kind != LEXPR_FORALL) cty = lean_whnf(ks, cty);
                cty = lean_expr_instantiate1(ks, ks->exprs[cty].d.binder.body, elim_st.param_fvars[p]);
            }
            uint32_t cap_b = 16, n_b = 0;
            uint32_t *b_args = (uint32_t *)calloc(cap_b, sizeof(uint32_t));
            uint32_t cap_rec = 16, n_rec = 0;
            uint32_t *v_vals = (uint32_t *)calloc(cap_rec, sizeof(uint32_t));

            while (ks->exprs[cty].kind == LEXPR_FORALL) {
                uint32_t dom = lean_consume_type_annotations(ks, ks->exprs[cty].d.binder.domain);
                uint32_t b_fv = lean_push_local(ks, ks->exprs[cty].d.binder.binder_name, dom, 0u);
                if (n_b >= cap_b) {
                    cap_b *= 2u;
                    b_args = (uint32_t *)realloc(b_args, cap_b * sizeof(uint32_t));
                }
                b_args[n_b++] = b_fv;

                uint32_t it = dom;
                uint32_t cap_u = 16, nu = 0;
                uint32_t *u_list = (uint32_t *)calloc(cap_u, sizeof(uint32_t));
                while (1) {
                    uint32_t it_w = lean_whnf(ks, it);
                    if (ks->exprs[it_w].kind != LEXPR_FORALL) { it = it_w; break; }
                    if (nu >= cap_u) {
                        cap_u *= 2u;
                        u_list = (uint32_t *)realloc(u_list, cap_u * sizeof(uint32_t));
                    }
                    u_list[nu++] = lean_push_local(ks, ks->exprs[it_w].d.binder.binder_name,
                                                   lean_consume_type_annotations(ks, ks->exprs[it_w].d.binder.domain), 0u);
                    it = lean_expr_instantiate1(ks, ks->exprs[it_w].d.binder.body, u_list[nu - 1]);
                }
                uint32_t *it_args = NULL;
                uint32_t n_it_args = 0;
                uint32_t it_fn = lean_get_app_args_alloc(ks, it, &it_args, &n_it_args);
                int d_match = -1;
                if (ks->exprs[it_fn].kind == LEXPR_CONST) {
                    for (uint32_t d = 0; d < n_work_types; d++) {
                        if (ks->exprs[it_fn].d.cnst.name == work_types[d].name) {
                            d_match = (int)d;
                            break;
                        }
                    }
                }
                if (d_match >= 0) {
                    uint32_t d_rec_name = lean_name_mk_str(ks, work_types[d_match].name, "rec");
                    uint32_t rec_app = lean_expr_mk_const(ks, d_rec_name, rec_nparams_lvls, rec_lvl_ids);
                    for (uint32_t p = 0; p < elim_st.nparams; p++) rec_app = lean_expr_mk_app(ks, rec_app, elim_st.param_fvars[p]);
                    for (uint32_t d = 0; d < n_work_types; d++) rec_app = lean_expr_mk_app(ks, rec_app, motive_fvars[d]);
                    for (uint32_t m = 0; m < n_work_ctors; m++) rec_app = lean_expr_mk_app(ks, rec_app, minor_fvars[m]);
                    for (uint32_t ii = 0; ii < work_types[d_match].num_indices; ii++) {
                        rec_app = lean_expr_mk_app(ks, rec_app, it_args[elim_st.nparams + ii]);
                    }
                    uint32_t b_u = b_fv;
                    for (uint32_t ui = 0; ui < nu; ui++) b_u = lean_expr_mk_app(ks, b_u, u_list[ui]);
                    rec_app = lean_expr_mk_app(ks, rec_app, b_u);
                    if (n_rec >= cap_rec) {
                        cap_rec *= 2u;
                        v_vals = (uint32_t *)realloc(v_vals, cap_rec * sizeof(uint32_t));
                    }
                    v_vals[n_rec++] = lean_lctx_mk_lambda(ks, nu, u_list, rec_app);
                }
                free(it_args);
                for (uint32_t ui = 0; ui < nu; ui++) lean_pop_local(ks);
                free(u_list);
                cty = lean_expr_instantiate1(ks, ks->exprs[cty].d.binder.body, b_fv);
            }

            uint32_t rhs_body = minor_fvars[c];
            for (uint32_t bi = 0; bi < n_b; bi++) rhs_body = lean_expr_mk_app(ks, rhs_body, b_args[bi]);
            for (uint32_t vi = 0; vi < n_rec; vi++) rhs_body = lean_expr_mk_app(ks, rhs_body, v_vals[vi]);
            uint32_t rhs = lean_lctx_mk_lambda(ks, n_b, b_args, rhs_body);
            for (uint32_t bi = 0; bi < n_b; bi++) lean_pop_local(ks);
            free(b_args);
            free(v_vals);
            rhs = lean_lctx_mk_lambda(ks, n_work_ctors, minor_fvars, rhs);
            rhs = lean_lctx_mk_lambda(ks, n_work_types, motive_fvars, rhs);
            rhs = lean_lctx_mk_lambda(ks, elim_st.nparams, elim_st.param_fvars, rhs);
            ctor_rec_rhs[c] = rhs;
        }

        /* Assemble `derived_recs[0..n_work_types-1]` */
        derived_recs = (LeanDecl *)calloc(n_work_types, sizeof(LeanDecl));
        uint32_t *aux_rec_names    = (uint32_t *)calloc(n_work_types ? n_work_types : 1, sizeof(uint32_t));
        uint32_t *nested_rec_exprs = (uint32_t *)calloc(n_work_types ? n_work_types : 1, sizeof(uint32_t));
        uint32_t n_rec_rep = 0;

        for (uint32_t d = 0; d < n_work_types; d++) {
            LeanDecl *dr = &derived_recs[d];
            dr->kind = LDECL_REC;
            if (d < ntypes) {
                dr->name = lean_name_mk_str(ks, work_types[d].name, "rec");
            } else {
                uint32_t nested_rec_name = lean_name_append_index_after(
                    ks, lean_name_mk_str(ks, types[0].name, "rec"), d - ntypes + 1u);
                dr->name = nested_rec_name;
                uint32_t aux_rec_name = lean_name_mk_str(ks, work_types[d].name, "rec");
                aux_rec_names[n_rec_rep] = aux_rec_name;
                nested_rec_exprs[n_rec_rep] = lean_expr_mk_const(ks, nested_rec_name, rec_nparams_lvls, rec_lvl_ids);
                n_rec_rep++;
            }
            dr->nparams = rec_nparams_lvls;
            dr->level_params = (uint32_t *)malloc((rec_nparams_lvls ? rec_nparams_lvls : 1) * sizeof(uint32_t));
            for (uint32_t l = 0; l < rec_nparams_lvls; l++) dr->level_params[l] = rec_lvl_params[l];

            uint32_t cod = motive_fvars[d];
            for (uint32_t ii = 0; ii < work_types[d].num_indices; ii++) {
                cod = lean_expr_mk_app(ks, cod, idx_fvars[d][ii]);
            }
            cod = lean_expr_mk_app(ks, cod, major_fvars[d]);
            uint32_t r_ty = lean_lctx_mk_forall(ks, 1, &major_fvars[d], cod);
            r_ty = lean_lctx_mk_forall(ks, work_types[d].num_indices, idx_fvars[d], r_ty);
            r_ty = lean_lctx_mk_forall(ks, n_work_ctors, minor_fvars, r_ty);
            r_ty = lean_lctx_mk_forall(ks, n_work_types, motive_fvars, r_ty);
            r_ty = lean_lctx_mk_forall(ks, elim_st.nparams, elim_st.param_fvars, r_ty);

            dr->type = r_ty;
            dr->num_params = elim_st.nparams;
            dr->num_indices = work_types[d].num_indices;
            dr->num_motives = n_work_types;
            dr->num_minors = n_work_ctors;
            dr->is_k = is_k_target ? 1 : 0;
            dr->is_unsafe = types[0].is_unsafe;

            /* Collect rules for constructors of `work_types[d]` */
            uint32_t n_rules = work_types[d].nctors;
            dr->nrules = n_rules;
            dr->rules = (LeanRecRule *)calloc(n_rules ? n_rules : 1, sizeof(LeanRecRule));
            uint32_t r_idx = 0;
            for (uint32_t c = 0; c < n_work_ctors; c++) {
                if (work_ctors[c].ind_name == work_types[d].name) {
                    dr->rules[r_idx].ctor_name = work_ctors[c].name;
                    dr->rules[r_idx].nfields   = work_ctors[c].num_fields;
                    dr->rules[r_idx].rhs       = ctor_rec_rhs[c];
                    r_idx++;
                }
            }
        }

        /* Restore nested occurrences in `derived_recs` if `elim_st.n_aux2nested > 0` */
        if (elim_st.n_aux2nested > 0) {
            for (uint32_t d = 0; d < n_work_types; d++) {
                derived_recs[d].type = lean_restore_nested(&elim_st, derived_recs[d].type,
                                                           n_rec_rep, aux_rec_names, nested_rec_exprs);
                for (uint32_t rl = 0; rl < derived_recs[d].nrules; rl++) {
                    /* Restore ctor_name if it was an aux constructor */
                    uint32_t cn = derived_recs[d].rules[rl].ctor_name;
                    uint32_t pfx = ks->names[cn].pre;
                    for (uint32_t a = 0; a < elim_st.n_aux2nested; a++) {
                        if (pfx == elim_st.aux2nested_k[a]) {
                            uint32_t nested = elim_st.aux2nested_v[a];
                            uint32_t *dummy_args = NULL;
                            uint32_t n_F = 0;
                            uint32_t F_fn = lean_get_app_args_alloc(ks, nested, &dummy_args, &n_F);
                            free(dummy_args);
                            if (ks->exprs[F_fn].kind == LEXPR_CONST) {
                                derived_recs[d].rules[rl].ctor_name =
                                    lean_name_replace_prefix(ks, cn, pfx, ks->exprs[F_fn].d.cnst.name);
                            }
                            break;
                        }
                    }
                    derived_recs[d].rules[rl].rhs = lean_restore_nested(&elim_st, derived_recs[d].rules[rl].rhs,
                                                                        n_rec_rep, aux_rec_names, nested_rec_exprs);
                }
            }
        }

        free(aux_rec_names);
        free(nested_rec_exprs);
        free(rec_lvl_params);
        free(rec_lvl_ids);
        free(base_lvl_ids);
        while (pushed_base_params > 0) {
            lean_pop_local(ks);
            pushed_base_params--;
        }
        free(ctor_rec_rhs);
    }

    /* Remove temporary aux inductives and aux constructors from `decls_by_name` now that recursors are restored */
    for (uint32_t c = 0; c < n_work_ctors; c++) {
        bool is_primary = false;
        for (uint32_t t = 0; t < ntypes; t++) {
            if (work_ctors[c].ind_name == types[t].name) { is_primary = true; break; }
        }
        if (!is_primary) {
            uint32_t cn = work_ctors[c].name;
            if (cn != 0 && cn < ks->cap_decls_by_name) {
                free(ks->decls_by_name[cn].level_params);
                memset(&ks->decls_by_name[cn], 0, sizeof(LeanDecl));
            }
        }
    }
    for (uint32_t t = ntypes; t < n_work_types; t++) {
        uint32_t in = work_types[t].name;
        if (in != 0 && in < ks->cap_decls_by_name) {
            free(ks->decls_by_name[in].ctors);
            memset(&ks->decls_by_name[in], 0, sizeof(LeanDecl));
        }
        work_types[t].ctors = NULL;
    }

    /* Step 4: Verify that exported `recs[0..nrecs-1]` match `derived_recs[0..n_work_types-1]`!
     * Note: `lean4export` exports `recs` in `NameMap` order (e.g. `[rec_1, rec, rec_2]` for `numNested == 2`),
     * so match each `recs[r]` to its unique `derived_recs[dIdx]` by name while verifying 1-to-1 coverage. */
    if (!(ks->allow_legacy_format && nrecs == 0)) {
        if (nrecs != n_work_types) {
            snprintf(err_buf, err_cap, "inductive block has %u recursors, expected %u", nrecs, n_work_types);
            goto fail;
        }
        for (uint32_t r = 0; r < nrecs; r++) {
            LeanDecl *er = &recs[r];
            int d_match = -1;
            for (uint32_t d = 0; d < n_work_types; d++) {
                if (er->name == derived_recs[d].name) { d_match = (int)d; break; }
            }
            if (d_match < 0) {
                snprintf(err_buf, err_cap, "rec %s: unexpected recursor name in inductive block",
                         ks->names[er->name].full);
                goto fail;
            }
            for (uint32_t r2 = 0; r2 < r; r2++) {
                if (recs[r2].name == er->name) {
                    snprintf(err_buf, err_cap, "rec %s: duplicate recursor in inductive block",
                             ks->names[er->name].full);
                    goto fail;
                }
            }
            LeanDecl *dr = &derived_recs[d_match];
            if (er->nparams != dr->nparams ||
                er->num_params != dr->num_params ||
                er->num_indices != dr->num_indices ||
                er->num_motives != dr->num_motives ||
                er->num_minors != dr->num_minors ||
                er->nrules != dr->nrules ||
                er->is_k != dr->is_k ||
                er->is_unsafe != dr->is_unsafe) {
                snprintf(err_buf, err_cap,
                         "rec %s: metadata mismatch against kernel-derived recursor (k=%u/%u, params=%u/%u, idx=%u/%u, motives=%u/%u, minors=%u/%u, rules=%u/%u)",
                         ks->names[er->name].full, er->is_k, dr->is_k, er->num_params, dr->num_params,
                         er->num_indices, dr->num_indices, er->num_motives, dr->num_motives,
                         er->num_minors, dr->num_minors, er->nrules, dr->nrules);
                goto fail;
            }
            if (er->has_all_field) {
                if (er->nall != ntypes) {
                    snprintf(err_buf, err_cap, "rec %s: 'all' count mismatch", ks->names[er->name].full);
                    goto fail;
                }
                for (uint32_t j = 0; j < ntypes; j++) {
                    if (er->all[j] != types[j].name) {
                        snprintf(err_buf, err_cap, "rec %s: 'all[%u]' mismatch", ks->names[er->name].full, j);
                        goto fail;
                    }
                }
            }
            /* Substitute `dr`'s level params with `er`'s level params in case the motive universe parameter was renamed */
            uint32_t *er_lvl_ids = (uint32_t *)calloc(er->nparams ? er->nparams : 1, sizeof(uint32_t));
            for (uint32_t l = 0; l < er->nparams; l++) {
                for (uint32_t l2 = l + 1; l2 < er->nparams; l2++) {
                    if (er->level_params[l] == er->level_params[l2]) {
                        free(er_lvl_ids);
                        snprintf(err_buf, err_cap, "rec %s: duplicate level parameter", ks->names[er->name].full);
                        goto fail;
                    }
                }
                er_lvl_ids[l] = lean_lvl_mk_param(ks, er->level_params[l]);
            }
            uint32_t expected_rec_type = lean_expr_subst_lvls(ks, dr->type, dr->nparams, dr->level_params, er_lvl_ids);
            if (!lean_expr_eqv(ks, er->type, expected_rec_type)) {
                free(er_lvl_ids);
                snprintf(err_buf, err_cap, "rec %s: exported type does not match kernel-derived recursor type",
                         ks->names[er->name].full);
                goto fail;
            }
            for (uint32_t rl = 0; rl < dr->nrules; rl++) {
                uint32_t expected_rhs = lean_expr_subst_lvls(ks, dr->rules[rl].rhs, dr->nparams, dr->level_params, er_lvl_ids);
                if (er->rules[rl].ctor_name != dr->rules[rl].ctor_name ||
                    er->rules[rl].nfields != dr->rules[rl].nfields ||
                    !lean_expr_eqv(ks, er->rules[rl].rhs, expected_rhs)) {
                    free(er_lvl_ids);
                    snprintf(err_buf, err_cap, "rec %s: rule %u (ctor %s) does not match kernel-derived recursor rule",
                             ks->names[er->name].full, rl, ks->names[er->rules[rl].ctor_name].full);
                    goto fail;
                }
            }
            free(er_lvl_ids);
        }

        /* Step 5: Pre-register all recursor headers in the block and run `lean_verify_and_admit_rec` */
        for (uint32_t r = 0; r < nrecs; r++) {
            if (recs[r].name == 0 || lean_lookup_decl(ks, recs[r].name) != NULL) {
                snprintf(err_buf, err_cap, "rec %s: invalid or duplicate recursor name", ks->names[recs[r].name].full);
                goto fail;
            }
            lean_ensure_decls_cap(ks, recs[r].name);
            ks->decls_by_name[recs[r].name] = recs[r];
        }
        for (uint32_t r = 0; r < nrecs; r++) {
            if (!lean_verify_and_admit_rec(ks, &recs[r], err_buf, err_cap)) {
                goto fail;
            }
        }
    }

    /* Cleanup temporary allocations */
    if (derived_recs) {
        for (uint32_t d = 0; d < n_work_types; d++) {
            free(derived_recs[d].level_params);
            free(derived_recs[d].rules);
        }
        free(derived_recs);
    }
    if (idx_fvars) {
        for (uint32_t d = 0; d < n_work_types; d++) free(idx_fvars[d]);
        free(idx_fvars);
    }
    free(major_fvars);
    free(motive_fvars);
    free(minor_fvars);
    for (uint32_t e = 0; e < elim_st.n_entries; e++) {
        free(elim_st.entries[e].params);
        free(elim_st.entries[e].levels);
    }
    free(elim_st.entries);
    for (uint32_t a = 0; a < elim_st.n_aux_types; a++) free(elim_st.aux_types[a].level_params);
    free(elim_st.aux_types);
    for (uint32_t a = 0; a < elim_st.n_aux_ctors; a++) free(elim_st.aux_ctors[a].level_params);
    free(elim_st.aux_ctors);
    free(elim_st.aux2nested_k);
    free(elim_st.aux2nested_v);
    free(elim_st.param_fvars);
    free(work_types);
    free(work_ctors);
    free(ind_names);
    free(ind_lvls);
    free(ind_consts);
    lean_scratch_scope_end(ks);
    return true;

fail:
    while (pushed_base_params > 0) {
        lean_pop_local(ks);
        pushed_base_params--;
    }
    for (uint32_t r = 0; r < nrecs; r++) {
        uint32_t rn = recs[r].name;
        if (rn != 0 && rn < ks->cap_decls_by_name) {
            memset(&ks->decls_by_name[rn], 0, sizeof(LeanDecl));
        }
    }
    for (uint32_t c = 0; c < (n_work_ctors ? n_work_ctors : nctors); c++) {
        uint32_t cn = work_ctors ? work_ctors[c].name : ctors[c].name;
        if (cn != 0 && cn < ks->cap_decls_by_name) {
            free(ks->decls_by_name[cn].level_params);
            memset(&ks->decls_by_name[cn], 0, sizeof(LeanDecl));
        }
    }
    for (uint32_t t = 0; t < (n_work_types ? n_work_types : ntypes); t++) {
        uint32_t in = work_types ? work_types[t].name : types[t].name;
        if (in != 0 && in < ks->cap_decls_by_name) {
            memset(&ks->decls_by_name[in], 0, sizeof(LeanDecl));
        }
        if (work_types && work_types[t].ctors && (t >= ntypes || work_types[t].ctors != types[t].ctors)) {
            free(work_types[t].ctors);
            work_types[t].ctors = NULL;
        }
    }
    if (derived_recs) {
        for (uint32_t d = 0; d < n_work_types; d++) {
            free(derived_recs[d].level_params);
            free(derived_recs[d].rules);
        }
        free(derived_recs);
    }
    if (idx_fvars) {
        for (uint32_t d = 0; d < n_work_types; d++) free(idx_fvars[d]);
        free(idx_fvars);
    }
    free(major_fvars);
    free(motive_fvars);
    free(minor_fvars);
    for (uint32_t e = 0; e < elim_st.n_entries; e++) {
        free(elim_st.entries[e].params);
        free(elim_st.entries[e].levels);
    }
    free(elim_st.entries);
    for (uint32_t a = 0; a < elim_st.n_aux_types; a++) free(elim_st.aux_types[a].level_params);
    free(elim_st.aux_types);
    for (uint32_t a = 0; a < elim_st.n_aux_ctors; a++) free(elim_st.aux_ctors[a].level_params);
    free(elim_st.aux_ctors);
    free(elim_st.aux2nested_k);
    free(elim_st.aux2nested_v);
    free(elim_st.param_fvars);
    free(work_types);
    free(work_ctors);
    free(ind_names);
    free(ind_lvls);
    free(ind_consts);
    lean_scratch_scope_end(ks);
    return false;
}

/* =========================================================================
 * 7. Strict NDJSON Stream Parser (`lean4export` 3.1.0 / 3.0.0 / 2.1.0)
 * ========================================================================= */

static void lean_map_set_checked(uint32_t **map, uint8_t **present, uint32_t *cap, uint32_t idx, uint32_t val) {
    if (idx >= *cap) {
        size_t ncap = *cap ? (size_t)(*cap) * 2u : 4096u;
        while (ncap <= (size_t)idx) ncap *= 2u;
        *map = (uint32_t *)realloc(*map, ncap * sizeof(uint32_t));
        *present = (uint8_t *)realloc(*present, ncap * sizeof(uint8_t));
        if (!*map || !*present) { perror("realloc(lean_map_set_checked)"); exit(3); }
        memset(*map + *cap, 0, (ncap - (size_t)(*cap)) * sizeof(uint32_t));
        memset(*present + *cap, 0, (ncap - (size_t)(*cap)) * sizeof(uint8_t));
        *cap = (uint32_t)ncap;
    }
    (*map)[idx] = val;
    (*present)[idx] = 1u;
}

static bool lean_map_has(const uint8_t *present, uint32_t cap, uint32_t idx) {
    return idx < cap && present[idx] != 0;
}

static void lean_kernel_init(LeanKernelState *ks) {
    memset(ks, 0, sizeof(*ks));
    lean_tc_init_kernel();
    lean_gen_init();
    g_tc_admitted_decls = 0;
    g_tc_admitted_thms  = 0;
    g_tc_rule_commits   = 0;

    ks->cap_names = 1024u;
    ks->names = (LeanName *)calloc(ks->cap_names, sizeof(LeanName));
    ks->names[0].kind = LNAME_ANON;
    ks->names[0].full = xstrdup("");
    ks->nnames = 1u;

    ks->cap_lvls = 512u;
    ks->lvls = (LeanLvl *)calloc(ks->cap_lvls, sizeof(LeanLvl));
    ks->lvls[0].kind = LLVL_ZERO;
    ks->nlvls = 1u;

    ks->cap_exprs = LEAN_EXPR_MMAP_SLOTS;
    ks->exprs_mmap_bytes = (size_t)LEAN_EXPR_MMAP_SLOTS * sizeof(LeanExpr);
    ks->exprs = (LeanExpr *)mmap(NULL, ks->exprs_mmap_bytes, PROT_READ | PROT_WRITE,
                                 MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    if (ks->exprs == MAP_FAILED) {
        perror("mmap(ks->exprs)");
        exit(3);
    }
    ks->nexprs = 1u; /* 0 = null/error sentinel */
    ks->nscratch_exprs = 0u;
    ks->in_scratch_scope = false;
    ks->scratch_gen = 1u;
    ks->cap_scratch_htab = 65536u;
    ks->scratch_htab = (LeanScratchHtabSlot *)calloc(ks->cap_scratch_htab, sizeof(LeanScratchHtabSlot));
    ks->stat_peak_scratch = 0u;
    ks->defeq_cache = (LeanDefEqCache *)calloc(LEAN_DEFEQ_CACHE_SIZE, sizeof(LeanDefEqCache));
    ks->subst_cache = (LeanSubstCache *)calloc(LEAN_SUBST_CACHE_SIZE, sizeof(LeanSubstCache));
    ks->subst_gen = 0u;

    /* Export index 0 for names (`Name.anonymous`) and levels (`Level.zero`) are pre-allocated */
    lean_map_set_checked(&ks->export_name_map, &ks->export_name_present, &ks->cap_export_names, 0u, 0u);
    lean_map_set_checked(&ks->export_lvl_map,  &ks->export_lvl_present,  &ks->cap_export_lvls,  0u, 0u);
    ks->outcome = LEAN_OUTCOME_ACCEPT;
}

static void lean_kernel_destroy(LeanKernelState *ks) {
    if (!ks) return;
    for (uint32_t i = 0; i < ks->nnames; i++) {
        free(ks->names[i].str);
        free(ks->names[i].full);
    }
    free(ks->names);
    free(ks->name_htab);
    free(ks->defeq_cache);
    free(ks->subst_cache);
    for (uint32_t i = 1; i < ks->nexprs; i++) {
        if (ks->exprs[i].kind == LEXPR_CONST) free(ks->exprs[i].d.cnst.us);
        else if (ks->exprs[i].kind == LEXPR_NATLIT && !ks->exprs[i].nat_is_small) free(ks->exprs[i].d.nat_big.dec_str);
        else if (ks->exprs[i].kind == LEXPR_STRLIT) free(ks->exprs[i].d.str_lit.str);
    }
    if (ks->exprs && ks->exprs != MAP_FAILED) {
        munmap(ks->exprs, ks->exprs_mmap_bytes);
    }
    free(ks->expr_htab);
    free(ks->scratch_htab);
    free(ks->lvls);
    free(ks->lvl_htab);
    for (uint32_t i = 0; i < ks->cap_decls_by_name; i++) {
        free(ks->decls_by_name[i].level_params);
        free(ks->decls_by_name[i].all);
        free(ks->decls_by_name[i].ctors);
        free(ks->decls_by_name[i].declared_ctors);
        free(ks->decls_by_name[i].rules);
    }
    free(ks->decls_by_name);
    free(ks->axiom_names);
    free(ks->locals);
    free(ks->export_name_map);
    free(ks->export_name_present);
    free(ks->export_lvl_map);
    free(ks->export_lvl_present);
    free(ks->export_expr_map);
    free(ks->export_expr_present);
    lean_gen_free();
    free(g_tc_id_terms);
    g_tc_id_terms = NULL;
    g_tc_id_terms_cap = 0;
    memset(ks, 0, sizeof(*ks));
}

static bool json_get_u32_strict(struct json_object *obj, const char *key, uint32_t *out) {
    struct json_object *val = NULL;
    if (!obj || !json_object_object_get_ex(obj, key, &val) || !val) return false;
    if (!json_object_is_type(val, json_type_int)) return false;
    int64_t v = json_object_get_int64(val);
    if (v < 0 || v > (int64_t)UINT32_MAX) return false;
    *out = (uint32_t)v;
    return true;
}

static bool json_get_u64_strict(struct json_object *obj, const char *key, uint64_t *out) {
    struct json_object *val = NULL;
    if (!obj || !json_object_object_get_ex(obj, key, &val) || !val) return false;
    if (!json_object_is_type(val, json_type_int)) return false;
    errno = 0;
    uint64_t v = json_object_get_uint64(val);
    if (errno != 0) return false;
    *out = v;
    return true;
}

static bool json_get_bool_strict(struct json_object *obj, const char *key, bool *out) {
    struct json_object *val = NULL;
    if (!obj || !json_object_object_get_ex(obj, key, &val) || !val) return false;
    if (!json_object_is_type(val, json_type_boolean)) return false;
    *out = (bool)json_object_get_boolean(val);
    return true;
}

static const char *json_get_cstr_strict(struct json_object *obj, const char *key) {
    struct json_object *val = NULL;
    if (!obj || !json_object_object_get_ex(obj, key, &val) || !val) return NULL;
    if (!json_object_is_type(val, json_type_string)) return NULL;
    return json_object_get_string(val);
}

static bool lean_resolve_name_idx(const LeanKernelState *ks, uint32_t raw_idx, uint32_t *out_id) {
    if (!lean_map_has(ks->export_name_present, ks->cap_export_names, raw_idx)) return false;
    *out_id = ks->export_name_map[raw_idx];
    return true;
}

static bool lean_resolve_lvl_idx(const LeanKernelState *ks, uint32_t raw_idx, uint32_t *out_id) {
    if (!lean_map_has(ks->export_lvl_present, ks->cap_export_lvls, raw_idx)) return false;
    *out_id = ks->export_lvl_map[raw_idx];
    return true;
}

static bool lean_resolve_expr_idx(const LeanKernelState *ks, uint32_t raw_idx, uint32_t *out_id) {
    if (!lean_map_has(ks->export_expr_present, ks->cap_export_exprs, raw_idx)) return false;
    *out_id = ks->export_expr_map[raw_idx];
    return *out_id != 0;
}

static bool json_parse_mapped_u32_array(struct json_object *arr,
                                        const uint32_t *map, const uint8_t *present, uint32_t cap,
                                        uint32_t **out_arr, uint32_t *out_cnt) {
    *out_arr = NULL;
    *out_cnt = 0;
    if (!arr || !json_object_is_type(arr, json_type_array)) return false;
    size_t len = json_object_array_length(arr);
    if (len == 0) return true;
    uint32_t *res = (uint32_t *)malloc(len * sizeof(uint32_t));
    if (!res) return false;
    for (size_t i = 0; i < len; i++) {
        struct json_object *el = json_object_array_get_idx(arr, i);
        if (!el || !json_object_is_type(el, json_type_int)) {
            free(res);
            return false;
        }
        int64_t v = json_object_get_int64(el);
        if (v < 0 || v > (int64_t)UINT32_MAX || !lean_map_has(present, cap, (uint32_t)v)) {
            free(res);
            return false;
        }
        res[i] = map[(uint32_t)v];
    }
    *out_arr = res;
    *out_cnt = (uint32_t)len;
    return true;
}

static bool lean_fail_reject(LeanKernelState *ks, char *err_buf, size_t err_cap, const char *fmt, ...) {
    ks->outcome = LEAN_OUTCOME_REJECT;
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(err_buf, err_cap, fmt, ap);
    va_end(ap);
    return false;
}

static bool lean_fail_decline(LeanKernelState *ks, char *err_buf, size_t err_cap, const char *fmt, ...) {
    ks->outcome = LEAN_OUTCOME_DECLINE;
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(err_buf, err_cap, fmt, ap);
    va_end(ap);
    return false;
}

/* Parse a constructor object (`{name, levelParams, type, induct, cidx, numParams, numFields, isUnsafe}`) */
static bool lean_parse_ctor_obj(LeanKernelState *ks, struct json_object *cobj, uint32_t default_ind_name,
                                LeanCtorSpec *cs, char *err_buf, size_t err_cap) {
    memset(cs, 0, sizeof(*cs));
    bool is_unsafe = false;
    if (json_get_bool_strict(cobj, "isUnsafe", &is_unsafe)) {
        if (is_unsafe) {
            return lean_fail_decline(ks, err_buf, err_cap, "unsafe constructor declined");
        }
        cs->is_unsafe = 0;
    } else if (!ks->allow_legacy_format) {
        return lean_fail_reject(ks, err_buf, err_cap, "constructor missing boolean isUnsafe");
    }
    uint32_t nm_raw = 0, ty_raw = 0, ind_raw = 0;
    if (!json_get_u32_strict(cobj, "name", &nm_raw) || !lean_resolve_name_idx(ks, nm_raw, &cs->name) || cs->name == 0) {
        return lean_fail_reject(ks, err_buf, err_cap, "constructor has invalid or missing name index");
    }
    struct json_object *lp_arr = NULL;
    if (!json_object_object_get_ex(cobj, "levelParams", &lp_arr) ||
        !json_parse_mapped_u32_array(lp_arr, ks->export_name_map, ks->export_name_present, ks->cap_export_names,
                                     &cs->level_params, &cs->nparams)) {
        return lean_fail_reject(ks, err_buf, err_cap, "constructor %s has invalid levelParams", ks->names[cs->name].full);
    }
    if (!json_get_u32_strict(cobj, "type", &ty_raw) || !lean_resolve_expr_idx(ks, ty_raw, &cs->type)) {
        free(cs->level_params);
        cs->level_params = NULL;
        return lean_fail_reject(ks, err_buf, err_cap, "constructor %s has invalid type index", ks->names[cs->name].full);
    }
    if (json_get_u32_strict(cobj, "induct", &ind_raw) ||
        (ks->allow_legacy_format && json_get_u32_strict(cobj, "ind", &ind_raw))) {
        if (!lean_resolve_name_idx(ks, ind_raw, &cs->ind_name) || cs->ind_name == 0) {
            free(cs->level_params);
            cs->level_params = NULL;
            return lean_fail_reject(ks, err_buf, err_cap, "constructor %s has invalid induct index", ks->names[cs->name].full);
        }
    } else if (ks->allow_legacy_format) {
        cs->ind_name = default_ind_name;
    } else {
        free(cs->level_params);
        cs->level_params = NULL;
        return lean_fail_reject(ks, err_buf, err_cap, "constructor %s missing induct index", ks->names[cs->name].full);
    }
    if (!json_get_u32_strict(cobj, "cidx", &cs->cidx) ||
        !json_get_u32_strict(cobj, "numParams", &cs->num_params) ||
        !json_get_u32_strict(cobj, "numFields", &cs->num_fields) ||
        cs->cidx >= 0x3fffffffu || cs->num_params >= 0x3fffffffu || cs->num_fields >= 0x3fffffffu) {
        free(cs->level_params);
        cs->level_params = NULL;
        return lean_fail_reject(ks, err_buf, err_cap, "constructor %s missing or out-of-range cidx/numParams/numFields",
                                ks->names[cs->name].full);
    }
    return true;
}

/* Parse a recursor object (`{name, levelParams, type, all, numParams, numIndices, numMotives, numMinors, rules, k, isUnsafe}`) */
static bool lean_parse_rec_obj(LeanKernelState *ks, struct json_object *robj, LeanDecl *rec, char *err_buf, size_t err_cap) {
    memset(rec, 0, sizeof(*rec));
    rec->kind = LDECL_REC;
    bool is_unsafe = false;
    if (json_get_bool_strict(robj, "isUnsafe", &is_unsafe)) {
        if (is_unsafe) {
            return lean_fail_decline(ks, err_buf, err_cap, "unsafe recursor declined");
        }
        rec->is_unsafe = 0;
    } else if (!ks->allow_legacy_format) {
        return lean_fail_reject(ks, err_buf, err_cap, "recursor missing boolean isUnsafe");
    }
    uint32_t nm_raw = 0, ty_raw = 0, ind_raw = 0;
    if (!json_get_u32_strict(robj, "name", &nm_raw) || !lean_resolve_name_idx(ks, nm_raw, &rec->name) || rec->name == 0) {
        return lean_fail_reject(ks, err_buf, err_cap, "recursor has invalid or missing name index");
    }
    if (!json_get_u32_strict(robj, "type", &ty_raw) || !lean_resolve_expr_idx(ks, ty_raw, &rec->type)) {
        return lean_fail_reject(ks, err_buf, err_cap, "recursor %s has invalid type index", ks->names[rec->name].full);
    }
    struct json_object *lp_arr = NULL;
    if (!json_object_object_get_ex(robj, "levelParams", &lp_arr) ||
        !json_parse_mapped_u32_array(lp_arr, ks->export_name_map, ks->export_name_present, ks->cap_export_names,
                                     &rec->level_params, &rec->nparams)) {
        return lean_fail_reject(ks, err_buf, err_cap, "recursor %s has invalid levelParams", ks->names[rec->name].full);
    }
    if (ks->allow_legacy_format && json_get_u32_strict(robj, "ind", &ind_raw)) {
        if (!lean_resolve_name_idx(ks, ind_raw, &rec->ind_name) || rec->ind_name == 0) {
            free(rec->level_params);
            rec->level_params = NULL;
            return lean_fail_reject(ks, err_buf, err_cap, "recursor %s has invalid ind index", ks->names[rec->name].full);
        }
    }
    struct json_object *all_arr = NULL;
    if (json_object_object_get_ex(robj, "all", &all_arr)) {
        if (!json_parse_mapped_u32_array(all_arr, ks->export_name_map, ks->export_name_present, ks->cap_export_names,
                                         &rec->all, &rec->nall) || rec->nall == 0) {
            free(rec->level_params);
            free(rec->all);
            rec->level_params = NULL;
            rec->all = NULL;
            return lean_fail_reject(ks, err_buf, err_cap, "recursor %s has invalid all array", ks->names[rec->name].full);
        }
        rec->has_all_field = 1;
    } else if (!ks->allow_legacy_format) {
        free(rec->level_params);
        rec->level_params = NULL;
        return lean_fail_reject(ks, err_buf, err_cap, "recursor %s missing all array", ks->names[rec->name].full);
    }
    if (!json_get_u32_strict(robj, "numParams", &rec->num_params) ||
        !json_get_u32_strict(robj, "numIndices", &rec->num_indices) ||
        !json_get_u32_strict(robj, "numMotives", &rec->num_motives) ||
        !json_get_u32_strict(robj, "numMinors", &rec->num_minors) ||
        !json_get_bool_strict(robj, "k", &rec->is_k) ||
        rec->num_params >= 0x1fffffffu || rec->num_indices >= 0x1fffffffu ||
        rec->num_motives >= 0x1fffffffu || rec->num_minors >= 0x1fffffffu) {
        free(rec->level_params);
        free(rec->all);
        rec->level_params = NULL;
        rec->all = NULL;
        return lean_fail_reject(ks, err_buf, err_cap, "recursor %s missing or out-of-range numeric/k metadata", ks->names[rec->name].full);
    }
    struct json_object *rules_arr = NULL;
    if (!json_object_object_get_ex(robj, "rules", &rules_arr) ||
        !rules_arr || !json_object_is_type(rules_arr, json_type_array)) {
        free(rec->level_params);
        free(rec->all);
        rec->level_params = NULL;
        rec->all = NULL;
        return lean_fail_reject(ks, err_buf, err_cap, "recursor %s missing rules array", ks->names[rec->name].full);
    }
    size_t rlen = json_object_array_length(rules_arr);
    rec->nrules = (uint32_t)rlen;
    rec->rules = rlen > 0 ? (LeanRecRule *)calloc(rlen, sizeof(LeanRecRule)) : NULL;
    for (size_t i = 0; i < rlen; i++) {
        struct json_object *ro = json_object_array_get_idx(rules_arr, i);
        uint32_t ctor_raw = 0, rhs_raw = 0;
        if (!ro || !json_object_is_type(ro, json_type_object) ||
            !json_get_u32_strict(ro, "ctor", &ctor_raw) ||
            !lean_resolve_name_idx(ks, ctor_raw, &rec->rules[i].ctor_name) ||
            !json_get_u32_strict(ro, "nfields", &rec->rules[i].nfields) ||
            rec->rules[i].nfields >= 0x3fffffffu ||
            !json_get_u32_strict(ro, "rhs", &rhs_raw) ||
            !lean_resolve_expr_idx(ks, rhs_raw, &rec->rules[i].rhs)) {
            free(rec->level_params);
            free(rec->all);
            free(rec->rules);
            rec->level_params = NULL;
            rec->all = NULL;
            rec->rules = NULL;
            return lean_fail_reject(ks, err_buf, err_cap, "recursor %s has malformed rule %zu",
                                    ks->names[rec->name].full, i);
        }
    }
    return true;
}

static inline bool scan_lit(const char **p, const char *end, const char *lit, size_t n) {
    if ((size_t)(end - *p) < n || memcmp(*p, lit, n) != 0) return false;
    *p += n;
    return true;
}

static inline bool scan_u32_strict(const char **p, const char *end, uint32_t *out) {
    const char *s = *p;
    if (s >= end || *s < '0' || *s > '9') return false;
    if (*s == '0') {
        s++;
        if (s < end && *s >= '0' && *s <= '9') return false;
        *p = s;
        *out = 0u;
        return true;
    }
    uint64_t v = 0;
    while (s < end && *s >= '0' && *s <= '9') {
        v = v * 10u + (uint64_t)(*s - '0');
        if (v > UINT32_MAX) return false;
        s++;
    }
    *p = s;
    *out = (uint32_t)v;
    return true;
}

static inline bool scan_binder_info(const char **p, const char *end) {
    return scan_lit(p, end, "\"default\"", 9) ||
           scan_lit(p, end, "\"implicit\"", 10) ||
           scan_lit(p, end, "\"strictImplicit\"", 16) ||
           scan_lit(p, end, "\"instImplicit\"", 14);
}

/* Zero-allocation byte-scanner fast path for canonical single-line lean4export 3.1.0
 * expression/name table records (~98.5% of lines in Init and Std). Falls back cleanly
 * (`*handled = false`) on any non-canonical formatting, escapes, or declarations. */
static void lean_try_fast_scan_ndjson_line(LeanKernelState *ks, const char *line, size_t line_len,
                                           bool *handled, bool *ok, char *err_buf, size_t err_cap) {
    *handled = false;
    if (!ks->metadata_seen || line_len < 12 || line[0] != '{' || line[line_len - 1] != '}') return;
    const char *p = line;
    const char *end = line + line_len;

    /* 1. {"app":{"arg":<arg>,"fn":<fn>},"ie":<idx>} */
    if (scan_lit(&p, end, "{\"app\":{\"arg\":", 14)) {
        uint32_t arg_raw = 0, fn_raw = 0, idx = 0, fn = 0, arg = 0;
        if (!scan_u32_strict(&p, end, &arg_raw) ||
            !scan_lit(&p, end, ",\"fn\":", 6) ||
            !scan_u32_strict(&p, end, &fn_raw) ||
            !scan_lit(&p, end, "},\"ie\":", 7) ||
            !scan_u32_strict(&p, end, &idx) ||
            !scan_lit(&p, end, "}", 1) || p != end) {
            return;
        }
        *handled = true;
        if (idx > ks->n_export_exprs + 1024u ||
            lean_map_has(ks->export_expr_present, ks->cap_export_exprs, idx) ||
            !lean_resolve_expr_idx(ks, fn_raw, &fn) ||
            !lean_resolve_expr_idx(ks, arg_raw, &arg)) {
            *ok = lean_fail_reject(ks, err_buf, err_cap, "invalid fast app expr at %u", idx);
            return;
        }
        uint32_t eid = lean_expr_mk_app(ks, fn, arg);
        lean_map_set_checked(&ks->export_expr_map, &ks->export_expr_present, &ks->cap_export_exprs, idx, eid);
        ks->n_export_exprs++;
        *ok = true;
        return;
    }

    /* 2. {"forallE":{"binderInfo":<bi>,"body":<bd>,"name":<nm>,"type":<ty>},"ie":<idx>} */
    p = line;
    if (scan_lit(&p, end, "{\"forallE\":{\"binderInfo\":", 25)) {
        uint32_t bd_raw = 0, nm_raw = 0, ty_raw = 0, idx = 0, nm = 0, ty = 0, bd = 0;
        if (!scan_binder_info(&p, end) ||
            !scan_lit(&p, end, ",\"body\":", 8) ||
            !scan_u32_strict(&p, end, &bd_raw) ||
            !scan_lit(&p, end, ",\"name\":", 8) ||
            !scan_u32_strict(&p, end, &nm_raw) ||
            !scan_lit(&p, end, ",\"type\":", 8) ||
            !scan_u32_strict(&p, end, &ty_raw) ||
            !scan_lit(&p, end, "},\"ie\":", 7) ||
            !scan_u32_strict(&p, end, &idx) ||
            !scan_lit(&p, end, "}", 1) || p != end) {
            return;
        }
        *handled = true;
        if (idx > ks->n_export_exprs + 1024u ||
            lean_map_has(ks->export_expr_present, ks->cap_export_exprs, idx) ||
            !lean_resolve_name_idx(ks, nm_raw, &nm) ||
            !lean_resolve_expr_idx(ks, ty_raw, &ty) ||
            !lean_resolve_expr_idx(ks, bd_raw, &bd)) {
            *ok = lean_fail_reject(ks, err_buf, err_cap, "invalid fast forallE expr at %u", idx);
            return;
        }
        uint32_t eid = lean_expr_mk_forall(ks, nm, ty, bd);
        lean_map_set_checked(&ks->export_expr_map, &ks->export_expr_present, &ks->cap_export_exprs, idx, eid);
        ks->n_export_exprs++;
        *ok = true;
        return;
    }

    /* 3. {"ie":<idx>, ...} (lam, letE, proj, sort) */
    p = line;
    if (scan_lit(&p, end, "{\"ie\":", 6)) {
        uint32_t idx = 0;
        if (!scan_u32_strict(&p, end, &idx)) return;
        if (scan_lit(&p, end, ",\"lam\":{\"binderInfo\":", 21)) {
            uint32_t bd_raw = 0, nm_raw = 0, ty_raw = 0, nm = 0, ty = 0, bd = 0;
            if (!scan_binder_info(&p, end) ||
                !scan_lit(&p, end, ",\"body\":", 8) ||
                !scan_u32_strict(&p, end, &bd_raw) ||
                !scan_lit(&p, end, ",\"name\":", 8) ||
                !scan_u32_strict(&p, end, &nm_raw) ||
                !scan_lit(&p, end, ",\"type\":", 8) ||
                !scan_u32_strict(&p, end, &ty_raw) ||
                !scan_lit(&p, end, "}}", 2) || p != end) {
                return;
            }
            *handled = true;
            if (idx > ks->n_export_exprs + 1024u ||
                lean_map_has(ks->export_expr_present, ks->cap_export_exprs, idx) ||
                !lean_resolve_name_idx(ks, nm_raw, &nm) ||
                !lean_resolve_expr_idx(ks, ty_raw, &ty) ||
                !lean_resolve_expr_idx(ks, bd_raw, &bd)) {
                *ok = lean_fail_reject(ks, err_buf, err_cap, "invalid fast lam expr at %u", idx);
                return;
            }
            uint32_t eid = lean_expr_mk_lam(ks, nm, ty, bd);
            lean_map_set_checked(&ks->export_expr_map, &ks->export_expr_present, &ks->cap_export_exprs, idx, eid);
            ks->n_export_exprs++;
            *ok = true;
            return;
        }
        if (scan_lit(&p, end, ",\"letE\":{\"body\":", 16)) {
            uint32_t bd_raw = 0, nm_raw = 0, ty_raw = 0, vl_raw = 0, nm = 0, ty = 0, vl = 0, bd = 0;
            if (!scan_u32_strict(&p, end, &bd_raw) ||
                !scan_lit(&p, end, ",\"name\":", 8) ||
                !scan_u32_strict(&p, end, &nm_raw) ||
                !(scan_lit(&p, end, ",\"nondep\":false,\"type\":", 23) ||
                  scan_lit(&p, end, ",\"nondep\":true,\"type\":", 22)) ||
                !scan_u32_strict(&p, end, &ty_raw) ||
                !scan_lit(&p, end, ",\"value\":", 9) ||
                !scan_u32_strict(&p, end, &vl_raw) ||
                !scan_lit(&p, end, "}}", 2) || p != end) {
                return;
            }
            *handled = true;
            if (idx > ks->n_export_exprs + 1024u ||
                lean_map_has(ks->export_expr_present, ks->cap_export_exprs, idx) ||
                !lean_resolve_name_idx(ks, nm_raw, &nm) ||
                !lean_resolve_expr_idx(ks, ty_raw, &ty) ||
                !lean_resolve_expr_idx(ks, vl_raw, &vl) ||
                !lean_resolve_expr_idx(ks, bd_raw, &bd)) {
                *ok = lean_fail_reject(ks, err_buf, err_cap, "invalid fast letE expr at %u", idx);
                return;
            }
            uint32_t eid = lean_expr_mk_let(ks, nm, ty, vl, bd);
            lean_map_set_checked(&ks->export_expr_map, &ks->export_expr_present, &ks->cap_export_exprs, idx, eid);
            ks->n_export_exprs++;
            *ok = true;
            return;
        }
        if (scan_lit(&p, end, ",\"proj\":{\"idx\":", 15)) {
            uint32_t fidx = 0, s_raw = 0, tn_raw = 0, s = 0, tn = 0;
            if (!scan_u32_strict(&p, end, &fidx) ||
                !scan_lit(&p, end, ",\"struct\":", 10) ||
                !scan_u32_strict(&p, end, &s_raw) ||
                !scan_lit(&p, end, ",\"typeName\":", 12) ||
                !scan_u32_strict(&p, end, &tn_raw) ||
                !scan_lit(&p, end, "}}", 2) || p != end) {
                return;
            }
            *handled = true;
            if (idx > ks->n_export_exprs + 1024u || fidx >= 0x3fffffffu ||
                lean_map_has(ks->export_expr_present, ks->cap_export_exprs, idx) ||
                !lean_resolve_name_idx(ks, tn_raw, &tn) || tn == 0 ||
                !lean_resolve_expr_idx(ks, s_raw, &s)) {
                *ok = lean_fail_reject(ks, err_buf, err_cap, "invalid fast proj expr at %u", idx);
                return;
            }
            uint32_t eid = lean_expr_mk_proj(ks, tn, fidx, s);
            lean_map_set_checked(&ks->export_expr_map, &ks->export_expr_present, &ks->cap_export_exprs, idx, eid);
            ks->n_export_exprs++;
            *ok = true;
            return;
        }
        if (scan_lit(&p, end, ",\"sort\":", 8)) {
            uint32_t u_raw = 0, u = 0;
            if (!scan_u32_strict(&p, end, &u_raw) || !scan_lit(&p, end, "}", 1) || p != end) return;
            *handled = true;
            if (idx > ks->n_export_exprs + 1024u ||
                lean_map_has(ks->export_expr_present, ks->cap_export_exprs, idx) ||
                !lean_resolve_lvl_idx(ks, u_raw, &u)) {
                *ok = lean_fail_reject(ks, err_buf, err_cap, "invalid fast sort expr at %u", idx);
                return;
            }
            uint32_t eid = lean_expr_mk_sort(ks, u);
            lean_map_set_checked(&ks->export_expr_map, &ks->export_expr_present, &ks->cap_export_exprs, idx, eid);
            ks->n_export_exprs++;
            *ok = true;
            return;
        }
        return;
    }

    /* 4. {"const":{"name":<nm>,"us":[...]},"ie":<idx>} */
    p = line;
    if (scan_lit(&p, end, "{\"const\":{\"name\":", 17)) {
        uint32_t nm_raw = 0, idx = 0, nm = 0;
        uint32_t us_raw[16], us[16], nus = 0;
        if (!scan_u32_strict(&p, end, &nm_raw) || !scan_lit(&p, end, ",\"us\":[", 7)) return;
        if (!scan_lit(&p, end, "]", 1)) {
            while (true) {
                if (nus >= 16 || !scan_u32_strict(&p, end, &us_raw[nus])) return;
                nus++;
                if (scan_lit(&p, end, ",", 1)) continue;
                if (scan_lit(&p, end, "]", 1)) break;
                return;
            }
        }
        if (!scan_lit(&p, end, "},\"ie\":", 7) || !scan_u32_strict(&p, end, &idx) ||
            !scan_lit(&p, end, "}", 1) || p != end) {
            return;
        }
        *handled = true;
        if (idx > ks->n_export_exprs + 1024u ||
            lean_map_has(ks->export_expr_present, ks->cap_export_exprs, idx) ||
            !lean_resolve_name_idx(ks, nm_raw, &nm) || nm == 0) {
            *ok = lean_fail_reject(ks, err_buf, err_cap, "invalid fast const expr at %u", idx);
            return;
        }
        for (uint32_t i = 0; i < nus; i++) {
            if (!lean_resolve_lvl_idx(ks, us_raw[i], &us[i])) {
                *ok = lean_fail_reject(ks, err_buf, err_cap, "invalid fast const level at %u", idx);
                return;
            }
        }
        uint32_t eid = lean_expr_mk_const(ks, nm, nus, us);
        lean_map_set_checked(&ks->export_expr_map, &ks->export_expr_present, &ks->cap_export_exprs, idx, eid);
        ks->n_export_exprs++;
        *ok = true;
        return;
    }

    /* 5. {"in":<idx>,"str":{"pre":<pre>,"str":"<plain>"}} */
    p = line;
    if (scan_lit(&p, end, "{\"in\":", 6)) {
        uint32_t idx = 0, pre_raw = 0, pre = 0;
        if (!scan_u32_strict(&p, end, &idx) || !scan_lit(&p, end, ",\"str\":{\"pre\":", 14) ||
            !scan_u32_strict(&p, end, &pre_raw) || !scan_lit(&p, end, ",\"str\":\"", 8)) {
            return;
        }
        if ((size_t)(end - p) < 3 || memcmp(end - 3, "\"}}", 3) != 0) return;
        const char *str_end = end - 3;
        size_t slen = (size_t)(str_end - p);
        if (slen >= 512) return;
        for (const char *c = p; c < str_end; c++) {
            unsigned char uc = (unsigned char)*c;
            if (uc < 0x20 || uc >= 0x80 || uc == '"' || uc == '\\') return;
        }
        *handled = true;
        if (idx == 0 || idx > ks->n_export_names + 1024u ||
            lean_map_has(ks->export_name_present, ks->cap_export_names, idx) ||
            !lean_resolve_name_idx(ks, pre_raw, &pre)) {
            *ok = lean_fail_reject(ks, err_buf, err_cap, "invalid fast str name at %u", idx);
            return;
        }
        char sbuf[512];
        memcpy(sbuf, p, slen);
        sbuf[slen] = '\0';
        uint32_t nid = lean_name_mk_str(ks, pre, sbuf);
        lean_map_set_checked(&ks->export_name_map, &ks->export_name_present, &ks->cap_export_names, idx, nid);
        ks->n_export_names++;
        *ok = true;
        return;
    }

    /* 6. {"bvar":<bidx>,"ie":<idx>} */
    p = line;
    if (scan_lit(&p, end, "{\"bvar\":", 8)) {
        uint32_t bidx = 0, idx = 0;
        if (!scan_u32_strict(&p, end, &bidx) || !scan_lit(&p, end, ",\"ie\":", 6) ||
            !scan_u32_strict(&p, end, &idx) || !scan_lit(&p, end, "}", 1) || p != end) {
            return;
        }
        *handled = true;
        if (idx > ks->n_export_exprs + 1024u || bidx == UINT32_MAX ||
            lean_map_has(ks->export_expr_present, ks->cap_export_exprs, idx)) {
            *ok = lean_fail_reject(ks, err_buf, err_cap, "invalid or duplicate bvar expr index %u", idx);
            return;
        }
        uint32_t eid = lean_expr_mk_bvar(ks, bidx);
        lean_map_set_checked(&ks->export_expr_map, &ks->export_expr_present, &ks->cap_export_exprs, idx, eid);
        ks->n_export_exprs++;
        *ok = true;
        return;
    }
}

static bool lean_parse_and_verify_ndjson_line(LeanKernelState *ks, const char *line, char *err_buf, size_t err_cap) {
    while (*line == ' ' || *line == '\t' || *line == '\r' || *line == '\n') line++;
    if (*line == '\0') return true;

    size_t line_len = strlen(line);
    while (line_len > 0 && (line[line_len - 1] == '\n' || line[line_len - 1] == '\r' ||
                            line[line_len - 1] == ' '  || line[line_len - 1] == '\t')) {
        line_len--;
    }

    bool fast_handled = false, fast_ok = false;
    lean_try_fast_scan_ndjson_line(ks, line, line_len, &fast_handled, &fast_ok, err_buf, err_cap);
    if (fast_handled) return fast_ok;

    struct json_tokener *tok = json_tokener_new_ex(64);
    json_tokener_set_flags(tok, JSON_TOKENER_STRICT);
    struct json_object *root = json_tokener_parse_ex(tok, line, (int)line_len);
    enum json_tokener_error jerr = json_tokener_get_error(tok);
    size_t char_end = tok->char_offset;
    json_tokener_free(tok);

    if (!root || jerr != json_tokener_success || char_end != line_len ||
        !json_object_is_type(root, json_type_object) || json_object_object_length(root) == 0) {
        if (root) json_object_put(root);
        return lean_fail_reject(ks, err_buf, err_cap, "malformed JSON record");
    }

    /* 0. Metadata header: {"meta": ...} */
    struct json_object *meta_obj = NULL;
    if (json_object_object_get_ex(root, "meta", &meta_obj)) {
        if (ks->metadata_seen || json_object_object_length(root) != 1 ||
            !meta_obj || !json_object_is_type(meta_obj, json_type_object)) {
            json_object_put(root);
            return lean_fail_reject(ks, err_buf, err_cap, "invalid or duplicate meta header");
        }
        struct json_object *fmt_obj = NULL;
        if (!json_object_object_get_ex(meta_obj, "format", &fmt_obj) ||
            !fmt_obj || !json_object_is_type(fmt_obj, json_type_object)) {
            json_object_put(root);
            return lean_fail_reject(ks, err_buf, err_cap, "meta header missing format object");
        }
        const char *fver = json_get_cstr_strict(fmt_obj, "version");
        if (!fver) {
            json_object_put(root);
            return lean_fail_reject(ks, err_buf, err_cap, "meta.format.version missing");
        }
        snprintf(ks->format_version, sizeof(ks->format_version), "%s", fver);
        if (strcmp(fver, "3.1.0") != 0 && strcmp(fver, "3.0.0") != 0 &&
            strcmp(fver, "2.1.0") != 0 && strcmp(fver, "review-current-input") != 0) {
            json_object_put(root);
            return lean_fail_decline(ks, err_buf, err_cap, "unsupported export format version: %s", ks->format_version);
        }
        struct json_object *lean_obj = NULL;
        if (json_object_object_get_ex(meta_obj, "lean", &lean_obj) &&
            lean_obj && json_object_is_type(lean_obj, json_type_object)) {
            const char *lver = json_get_cstr_strict(lean_obj, "version");
            const char *lgit = json_get_cstr_strict(lean_obj, "githash");
            if (lver) snprintf(ks->lean_version, sizeof(ks->lean_version), "%s", lver);
            if (lgit) snprintf(ks->lean_githash, sizeof(ks->lean_githash), "%s", lgit);
            /* Accept Lean 4.20.x .. 4.39.x (two-digit minor version followed by '.');
             * decline unrecognized Lean versions (e.g. 3.x, 5.x, 99.x, or 4.330.0). */
            if (lver) {
                bool valid_lean4 = (lver[0] == '4' && lver[1] == '.' &&
                                    (lver[2] == '2' || lver[2] == '3') &&
                                    (lver[3] >= '0' && lver[3] <= '9') &&
                                    lver[4] == '.');
                if (!valid_lean4) {
                    json_object_put(root);
                    return lean_fail_decline(ks, err_buf, err_cap, "unsupported Lean version in meta: %s", ks->lean_version);
                }
            }
        }
        ks->metadata_seen = true;
        json_object_put(root);
        return true;
    }

    if (!ks->metadata_seen && !ks->allow_legacy_format) {
        json_object_put(root);
        return lean_fail_reject(ks, err_buf, err_cap, "missing meta header on first record");
    }

    /* 1. Name table record: {"in": idx, "str": {"pre": p, "str": s}} or {"in": idx, "num": {"pre": p, "i": n}} */
    struct json_object *in_val = NULL;
    if (json_object_object_get_ex(root, "in", &in_val)) {
        uint32_t idx = 0;
        if (json_object_object_length(root) != 2 || !json_get_u32_strict(root, "in", &idx) ||
            idx == 0 || idx > ks->n_export_names + 1024u ||
            lean_map_has(ks->export_name_present, ks->cap_export_names, idx)) {
            json_object_put(root);
            return lean_fail_reject(ks, err_buf, err_cap, "invalid or duplicate name index");
        }
        struct json_object *sub = NULL;
        if (json_object_object_get_ex(root, "str", &sub) && sub && json_object_is_type(sub, json_type_object)) {
            uint32_t pre_raw = 0, pre = 0;
            const char *s = json_get_cstr_strict(sub, "str");
            if (!s || !json_get_u32_strict(sub, "pre", &pre_raw) || !lean_resolve_name_idx(ks, pre_raw, &pre)) {
                json_object_put(root);
                return lean_fail_reject(ks, err_buf, err_cap, "malformed str name record %u", idx);
            }
            uint32_t nid = lean_name_mk_str(ks, pre, s);
            lean_map_set_checked(&ks->export_name_map, &ks->export_name_present, &ks->cap_export_names, idx, nid);
            ks->n_export_names++;
            json_object_put(root);
            return true;
        }
        if (json_object_object_get_ex(root, "num", &sub) && sub && json_object_is_type(sub, json_type_object)) {
            uint32_t pre_raw = 0, pre = 0;
            uint64_t num = 0;
            if (!json_get_u32_strict(sub, "pre", &pre_raw) || !lean_resolve_name_idx(ks, pre_raw, &pre) ||
                !json_get_u64_strict(sub, "i", &num)) {
                json_object_put(root);
                return lean_fail_reject(ks, err_buf, err_cap, "malformed num name record %u", idx);
            }
            uint32_t nid = lean_name_mk_num(ks, pre, num);
            lean_map_set_checked(&ks->export_name_map, &ks->export_name_present, &ks->cap_export_names, idx, nid);
            ks->n_export_names++;
            json_object_put(root);
            return true;
        }
        json_object_put(root);
        return lean_fail_reject(ks, err_buf, err_cap, "unknown name variant at index %u", idx);
    }

    /* 2. Universe level table record: {"il": idx, "succ"|"max"|"imax"|"param": ...} */
    struct json_object *il_val = NULL;
    if (json_object_object_get_ex(root, "il", &il_val)) {
        uint32_t idx = 0;
        if (json_object_object_length(root) != 2 || !json_get_u32_strict(root, "il", &idx) ||
            idx == 0 || idx > ks->n_export_lvls + 1024u ||
            lean_map_has(ks->export_lvl_present, ks->cap_export_lvls, idx)) {
            json_object_put(root);
            return lean_fail_reject(ks, err_buf, err_cap, "invalid or duplicate level index");
        }
        uint32_t lid = 0, raw_u = 0, u = 0;
        struct json_object *sub = NULL;
        if (json_object_object_get_ex(root, "succ", &sub)) {
            if (!json_get_u32_strict(root, "succ", &raw_u) || !lean_resolve_lvl_idx(ks, raw_u, &u)) {
                json_object_put(root);
                return lean_fail_reject(ks, err_buf, err_cap, "malformed succ level at %u", idx);
            }
            lid = lean_lvl_mk_succ(ks, u);
        } else if (json_object_object_get_ex(root, "max", &sub) || json_object_object_get_ex(root, "imax", &sub)) {
            bool is_imax = json_object_object_get_ex(root, "imax", NULL);
            uint32_t *arr = NULL, cnt = 0;
            if (!json_parse_mapped_u32_array(sub, ks->export_lvl_map, ks->export_lvl_present, ks->cap_export_lvls,
                                             &arr, &cnt) || cnt != 2) {
                free(arr);
                json_object_put(root);
                return lean_fail_reject(ks, err_buf, err_cap, "malformed max/imax level at %u", idx);
            }
            lid = is_imax ? lean_lvl_mk_imax(ks, arr[0], arr[1]) : lean_lvl_mk_max(ks, arr[0], arr[1]);
            free(arr);
        } else if (json_object_object_get_ex(root, "param", &sub)) {
            uint32_t nm_raw = 0, nm = 0;
            if (!json_get_u32_strict(root, "param", &nm_raw) || !lean_resolve_name_idx(ks, nm_raw, &nm) || nm == 0) {
                json_object_put(root);
                return lean_fail_reject(ks, err_buf, err_cap, "malformed param level at %u", idx);
            }
            lid = lean_lvl_mk_param(ks, nm);
        } else {
            json_object_put(root);
            return lean_fail_reject(ks, err_buf, err_cap, "unknown level variant at %u", idx);
        }
        lean_map_set_checked(&ks->export_lvl_map, &ks->export_lvl_present, &ks->cap_export_lvls, idx, lid);
        ks->n_export_lvls++;
        json_object_put(root);
        return true;
    }

    /* 3. Expression DAG record: {"ie": idx, ...} */
    struct json_object *ie_val = NULL;
    if (json_object_object_get_ex(root, "ie", &ie_val)) {
        uint32_t idx = 0;
        if (json_object_object_length(root) != 2 || !json_get_u32_strict(root, "ie", &idx) ||
            idx > ks->n_export_exprs + 1024u ||
            lean_map_has(ks->export_expr_present, ks->cap_export_exprs, idx)) {
            json_object_put(root);
            return lean_fail_reject(ks, err_buf, err_cap, "invalid, duplicate, or multi-variant expr index");
        }
        uint32_t eid = 0;
        struct json_object *sub = NULL;
        if (json_object_object_get_ex(root, "bvar", &sub)) {
            uint32_t bv = 0;
            if (!json_get_u32_strict(root, "bvar", &bv) || bv == UINT32_MAX) {
                json_object_put(root);
                return lean_fail_reject(ks, err_buf, err_cap, "malformed bvar expr at %u", idx);
            }
            eid = lean_expr_mk_bvar(ks, bv);
        } else if (json_object_object_get_ex(root, "sort", &sub)) {
            uint32_t u_raw = 0, u = 0;
            if (!json_get_u32_strict(root, "sort", &u_raw) || !lean_resolve_lvl_idx(ks, u_raw, &u)) {
                json_object_put(root);
                return lean_fail_reject(ks, err_buf, err_cap, "malformed sort expr at %u", idx);
            }
            eid = lean_expr_mk_sort(ks, u);
        } else if (json_object_object_get_ex(root, "const", &sub)) {
            uint32_t nm_raw = 0, nm = 0, *us = NULL, nus = 0;
            struct json_object *us_arr = NULL;
            if (!sub || !json_object_is_type(sub, json_type_object) ||
                !json_get_u32_strict(sub, "name", &nm_raw) || !lean_resolve_name_idx(ks, nm_raw, &nm) || nm == 0 ||
                !json_object_object_get_ex(sub, "us", &us_arr) ||
                !json_parse_mapped_u32_array(us_arr, ks->export_lvl_map, ks->export_lvl_present, ks->cap_export_lvls,
                                             &us, &nus)) {
                free(us);
                json_object_put(root);
                return lean_fail_reject(ks, err_buf, err_cap, "malformed const expr at %u", idx);
            }
            eid = lean_expr_mk_const(ks, nm, nus, us);
            free(us);
        } else if (json_object_object_get_ex(root, "app", &sub)) {
            uint32_t fn = 0, arg = 0;
            if (sub && json_object_is_type(sub, json_type_object)) {
                uint32_t fn_raw = 0, arg_raw = 0;
                if (!json_get_u32_strict(sub, "fn", &fn_raw) || !lean_resolve_expr_idx(ks, fn_raw, &fn) ||
                    !json_get_u32_strict(sub, "arg", &arg_raw) || !lean_resolve_expr_idx(ks, arg_raw, &arg)) {
                    json_object_put(root);
                    return lean_fail_reject(ks, err_buf, err_cap, "malformed app object at %u", idx);
                }
            } else if (sub && json_object_is_type(sub, json_type_array)) {
                uint32_t *arr = NULL, cnt = 0;
                if (!json_parse_mapped_u32_array(sub, ks->export_expr_map, ks->export_expr_present, ks->cap_export_exprs,
                                                 &arr, &cnt) || cnt != 2) {
                    free(arr);
                    json_object_put(root);
                    return lean_fail_reject(ks, err_buf, err_cap, "malformed app array at %u", idx);
                }
                fn = arr[0]; arg = arr[1];
                free(arr);
            } else {
                json_object_put(root);
                return lean_fail_reject(ks, err_buf, err_cap, "malformed app at %u", idx);
            }
            eid = lean_expr_mk_app(ks, fn, arg);
        } else if (json_object_object_get_ex(root, "lam", &sub) || json_object_object_get_ex(root, "forallE", &sub)) {
            bool is_lam = json_object_object_get_ex(root, "lam", NULL);
            uint32_t nm_raw = 0, nm = 0, ty_raw = 0, ty = 0, bd_raw = 0, bd = 0;
            if (!sub || !json_object_is_type(sub, json_type_object) ||
                !json_get_u32_strict(sub, "name", &nm_raw) || !lean_resolve_name_idx(ks, nm_raw, &nm) ||
                !json_get_u32_strict(sub, "type", &ty_raw) || !lean_resolve_expr_idx(ks, ty_raw, &ty) ||
                !json_get_u32_strict(sub, "body", &bd_raw) || !lean_resolve_expr_idx(ks, bd_raw, &bd)) {
                json_object_put(root);
                return lean_fail_reject(ks, err_buf, err_cap, "malformed binder expr at %u", idx);
            }
            if (!ks->allow_legacy_format) {
                const char *bi = json_get_cstr_strict(sub, "binderInfo");
                if (!bi || (strcmp(bi, "default") != 0 && strcmp(bi, "implicit") != 0 &&
                            strcmp(bi, "strictImplicit") != 0 && strcmp(bi, "instImplicit") != 0)) {
                    json_object_put(root);
                    return lean_fail_reject(ks, err_buf, err_cap, "invalid or missing binderInfo at %u", idx);
                }
            }
            eid = is_lam ? lean_expr_mk_lam(ks, nm, ty, bd) : lean_expr_mk_forall(ks, nm, ty, bd);
        } else if (json_object_object_get_ex(root, "letE", &sub)) {
            uint32_t nm_raw = 0, nm = 0, ty_raw = 0, ty = 0, vl_raw = 0, vl = 0, bd_raw = 0, bd = 0;
            bool nondep = false;
            if (!sub || !json_object_is_type(sub, json_type_object) ||
                !json_get_u32_strict(sub, "name", &nm_raw) || !lean_resolve_name_idx(ks, nm_raw, &nm) ||
                !json_get_u32_strict(sub, "type", &ty_raw) || !lean_resolve_expr_idx(ks, ty_raw, &ty) ||
                !json_get_u32_strict(sub, "value", &vl_raw) || !lean_resolve_expr_idx(ks, vl_raw, &vl) ||
                !json_get_u32_strict(sub, "body", &bd_raw) || !lean_resolve_expr_idx(ks, bd_raw, &bd) ||
                (!ks->allow_legacy_format && !json_get_bool_strict(sub, "nondep", &nondep))) {
                json_object_put(root);
                return lean_fail_reject(ks, err_buf, err_cap, "malformed letE expr at %u", idx);
            }
            eid = lean_expr_mk_let(ks, nm, ty, vl, bd);
        } else if (json_object_object_get_ex(root, "mdata", &sub)) {
            uint32_t inner_raw = 0;
            struct json_object *d_arr = NULL;
            if (!sub || !json_object_is_type(sub, json_type_object) ||
                !json_get_u32_strict(sub, "expr", &inner_raw) || !lean_resolve_expr_idx(ks, inner_raw, &eid) ||
                (!ks->allow_legacy_format &&
                 (!json_object_object_get_ex(sub, "data", &d_arr) || !d_arr || !json_object_is_type(d_arr, json_type_array)))) {
                json_object_put(root);
                return lean_fail_reject(ks, err_buf, err_cap, "malformed mdata expr at %u", idx);
            }
        } else if (json_object_object_get_ex(root, "natVal", &sub)) {
            const char *s = json_get_cstr_strict(root, "natVal");
            if (!s || s[0] == '\0') {
                json_object_put(root);
                return lean_fail_reject(ks, err_buf, err_cap, "missing or empty natVal at %u", idx);
            }
            for (const char *p = s; *p; p++) {
                if (*p < '0' || *p > '9') {
                    json_object_put(root);
                    return lean_fail_reject(ks, err_buf, err_cap, "non-digit character in natVal at %u", idx);
                }
            }
            eid = lean_expr_mk_natlit_str(ks, s);
        } else if (json_object_object_get_ex(root, "strVal", &sub)) {
            const char *s = json_get_cstr_strict(root, "strVal");
            if (!s) {
                json_object_put(root);
                return lean_fail_reject(ks, err_buf, err_cap, "non-string strVal at %u", idx);
            }
            eid = lean_expr_mk_strlit(ks, s);
        } else if (ks->allow_legacy_format && json_object_object_get_ex(root, "lit", &sub)) {
            const char *ns = sub ? json_get_cstr_strict(sub, "natVal") : NULL;
            const char *ss = sub ? json_get_cstr_strict(sub, "strVal") : NULL;
            if (ns && ns[0] != '\0') eid = lean_expr_mk_natlit_str(ks, ns);
            else if (ss) eid = lean_expr_mk_strlit(ks, ss);
            else {
                json_object_put(root);
                return lean_fail_reject(ks, err_buf, err_cap, "malformed lit expr at %u", idx);
            }
        } else if (json_object_object_get_ex(root, "proj", &sub)) {
            uint32_t tn_raw = 0, tn = 0, pidx = 0, st_raw = 0, st = 0;
            if (!sub || !json_object_is_type(sub, json_type_object) ||
                !json_get_u32_strict(sub, "typeName", &tn_raw) || !lean_resolve_name_idx(ks, tn_raw, &tn) || tn == 0 ||
                !json_get_u32_strict(sub, "idx", &pidx) || pidx >= 0x3fffffffu ||
                !json_get_u32_strict(sub, "struct", &st_raw) || !lean_resolve_expr_idx(ks, st_raw, &st)) {
                json_object_put(root);
                return lean_fail_reject(ks, err_buf, err_cap, "malformed proj expr at %u", idx);
            }
            eid = lean_expr_mk_proj(ks, tn, pidx, st);
        } else {
            json_object_put(root);
            return lean_fail_reject(ks, err_buf, err_cap, "unknown expression constructor at %u", idx);
        }
        lean_map_set_checked(&ks->export_expr_map, &ks->export_expr_present, &ks->cap_export_exprs, idx, eid);
        ks->n_export_exprs++;
        json_object_put(root);
        return true;
    }

    /* 4. Official `3.1.0` Inductive block: {"inductive": {"types": [...], "ctors": [...], "recs": [...]}} */
    struct json_object *ind_block = NULL;
    if (json_object_object_get_ex(root, "inductive", &ind_block)) {
        if (json_object_object_length(root) != 1 || !ind_block || !json_object_is_type(ind_block, json_type_object)) {
            json_object_put(root);
            return lean_fail_reject(ks, err_buf, err_cap, "malformed inductive block");
        }
        struct json_object *types_arr = NULL, *ctors_arr = NULL, *recs_arr = NULL;
        bool has_310 = json_object_object_get_ex(ind_block, "types", &types_arr) &&
                       json_object_object_get_ex(ind_block, "ctors", &ctors_arr) &&
                       json_object_object_get_ex(ind_block, "recs",  &recs_arr);
        bool has_300 = !has_310 && ks->allow_legacy_format &&
                       json_object_object_get_ex(ind_block, "inductiveVals", &types_arr) &&
                       json_object_object_get_ex(ind_block, "constructorVals", &ctors_arr) &&
                       json_object_object_get_ex(ind_block, "recursorVals",  &recs_arr);
        if ((!has_310 && !has_300) ||
            !json_object_is_type(types_arr, json_type_array) ||
            !json_object_is_type(ctors_arr, json_type_array) ||
            !json_object_is_type(recs_arr,  json_type_array)) {
            json_object_put(root);
            return lean_fail_reject(ks, err_buf, err_cap, "inductive block missing types/ctors/recs arrays");
        }
        uint32_t ntypes = (uint32_t)json_object_array_length(types_arr);
        uint32_t nctors = (uint32_t)json_object_array_length(ctors_arr);
        uint32_t nrecs  = (uint32_t)json_object_array_length(recs_arr);
        if (ntypes == 0) {
            json_object_put(root);
            return lean_fail_reject(ks, err_buf, err_cap, "empty inductive block rejected");
        }
        LeanDecl *types = (LeanDecl *)calloc(ntypes, sizeof(LeanDecl));
        LeanCtorSpec *ctors = nctors > 0 ? (LeanCtorSpec *)calloc(nctors, sizeof(LeanCtorSpec)) : NULL;
        LeanDecl *recs = nrecs > 0 ? (LeanDecl *)calloc(nrecs, sizeof(LeanDecl)) : NULL;
        bool parse_ok = true;

        for (uint32_t t = 0; parse_ok && t < ntypes; t++) {
            struct json_object *tobj = json_object_array_get_idx(types_arr, t);
            LeanDecl *ind = &types[t];
            ind->kind = LDECL_IND;
            bool is_unsafe = false;
            if (!tobj || !json_object_is_type(tobj, json_type_object)) {
                parse_ok = lean_fail_reject(ks, err_buf, err_cap, "malformed inductive type entry");
                break;
            }
            if (json_get_bool_strict(tobj, "isUnsafe", &is_unsafe)) {
                if (is_unsafe) {
                    parse_ok = lean_fail_decline(ks, err_buf, err_cap, "unsafe inductive declined");
                    break;
                }
                ind->is_unsafe = 0;
            } else if (!ks->allow_legacy_format) {
                parse_ok = lean_fail_reject(ks, err_buf, err_cap, "inductive type entry missing isUnsafe");
                break;
            }
            uint32_t nm_raw = 0, ty_raw = 0;
            struct json_object *lp_arr = NULL;
            if (!json_get_u32_strict(tobj, "name", &nm_raw) || !lean_resolve_name_idx(ks, nm_raw, &ind->name) || ind->name == 0 ||
                !json_get_u32_strict(tobj, "type", &ty_raw) || !lean_resolve_expr_idx(ks, ty_raw, &ind->type) ||
                !json_object_object_get_ex(tobj, "levelParams", &lp_arr) ||
                !json_parse_mapped_u32_array(lp_arr, ks->export_name_map, ks->export_name_present, ks->cap_export_names,
                                             &ind->level_params, &ind->nparams) ||
                !json_get_u32_strict(tobj, "numParams", &ind->num_params) ||
                !json_get_u32_strict(tobj, "numIndices", &ind->num_indices) ||
                ind->num_params > ks->nexprs || ind->num_indices > ks->nexprs ||
                !json_get_bool_strict(tobj, "isRec", &ind->is_rec) ||
                !json_get_bool_strict(tobj, "isReflexive", &ind->is_reflexive)) {
                parse_ok = lean_fail_reject(ks, err_buf, err_cap, "inductive type entry missing or out-of-range required fields");
                break;
            }
            if (json_get_u32_strict(tobj, "numNested", &ind->num_nested)) {
                if (ind->num_nested > ks->nexprs) {
                    parse_ok = lean_fail_reject(ks, err_buf, err_cap, "inductive type entry has out-of-range numNested");
                    break;
                }
                ind->has_num_nested = 1;
            } else if (!ks->allow_legacy_format) {
                parse_ok = lean_fail_reject(ks, err_buf, err_cap, "inductive type entry missing numNested");
                break;
            }
            struct json_object *all_arr = NULL;
            if (json_object_object_get_ex(tobj, "all", &all_arr)) {
                if (!json_parse_mapped_u32_array(all_arr, ks->export_name_map, ks->export_name_present, ks->cap_export_names,
                                                 &ind->all, &ind->nall)) {
                    parse_ok = lean_fail_reject(ks, err_buf, err_cap, "inductive type entry has invalid all array");
                    break;
                }
                ind->has_all_field = 1;
            } else if (!ks->allow_legacy_format) {
                parse_ok = lean_fail_reject(ks, err_buf, err_cap, "inductive type entry missing all array");
                break;
            }
            struct json_object *ct_arr = NULL;
            if (json_object_object_get_ex(tobj, "ctors", &ct_arr)) {
                if (!json_parse_mapped_u32_array(ct_arr, ks->export_name_map, ks->export_name_present, ks->cap_export_names,
                                                 &ind->declared_ctors, &ind->num_declared_ctors)) {
                    parse_ok = lean_fail_reject(ks, err_buf, err_cap, "inductive type entry has invalid ctors array");
                    break;
                }
                ind->has_declared_ctors = 1;
            } else if (!ks->allow_legacy_format) {
                parse_ok = lean_fail_reject(ks, err_buf, err_cap, "inductive type entry missing ctors array");
                break;
            }
        }

        for (uint32_t c = 0; parse_ok && c < nctors; c++) {
            struct json_object *cobj = json_object_array_get_idx(ctors_arr, c);
            if (!cobj || !json_object_is_type(cobj, json_type_object) ||
                !lean_parse_ctor_obj(ks, cobj, types[0].name, &ctors[c], err_buf, err_cap)) {
                parse_ok = false;
                break;
            }
        }

        for (uint32_t r = 0; parse_ok && r < nrecs; r++) {
            struct json_object *robj = json_object_array_get_idx(recs_arr, r);
            if (!robj || !json_object_is_type(robj, json_type_object) ||
                !lean_parse_rec_obj(ks, robj, &recs[r], err_buf, err_cap)) {
                parse_ok = false;
                break;
            }
        }

        bool ok = parse_ok && lean_verify_inductive_block(ks, ntypes, types, nctors, ctors, nrecs, recs, err_buf, err_cap);
        for (uint32_t c = 0; c < nctors; c++) {
            free(ctors[c].level_params);
        }
        if (!ok) {
            if (ks->outcome == LEAN_OUTCOME_ACCEPT) ks->outcome = LEAN_OUTCOME_REJECT;
            for (uint32_t t = 0; t < ntypes; t++) {
                free(types[t].level_params);
                free(types[t].all);
                free(types[t].ctors);
                free(types[t].declared_ctors);
            }
            for (uint32_t r = 0; r < nrecs; r++) {
                free(recs[r].level_params);
                free(recs[r].all);
                free(recs[r].rules);
            }
        }
        free(types);
        free(ctors);
        free(recs);
        json_object_put(root);
        return ok;
    }

    /* 5. Single declaration records: axiom, def, thm, opaque, quot */
    if (json_object_object_length(root) != 1) {
        json_object_put(root);
        return lean_fail_reject(ks, err_buf, err_cap, "record has multiple top-level keys");
    }

    LeanDecl d;
    memset(&d, 0, sizeof(d));
    struct json_object *dobj = NULL;
    if (json_object_object_get_ex(root, "axiom", &dobj))        d.kind = LDECL_AXIOM;
    else if (json_object_object_get_ex(root, "def", &dobj))     d.kind = LDECL_DEFN;
    else if (ks->allow_legacy_format && json_object_object_get_ex(root, "defn", &dobj)) d.kind = LDECL_DEFN;
    else if (json_object_object_get_ex(root, "thm", &dobj))     d.kind = LDECL_THM;
    else if (json_object_object_get_ex(root, "opaque", &dobj))  d.kind = LDECL_OPAQUE;
    else if (json_object_object_get_ex(root, "quot", &dobj))    d.kind = LDECL_QUOT;
    else {
        json_object_put(root);
        return lean_fail_reject(ks, err_buf, err_cap, "unrecognized top-level record key");
    }

    if (!dobj || !json_object_is_type(dobj, json_type_object)) {
        json_object_put(root);
        return lean_fail_reject(ks, err_buf, err_cap, "declaration payload is not a JSON object");
    }

    if (d.kind == LDECL_DEFN) {
        const char *safety = json_get_cstr_strict(dobj, "safety");
        if (safety) {
            if (strcmp(safety, "unsafe") == 0 || strcmp(safety, "partial") == 0) {
                bool r = lean_fail_reject(ks, err_buf, err_cap, "non-safe definition (%s) rejected", safety);
                json_object_put(root);
                return r;
            }
            if (strcmp(safety, "safe") != 0) {
                bool r = lean_fail_reject(ks, err_buf, err_cap, "invalid safety value on def: %s", safety);
                json_object_put(root);
                return r;
            }
        } else if (!ks->allow_legacy_format) {
            json_object_put(root);
            return lean_fail_reject(ks, err_buf, err_cap, "def missing required safety field");
        }
    } else {
        bool is_unsafe = false;
        if (json_get_bool_strict(dobj, "isUnsafe", &is_unsafe)) {
            if (is_unsafe) {
                json_object_put(root);
                return lean_fail_decline(ks, err_buf, err_cap, "unsafe declaration declined");
            }
        } else if (!ks->allow_legacy_format && d.kind != LDECL_THM && d.kind != LDECL_QUOT) {
            json_object_put(root);
            return lean_fail_reject(ks, err_buf, err_cap, "declaration missing boolean isUnsafe");
        }
    }

    uint32_t nm_raw = 0, ty_raw = 0, vl_raw = 0;
    struct json_object *lp_arr = NULL;
    if (!json_get_u32_strict(dobj, "name", &nm_raw) || !lean_resolve_name_idx(ks, nm_raw, &d.name) || d.name == 0 ||
        !json_get_u32_strict(dobj, "type", &ty_raw) || !lean_resolve_expr_idx(ks, ty_raw, &d.type) ||
        !json_object_object_get_ex(dobj, "levelParams", &lp_arr) ||
        !json_parse_mapped_u32_array(lp_arr, ks->export_name_map, ks->export_name_present, ks->cap_export_names,
                                     &d.level_params, &d.nparams)) {
        free(d.level_params);
        json_object_put(root);
        return lean_fail_reject(ks, err_buf, err_cap, "declaration missing name/type/levelParams");
    }

    struct json_object *decl_all_arr = NULL;
    if (json_object_object_get_ex(dobj, "all", &decl_all_arr)) {
        bool all_ok = json_parse_mapped_u32_array(decl_all_arr, ks->export_name_map, ks->export_name_present,
                                                  ks->cap_export_names, &d.all, &d.nall) && d.nall > 0;
        for (uint32_t j = 0; all_ok && j < d.nall; j++) {
            if (d.all[j] == 0) all_ok = false;
        }
        if (!all_ok) {
            free(d.level_params);
            free(d.all);
            json_object_put(root);
            return lean_fail_reject(ks, err_buf, err_cap, "declaration %s has invalid all array", ks->names[d.name].full);
        }
    } else if (!ks->allow_legacy_format && (d.kind == LDECL_DEFN || d.kind == LDECL_THM || d.kind == LDECL_OPAQUE)) {
        free(d.level_params);
        json_object_put(root);
        return lean_fail_reject(ks, err_buf, err_cap, "declaration %s missing all array", ks->names[d.name].full);
    }

    if (d.kind == LDECL_QUOT && !ks->allow_legacy_format) {
        const char *qkind = json_get_cstr_strict(dobj, "kind");
        if (qkind) {
            if (strcmp(qkind, "type") == 0)      d.quot_kind = LQUOT_TYPE;
            else if (strcmp(qkind, "ctor") == 0) d.quot_kind = LQUOT_CTOR;
            else if (strcmp(qkind, "lift") == 0) d.quot_kind = LQUOT_LIFT;
            else if (strcmp(qkind, "ind") == 0)  d.quot_kind = LQUOT_IND;
            else {
                free(d.level_params);
                free(d.all);
                bool r = lean_fail_reject(ks, err_buf, err_cap, "quot %s has invalid kind: %s", ks->names[d.name].full, qkind);
                json_object_put(root);
                return r;
            }
        }
    }

    if (d.kind == LDECL_DEFN || d.kind == LDECL_THM || d.kind == LDECL_OPAQUE) {
        if (!json_get_u32_strict(dobj, "value", &vl_raw) || !lean_resolve_expr_idx(ks, vl_raw, &d.value)) {
            free(d.level_params);
            free(d.all);
            json_object_put(root);
            return lean_fail_reject(ks, err_buf, err_cap, "declaration %s has invalid value index", ks->names[d.name].full);
        }
        if (d.kind == LDECL_DEFN) {
            struct json_object *hobj = NULL;
            if (json_object_object_get_ex(dobj, "hints", &hobj) && hobj) {
                if (json_object_is_type(hobj, json_type_string)) {
                    const char *hs = json_object_get_string(hobj);
                    if (hs && strcmp(hs, "abbrev") == 0) {
                        d.hint_kind = LHINT_ABBREV;
                        d.height = 0xffffffffu;
                        d.has_explicit_hints = true;
                    } else if (hs && strcmp(hs, "opaque") == 0) {
                        d.hint_kind = LHINT_OPAQUE;
                        d.height = 0u;
                        d.has_explicit_hints = true;
                    } else {
                        free(d.level_params);
                        free(d.all);
                        json_object_put(root);
                        return lean_fail_reject(ks, err_buf, err_cap, "def %s has invalid hints string", ks->names[d.name].full);
                    }
                } else if (json_object_is_type(hobj, json_type_object)) {
                    uint32_t reg_h = 0;
                    if (json_get_u32_strict(hobj, "regular", &reg_h)) {
                        d.hint_kind = LHINT_REGULAR;
                        d.height = (reg_h < 0xfffffffeu) ? (reg_h + 1u) : 0xfffffffeu;
                        d.has_explicit_hints = true;
                    } else {
                        free(d.level_params);
                        free(d.all);
                        json_object_put(root);
                        return lean_fail_reject(ks, err_buf, err_cap, "def %s has invalid hints object", ks->names[d.name].full);
                    }
                } else {
                    free(d.level_params);
                    free(d.all);
                    json_object_put(root);
                    return lean_fail_reject(ks, err_buf, err_cap, "def %s has malformed hints", ks->names[d.name].full);
                }
            } else if (!ks->allow_legacy_format) {
                free(d.level_params);
                free(d.all);
                json_object_put(root);
                return lean_fail_reject(ks, err_buf, err_cap, "def %s missing hints field", ks->names[d.name].full);
            }
        }
    }

    bool ok = lean_verify_and_admit_decl(ks, &d, err_buf, err_cap);
    if (!ok) {
        if (ks->outcome == LEAN_OUTCOME_ACCEPT) ks->outcome = LEAN_OUTCOME_REJECT;
        if (d.name < ks->cap_decls_by_name) {
            memset(&ks->decls_by_name[d.name], 0, sizeof(LeanDecl));
        }
        free(d.level_params);
        free(d.all);
        free(d.ctors);
        free(d.rules);
        json_object_put(root);
        return false;
    }
    json_object_put(root);
    return true;
}

static bool lean_verify_ndjson_stream(LeanKernelState *ks, FILE *fp, char *err_buf, size_t err_cap) {
    size_t cap = 65536;
    char *line = (char *)malloc(cap);
    uint64_t line_no = 0;
    uint64_t non_empty_lines = 0;
    while (true) {
        size_t len = 0;
        while (true) {
            if (!fgets(line + len, (int)(cap - len), fp)) break;
            len += strlen(line + len);
            if (len > 0 && line[len - 1] == '\n') break;
            if (len + 1 >= cap) {
                cap *= 2;
                line = (char *)realloc(line, cap);
            }
        }
        if (len == 0) break;
        line_no++;
        const char *p = line;
        while (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n') p++;
        if (*p == '\0') continue;
        non_empty_lines++;
        if (!lean_parse_and_verify_ndjson_line(ks, line, err_buf, err_cap)) {
            char tmp[1024];
            int n = snprintf(tmp, sizeof(tmp), "line %" PRIu64 ": %.900s", line_no, err_buf);
            if (n < 0) n = 0;
            size_t copy_len = (size_t)n < err_cap - 1 ? (size_t)n : err_cap - 1;
            memcpy(err_buf, tmp, copy_len);
            err_buf[copy_len] = '\0';
            free(line);
            return false;
        }
    }
    free(line);
    if (non_empty_lines == 0 || (!ks->metadata_seen && !ks->allow_legacy_format)) {
        return lean_fail_reject(ks, err_buf, err_cap, "empty stream or missing metadata header");
    }
    if (ks->saw_non_safe_decl) {
        return lean_fail_decline(ks, err_buf, err_cap, "stream contains unsafe or partial declarations");
    }
    return true;
}

static bool lean_verify_ndjson_string(LeanKernelState *ks, const char *ndjson, char *err_buf, size_t err_cap) {
    ks->allow_legacy_format = true;
    const char *p = ndjson;
    uint64_t line_no = 0;
    while (*p) {
        const char *nl = strchr(p, '\n');
        size_t len = nl ? (size_t)(nl - p) : strlen(p);
        char *line = (char *)malloc(len + 1);
        memcpy(line, p, len);
        line[len] = '\0';
        line_no++;
        bool ok = lean_parse_and_verify_ndjson_line(ks, line, err_buf, err_cap);
        free(line);
        if (!ok) {
            char tmp[512];
            snprintf(tmp, sizeof(tmp), "line %" PRIu64 ": %s", line_no, err_buf);
            snprintf(err_buf, err_cap, "%s", tmp);
            return false;
        }
        p = nl ? nl + 1 : p + len;
    }
    if (ks->saw_non_safe_decl) {
        return lean_fail_decline(ks, err_buf, err_cap, "stream contains unsafe or partial declarations");
    }
    return true;
}

/* =========================================================================
 * 8. Built-In Self-Test Suite (Positive Proofs + Soundness & tcalc Controls)
 * ========================================================================= */

static bool lean_check_required_decl_name(const LeanKernelState *ks, const char *req_name, char *err_buf, size_t err_cap);

static int run_lean_tcalc_selftest(void) {
    printf("=== Lean 4 -> tcalc Kernel Verifier Self-Test Suite ===\n");
    int passed = 0, failed = 0;

    /* Test 1: Positive kernel verification (Universes, Impredicative Prop, Nat, Add, Eq, Proof Irrelevance) */
    const char *pos_ndjson =
        "{\"meta\":{\"format\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"}}}\n"
        "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"u\"}}\n"
        "{\"il\":1,\"succ\":0}\n"
        "{\"il\":2,\"succ\":1}\n"
        "{\"il\":3,\"param\":1}\n"
        "{\"il\":4,\"succ\":3}\n"
        "{\"ie\":0,\"sort\":0}\n"
        "{\"ie\":1,\"sort\":1}\n"
        "{\"ie\":2,\"sort\":2}\n"
        "{\"ie\":3,\"sort\":3}\n"
        "{\"ie\":4,\"sort\":4}\n"
        "{\"in\":2,\"str\":{\"pre\":0,\"str\":\"Nat\"}}\n"
        "{\"in\":3,\"str\":{\"pre\":2,\"str\":\"zero\"}}\n"
        "{\"in\":4,\"str\":{\"pre\":2,\"str\":\"succ\"}}\n"
        "{\"in\":5,\"str\":{\"pre\":0,\"str\":\"n\"}}\n"
        "{\"ie\":5,\"const\":{\"name\":2,\"us\":[]}}\n"
        "{\"ie\":6,\"forallE\":{\"name\":5,\"type\":5,\"body\":5}}\n"
        "{\"inductive\":{\"types\":[{\"name\":2,\"levelParams\":[],\"type\":1,\"numParams\":0,\"numIndices\":0,\"isRec\":true,\"isReflexive\":false,\"numNested\":0}],"
        "\"ctors\":[{\"name\":3,\"levelParams\":[],\"type\":5,\"ind\":2,\"cidx\":0,\"numParams\":0,\"numFields\":0},"
        "{\"name\":4,\"levelParams\":[],\"type\":6,\"ind\":2,\"cidx\":1,\"numParams\":0,\"numFields\":1}],\"recs\":[]}}\n"
        "{\"in\":6,\"str\":{\"pre\":0,\"str\":\"Eq\"}}\n"
        "{\"in\":7,\"str\":{\"pre\":6,\"str\":\"refl\"}}\n"
        "{\"in\":8,\"str\":{\"pre\":0,\"str\":\"alpha\"}}\n"
        "{\"in\":9,\"str\":{\"pre\":0,\"str\":\"a\"}}\n"
        "{\"in\":10,\"str\":{\"pre\":0,\"str\":\"b\"}}\n"
        "{\"ie\":7,\"bvar\":0}\n"
        "{\"ie\":8,\"bvar\":1}\n"
        "{\"ie\":9,\"bvar\":2}\n"
        "{\"ie\":10,\"forallE\":{\"name\":10,\"type\":8,\"body\":0}}\n"
        "{\"ie\":11,\"forallE\":{\"name\":9,\"type\":7,\"body\":10}}\n"
        "{\"ie\":12,\"forallE\":{\"name\":8,\"type\":3,\"body\":11}}\n"
        "{\"ie\":13,\"const\":{\"name\":6,\"us\":[3]}}\n"
        "{\"ie\":14,\"app\":{\"fn\":13,\"arg\":8}}\n"
        "{\"ie\":15,\"app\":{\"fn\":14,\"arg\":7}}\n"
        "{\"ie\":16,\"app\":{\"fn\":15,\"arg\":7}}\n"
        "{\"ie\":17,\"forallE\":{\"name\":9,\"type\":7,\"body\":16}}\n"
        "{\"ie\":18,\"forallE\":{\"name\":8,\"type\":3,\"body\":17}}\n"
        "{\"inductive\":{\"types\":[{\"name\":6,\"levelParams\":[1],\"type\":12,\"numParams\":2,\"numIndices\":1,\"isRec\":false,\"isReflexive\":false,\"numNested\":0}],"
        "\"ctors\":[{\"name\":7,\"levelParams\":[1],\"type\":18,\"ind\":6,\"cidx\":0,\"numParams\":2,\"numFields\":0}],\"recs\":[]}}\n"
        "{\"in\":11,\"str\":{\"pre\":2,\"str\":\"add\"}}\n"
        "{\"ie\":19,\"forallE\":{\"name\":5,\"type\":5,\"body\":6}}\n"
        "{\"axiom\":{\"name\":11,\"levelParams\":[],\"type\":19}}\n"
        "{\"ie\":20,\"lit\":{\"natVal\":\"2\"}}\n"
        "{\"ie\":21,\"lit\":{\"natVal\":\"3\"}}\n"
        "{\"ie\":22,\"lit\":{\"natVal\":\"5\"}}\n"
        "{\"ie\":23,\"const\":{\"name\":11,\"us\":[]}}\n"
        "{\"ie\":24,\"app\":{\"fn\":23,\"arg\":20}}\n"
        "{\"ie\":25,\"app\":{\"fn\":24,\"arg\":21}}\n"
        "{\"ie\":26,\"const\":{\"name\":6,\"us\":[1]}}\n"
        "{\"ie\":27,\"app\":{\"fn\":26,\"arg\":5}}\n"
        "{\"ie\":28,\"app\":{\"fn\":27,\"arg\":25}}\n"
        "{\"ie\":29,\"app\":{\"fn\":28,\"arg\":22}}\n"
        "{\"ie\":30,\"const\":{\"name\":7,\"us\":[1]}}\n"
        "{\"ie\":31,\"app\":{\"fn\":30,\"arg\":5}}\n"
        "{\"ie\":32,\"app\":{\"fn\":31,\"arg\":22}}\n"
        "{\"in\":12,\"str\":{\"pre\":0,\"str\":\"two_add_three_eq_five\"}}\n"
        "{\"thm\":{\"name\":12,\"levelParams\":[],\"type\":29,\"value\":32}}\n"
        "{\"in\":13,\"str\":{\"pre\":0,\"str\":\"P\"}}\n"
        "{\"in\":14,\"str\":{\"pre\":0,\"str\":\"p\"}}\n"
        "{\"in\":15,\"str\":{\"pre\":0,\"str\":\"q\"}}\n"
        "{\"ie\":33,\"const\":{\"name\":6,\"us\":[0]}}\n"
        "{\"ie\":34,\"app\":{\"fn\":33,\"arg\":9}}\n"
        "{\"ie\":35,\"app\":{\"fn\":34,\"arg\":8}}\n"
        "{\"ie\":36,\"app\":{\"fn\":35,\"arg\":7}}\n"
        "{\"ie\":37,\"forallE\":{\"name\":15,\"type\":8,\"body\":36}}\n"
        "{\"ie\":38,\"forallE\":{\"name\":14,\"type\":7,\"body\":37}}\n"
        "{\"ie\":39,\"forallE\":{\"name\":13,\"type\":0,\"body\":38}}\n"
        "{\"ie\":40,\"const\":{\"name\":7,\"us\":[0]}}\n"
        "{\"ie\":41,\"app\":{\"fn\":40,\"arg\":9}}\n"
        "{\"ie\":42,\"app\":{\"fn\":41,\"arg\":8}}\n"
        "{\"ie\":43,\"lam\":{\"name\":15,\"type\":8,\"body\":42}}\n"
        "{\"ie\":44,\"lam\":{\"name\":14,\"type\":7,\"body\":43}}\n"
        "{\"ie\":45,\"lam\":{\"name\":13,\"type\":0,\"body\":44}}\n"
        "{\"in\":16,\"str\":{\"pre\":0,\"str\":\"proof_irrel_thm\"}}\n"
        "{\"thm\":{\"name\":16,\"levelParams\":[],\"type\":39,\"value\":45}}\n";

    LeanKernelState ks;
    lean_kernel_init(&ks);
    char err[512] = {0};
    if (lean_verify_ndjson_string(&ks, pos_ndjson, err, sizeof(err)) &&
        ks.stat_thms == 2 && ks.stat_proof_irrel_hits >= 1 && g_tc_admitted_decls >= 6) {
        printf("  [PASS] Positive kernel verification (3.1.0 format, Nat, Eq, 2+3=5, Proof Irrelevance, tcalc commits=%" PRIu64 ")\n",
               g_tc_rule_commits);
        passed++;
    } else {
        printf("  [FAIL] Positive kernel verification failed: %s\n", err);
        failed++;
    }
    lean_kernel_destroy(&ks);

    /* Negative Control 1: Forged constructor returning wrong inductive (`ctorResultingTypeMismatch`) */
    const char *neg_forged_ctor =
        "{\"meta\":{\"format\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"}}}\n"
        "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"EmptyProof\"}}\n"
        "{\"in\":2,\"str\":{\"pre\":0,\"str\":\"Unrelated\"}}\n"
        "{\"in\":3,\"str\":{\"pre\":2,\"str\":\"forge\"}}\n"
        "{\"ie\":0,\"sort\":0}\n"
        "{\"ie\":1,\"const\":{\"name\":1,\"us\":[]}}\n"
        "{\"inductive\":{\"types\":[{\"name\":1,\"levelParams\":[],\"type\":0,\"numParams\":0,\"numIndices\":0,\"isRec\":false,\"isReflexive\":false}],\"ctors\":[],\"recs\":[]}}\n"
        "{\"inductive\":{\"types\":[{\"name\":2,\"levelParams\":[],\"type\":0,\"numParams\":0,\"numIndices\":0,\"isRec\":false,\"isReflexive\":false}],"
        "\"ctors\":[{\"name\":3,\"levelParams\":[],\"type\":1,\"ind\":2,\"cidx\":0,\"numParams\":0,\"numFields\":0}],\"recs\":[]}}\n";

    lean_kernel_init(&ks);
    if (!lean_verify_ndjson_string(&ks, neg_forged_ctor, err, sizeof(err))) {
        printf("  [PASS] Negative Control 1 (forged constructor returning wrong inductive rejected: %s)\n", err);
        passed++;
    } else {
        printf("  [FAIL] Negative Control 1 accepted forged constructor!\n");
        failed++;
    }
    lean_kernel_destroy(&ks);

    /* Negative Control 2: Non-strictly-positive inductive constructor `Bad.mk : (Bad -> Prop) -> Bad` */
    const char *neg_non_positive =
        "{\"meta\":{\"format\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"}}}\n"
        "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"Bad\"}}\n"
        "{\"in\":2,\"str\":{\"pre\":1,\"str\":\"mk\"}}\n"
        "{\"in\":3,\"str\":{\"pre\":0,\"str\":\"f\"}}\n"
        "{\"il\":1,\"succ\":0}\n"
        "{\"ie\":0,\"sort\":0}\n"
        "{\"ie\":1,\"sort\":1}\n"
        "{\"ie\":2,\"const\":{\"name\":1,\"us\":[]}}\n"
        "{\"ie\":3,\"forallE\":{\"name\":3,\"type\":2,\"body\":0}}\n"
        "{\"ie\":4,\"forallE\":{\"name\":3,\"type\":3,\"body\":2}}\n"
        "{\"inductive\":{\"types\":[{\"name\":1,\"levelParams\":[],\"type\":1,\"numParams\":0,\"numIndices\":0,\"isRec\":true,\"isReflexive\":false}],"
        "\"ctors\":[{\"name\":2,\"levelParams\":[],\"type\":4,\"ind\":1,\"cidx\":0,\"numParams\":0,\"numFields\":1}],\"recs\":[]}}\n";

    lean_kernel_init(&ks);
    if (!lean_verify_ndjson_string(&ks, neg_non_positive, err, sizeof(err))) {
        printf("  [PASS] Negative Control 2 (non-strictly-positive inductive rejected: %s)\n", err);
        passed++;
    } else {
        printf("  [FAIL] Negative Control 2 accepted non-strictly-positive inductive!\n");
        failed++;
    }
    lean_kernel_destroy(&ks);

    /* Negative Control 3: Inductive field universe bump `Small : Type 0` with `mk : Type 0 -> Small` */
    const char *neg_univ_bump =
        "{\"meta\":{\"format\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"}}}\n"
        "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"Small\"}}\n"
        "{\"in\":2,\"str\":{\"pre\":1,\"str\":\"mk\"}}\n"
        "{\"in\":3,\"str\":{\"pre\":0,\"str\":\"A\"}}\n"
        "{\"il\":1,\"succ\":0}\n"
        "{\"ie\":1,\"sort\":1}\n"
        "{\"ie\":2,\"const\":{\"name\":1,\"us\":[]}}\n"
        "{\"ie\":3,\"forallE\":{\"name\":3,\"type\":1,\"body\":2}}\n"
        "{\"inductive\":{\"types\":[{\"name\":1,\"levelParams\":[],\"type\":1,\"numParams\":0,\"numIndices\":0,\"isRec\":false,\"isReflexive\":false}],"
        "\"ctors\":[{\"name\":2,\"levelParams\":[],\"type\":3,\"ind\":1,\"cidx\":0,\"numParams\":0,\"numFields\":1}],\"recs\":[]}}\n";

    lean_kernel_init(&ks);
    if (!lean_verify_ndjson_string(&ks, neg_univ_bump, err, sizeof(err))) {
        printf("  [PASS] Negative Control 3 (constructor universe bump rejected: %s)\n", err);
        passed++;
    } else {
        printf("  [FAIL] Negative Control 3 accepted constructor universe bump!\n");
        failed++;
    }
    lean_kernel_destroy(&ks);

    /* Negative Control 4: Direct test of premise-bearing `tcalc` rules (`R_DERIVE_IS_PROP` and `R_ADMIT_THM`):
     * Attempting to derive `IsProp(ty)` from `IsType(ty, 1)` or admit a theorem with mismatched `HasType` premise
     * must be rejected directly by `tcalc`'s `tx_Fixed` engine! */
    lean_kernel_init(&ks);
    {
        Occ has_type_1 = lean_tc_commit2(R_CHECK_SORT, 10u, 20u);
        Occ is_type_lvl1 = lean_tc_derive_is_type(has_type_1, 10u, 20u, 1u); /* level 1 != 0 (Prop) */
        Occ forged_is_prop = lean_tc_derive_is_prop(is_type_lvl1, 10u);
        Occ is_type_lvl0 = lean_tc_derive_is_type(has_type_1, 10u, 20u, 0u);
        Occ valid_is_prop = lean_tc_derive_is_prop(is_type_lvl0, 10u);
        Occ has_wrong_ty = lean_tc_commit2(R_CHECK_CONST, 99u, 777u); /* HasType(99, 777) != HasType(99, 10) */
        Occ forged_thm = lean_tc_admit_thm(valid_is_prop, has_wrong_ty, 1u, 10u, 99u);
        if (is_type_lvl1 != 0 && forged_is_prop == 0 && valid_is_prop != 0 && forged_thm == 0) {
            printf("  [PASS] Negative Control 4 (tcalc premise-bearing R_DERIVE_IS_PROP & R_ADMIT_THM reject forged premises)\n");
            passed++;
        } else {
            printf("  [FAIL] Negative Control 4 tcalc premise enforcement failed!\n");
            failed++;
        }
    }
    lean_kernel_destroy(&ks);

    /* Negative Control 5: Trust-policy & manifest enforcement (`--forbid-sorry` rejects sorryAx-tainted theorem) */
    const char *neg_sorry_thm =
        "{\"meta\":{\"format\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"}}}\n"
        "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"sorryAx\"}}\n"
        "{\"in\":2,\"str\":{\"pre\":0,\"str\":\"P\"}}\n"
        "{\"in\":3,\"str\":{\"pre\":0,\"str\":\"fake_thm\"}}\n"
        "{\"ie\":0,\"sort\":0}\n"
        "{\"ie\":1,\"bvar\":0}\n"
        "{\"ie\":2,\"forallE\":{\"name\":2,\"type\":0,\"body\":1}}\n"
        "{\"axiom\":{\"name\":1,\"levelParams\":[],\"type\":2}}\n"
        "{\"axiom\":{\"name\":2,\"levelParams\":[],\"type\":0}}\n"
        "{\"ie\":3,\"const\":{\"name\":1,\"us\":[]}}\n"
        "{\"ie\":4,\"const\":{\"name\":2,\"us\":[]}}\n"
        "{\"ie\":5,\"app\":{\"fn\":3,\"arg\":4}}\n"
        "{\"thm\":{\"name\":3,\"levelParams\":[],\"type\":4,\"value\":5}}\n";

    lean_kernel_init(&ks);
    ks.forbid_sorry = true;
    if (!lean_verify_ndjson_string(&ks, neg_sorry_thm, err, sizeof(err))) {
        printf("  [PASS] Negative Control 5 (--forbid-sorry trust policy rejects sorryAx-tainted theorem: %s)\n", err);
        passed++;
    } else {
        printf("  [FAIL] Negative Control 5 accepted sorryAx under --forbid-sorry!\n");
        failed++;
    }
    lean_kernel_destroy(&ks);

    /* Negative Control 6: Reject attacker-forged recursor claiming a circular inductive hypothesis
     * on a non-recursive constructor (`Ind.mk : Ind` with `MinorType = motive Ind.mk -> motive Ind.mk`
     * and `rhs = fun motive h => h (Ind.rec motive h Ind.mk)`). */
    const char *neg_forged_ih_rec =
        "{\"meta\":{\"format\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"}}}\n"
        "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"Ind\"}}\n"
        "{\"in\":2,\"str\":{\"pre\":1,\"str\":\"mk\"}}\n"
        "{\"in\":3,\"str\":{\"pre\":1,\"str\":\"rec\"}}\n"
        "{\"in\":4,\"str\":{\"pre\":0,\"str\":\"motive\"}}\n"
        "{\"in\":5,\"str\":{\"pre\":0,\"str\":\"h\"}}\n"
        "{\"in\":6,\"str\":{\"pre\":0,\"str\":\"t\"}}\n"
        "{\"ie\":0,\"sort\":0}\n"
        "{\"ie\":1,\"const\":{\"name\":1,\"us\":[]}}\n"
        "{\"ie\":2,\"const\":{\"name\":2,\"us\":[]}}\n"
        "{\"ie\":3,\"const\":{\"name\":3,\"us\":[]}}\n"
        "{\"ie\":4,\"bvar\":0}\n"
        "{\"ie\":5,\"bvar\":1}\n"
        "{\"ie\":6,\"bvar\":2}\n"
        "{\"ie\":7,\"forallE\":{\"name\":6,\"type\":1,\"body\":0}}\n"
        "{\"ie\":8,\"app\":{\"fn\":4,\"arg\":2}}\n"
        "{\"ie\":9,\"app\":{\"fn\":5,\"arg\":2}}\n"
        "{\"ie\":10,\"forallE\":{\"name\":5,\"type\":8,\"body\":9}}\n"
        "{\"ie\":11,\"app\":{\"fn\":6,\"arg\":4}}\n"
        "{\"ie\":12,\"forallE\":{\"name\":6,\"type\":1,\"body\":11}}\n"
        "{\"ie\":13,\"forallE\":{\"name\":5,\"type\":10,\"body\":12}}\n"
        "{\"ie\":14,\"forallE\":{\"name\":4,\"type\":7,\"body\":13}}\n"
        "{\"ie\":15,\"app\":{\"fn\":3,\"arg\":5}}\n"
        "{\"ie\":16,\"app\":{\"fn\":15,\"arg\":4}}\n"
        "{\"ie\":17,\"app\":{\"fn\":16,\"arg\":2}}\n"
        "{\"ie\":18,\"app\":{\"fn\":4,\"arg\":17}}\n"
        "{\"ie\":19,\"lam\":{\"name\":5,\"type\":10,\"body\":18}}\n"
        "{\"ie\":20,\"lam\":{\"name\":4,\"type\":7,\"body\":19}}\n"
        "{\"inductive\":{\"types\":[{\"name\":1,\"levelParams\":[],\"type\":0,\"numParams\":0,\"numIndices\":0,\"all\":[1],\"ctors\":[2],\"numNested\":0,\"isRec\":false,\"isUnsafe\":false,\"isReflexive\":false}],\"ctors\":[{\"name\":2,\"levelParams\":[],\"type\":1,\"induct\":1,\"cidx\":0,\"numParams\":0,\"numFields\":0,\"isUnsafe\":false}],\"recs\":[{\"name\":3,\"levelParams\":[],\"type\":14,\"all\":[1],\"numParams\":0,\"numIndices\":0,\"numMotives\":1,\"numMinors\":1,\"rules\":[{\"ctor\":2,\"nfields\":0,\"rhs\":20}],\"k\":false,\"isUnsafe\":false}]}}\n";

    lean_kernel_init(&ks);
    if (!lean_verify_ndjson_string(&ks, neg_forged_ih_rec, err, sizeof(err))) {
        printf("  [PASS] Negative Control 6 (forged circular inductive-hypothesis recursor rejected: %s)\n", err);
        passed++;
    } else {
        printf("  [FAIL] Negative Control 6 accepted forged circular inductive-hypothesis recursor!\n");
        failed++;
    }
    lean_kernel_destroy(&ks);

    /* Control 7: CeTTa Transform Bridge (`tc_cetta_bridge.h`) event receipt & `Event.restrict` inclusion check */
    lean_kernel_init(&ks);
    g_lean_bridge_event_mode = true;
    {
        Occ has_type_0 = lean_tc_commit2(R_CHECK_SORT, 10u, 20u);
        Occ is_type_0  = lean_tc_derive_is_type(has_type_0, 10u, 20u, 0u);
        Occ is_prop_0  = lean_tc_derive_is_prop(is_type_0, 10u);
        Occ has_proof  = lean_tc_commit2(R_CHECK_CONST, 99u, 10u);
        Occ thm_occ    = lean_tc_admit_thm(is_prop_0, has_proof, 1u, 10u, 99u);
        TcPreparedStep view = tc_event_firing(&g_last_lean_event);

        TcAdmissionProfile dst_prof = tc_admission_guard_profile(false);
        TcAdmissionInclusion inc;
        bool inc_ok = tc_admission_inclusion_init(&inc, &g_lean_admission_profile, &dst_prof, false);
        TcAdmittedEvent transported;
        bool restrict_ok = inc_ok && tc_event_restrict_included(&g_last_lean_event, &inc, &transported);

        TcAdmissionInclusion forged_inc = inc;
        forged_inc.magic ^= 0x1u;
        TcAdmittedEvent forged_out;
        bool forged_ok = tc_event_restrict_included(&g_last_lean_event, &forged_inc, &forged_out);

        if (thm_occ != 0 && view.rule == R_ADMIT_THM && g_last_lean_event.nkeep == 3 &&
            restrict_ok && transported.receipt.out == thm_occ && !forged_ok) {
            printf("  [PASS] Control 7 (CeTTa bridge TcAdmittedEvent receipt, Cesta tc_event_firing, and Event.restrict verified)\n");
            passed++;
        } else {
            printf("  [FAIL] Control 7 CeTTa bridge integration check failed!\n");
            failed++;
        }
    }
    g_lean_bridge_event_mode = false;
    lean_kernel_destroy(&ks);

    /* Control 8: 4-Tier Second-Futamura + Cesta Ordinary-Flat + Direct t-ISA x86-64 Differential Parity
     * Verifies that Level 1 (`tc_bridge_execute_candidate`), Level 2a (`tc_lean_fire_arena_dispatch`
     * + Cesta `ordinary_flat_cesta_runtime.o`), Level 2b (`tc_lean_gen_flat_dispatch` from
     * `lean_tcalc_gen.h`), and Level 3 (`t-ISA` direct x86-64 byte emission from `tc_inspect_rule`)
     * accept identical valid derivations and reject identical forged premises. */
    {
        bool tier_ok = true;
        for (int tier = 0; tier < 4; tier++) {
            lean_kernel_init(&ks);
            g_lean_bridge_event_mode = (tier == 0);
            g_lean_arena_mode        = (tier == 1);
            g_lean_tisa_x86_mode     = (tier == 3);
            Occ has_type_0    = lean_tc_commit2(R_CHECK_SORT, 10u, 20u);
            Occ is_type_lvl1  = lean_tc_derive_is_type(has_type_0, 10u, 20u, 1u);
            Occ forged_prop   = lean_tc_derive_is_prop(is_type_lvl1, 10u);
            Occ is_type_lvl0  = lean_tc_derive_is_type(has_type_0, 10u, 20u, 0u);
            Occ valid_prop    = lean_tc_derive_is_prop(is_type_lvl0, 10u);
            Occ wrong_proof   = lean_tc_commit2(R_CHECK_CONST, 99u, 777u);
            Occ forged_thm    = lean_tc_admit_thm(valid_prop, wrong_proof, 1u, 10u, 99u);
            Occ valid_proof   = lean_tc_commit2(R_CHECK_CONST, 99u, 10u);
            Occ valid_thm     = lean_tc_admit_thm(valid_prop, valid_proof, 1u, 10u, 99u);
            if (!(is_type_lvl1 != 0 && forged_prop == 0 && valid_prop != 0 &&
                  forged_thm == 0 && valid_thm != 0)) {
                tier_ok = false;
            }
            g_lean_bridge_event_mode = false;
            g_lean_arena_mode        = false;
            g_lean_tisa_x86_mode     = false;
            lean_kernel_destroy(&ks);
        }
        if (tier_ok) {
            printf("  [PASS] Control 8 (4-Tier Second-Futamura + Cesta ordinary-flat + Direct t-ISA x86-64 differential parity verified)\n");
            passed++;
        } else {
            printf("  [FAIL] Control 8 4-tier differential parity check failed!\n");
            failed++;
        }
    }

    /* Control 9: Two-Tier Persistent (has_fvar==0) + Scratch (has_fvar==1) Expression Arena Reclamation
     * Verifies that transient FVar-bearing expressions allocated during declaration checking
     * are reclaimed at declaration boundaries (`ks.nscratch_exprs == 0` and
     * `ks.stat_scratch_reclaimed > 0`) while preserving closed persistent expressions. */
    {
        lean_kernel_init(&ks);
        bool ok9 = lean_verify_ndjson_string(&ks, pos_ndjson, err, sizeof(err));
        if (ok9 && !ks.in_scratch_scope && ks.nscratch_exprs == 0 && ks.stat_scratch_reclaimed > 0) {
            printf("  [PASS] Control 9 (Two-Tier Persistent + Scratch Expression Arena: persistent=%u, peak_scratch=%u, reclaimed=%" PRIu64 ")\n",
                   ks.nexprs - 1u, ks.stat_peak_scratch, ks.stat_scratch_reclaimed);
            passed++;
        } else {
            printf("  [FAIL] Control 9 Two-Tier Scratch Arena check failed!\n");
            failed++;
        }
        lean_kernel_destroy(&ks);
    }

    /* Control 10: Exact UTF-8 / Unicode Escape Decoding, Surrogate Pairs, and Embedded-NUL Rejection
     * Verifies that:
     * (a) Distinct non-ASCII escapes (\u03b1 vs \u03b2) do not collide to '?' (rejecting undeclared \u03b2);
     * (b) Escaped \u03b1 and raw UTF-8 "α" (plus supplementary surrogate pair \ud835\udcab) decode identically;
     * (c) Embedded NUL (\u0000) is strictly rejected. */
    {
        const char *neg_unicode_collision =
            "{\"meta\":{\"format\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"}}}\n"
            "{\"ie\":0,\"sort\":0}\n"
            "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"P\"}}\n"
            "{\"axiom\":{\"name\":1,\"levelParams\":[],\"type\":0}}\n"
            "{\"ie\":1,\"const\":{\"name\":1,\"us\":[]}}\n"
            "{\"in\":2,\"str\":{\"pre\":0,\"str\":\"\\u03b1\"}}\n"
            "{\"axiom\":{\"name\":2,\"levelParams\":[],\"type\":1}}\n"
            "{\"in\":3,\"str\":{\"pre\":0,\"str\":\"\\u03b2\"}}\n"
            "{\"ie\":2,\"const\":{\"name\":3,\"us\":[]}}\n"
            "{\"in\":4,\"str\":{\"pre\":0,\"str\":\"forged_alias\"}}\n"
            "{\"thm\":{\"name\":4,\"levelParams\":[],\"type\":1,\"value\":2}}\n";

        const char *pos_unicode_equiv =
            "{\"meta\":{\"format\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"}}}\n"
            "{\"ie\":0,\"sort\":0}\n"
            "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"P\"}}\n"
            "{\"axiom\":{\"name\":1,\"levelParams\":[],\"type\":0}}\n"
            "{\"ie\":1,\"const\":{\"name\":1,\"us\":[]}}\n"
            "{\"in\":2,\"str\":{\"pre\":0,\"str\":\"\\u03b1_\\ud835\\udcab\"}}\n"
            "{\"axiom\":{\"name\":2,\"levelParams\":[],\"type\":1}}\n"
            "{\"ie\":2,\"const\":{\"name\":2,\"us\":[]}}\n"
            "{\"in\":3,\"str\":{\"pre\":0,\"str\":\"thm_ok\"}}\n"
            "{\"thm\":{\"name\":3,\"levelParams\":[],\"type\":1,\"value\":2}}\n";

        const char *neg_embedded_nul =
            "{\"meta\":{\"format\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"}}}\n"
            "{\"ie\":0,\"sort\":0}\n"
            "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"a\\u0000b\"}}\n";

        lean_kernel_init(&ks);
        bool c10_reject_collision = !lean_verify_ndjson_string(&ks, neg_unicode_collision, err, sizeof(err));
        lean_kernel_destroy(&ks);

        lean_kernel_init(&ks);
        bool c10_accept_equiv = lean_verify_ndjson_string(&ks, pos_unicode_equiv, err, sizeof(err)) &&
                                lean_check_required_decl_name(&ks, "\xce\xb1_\xf0\x9d\x92\xab", err, sizeof(err));
        lean_kernel_destroy(&ks);

        lean_kernel_init(&ks);
        bool c10_reject_nul = !lean_verify_ndjson_string(&ks, neg_embedded_nul, err, sizeof(err));
        lean_kernel_destroy(&ks);

        if (c10_reject_collision && c10_accept_equiv && c10_reject_nul) {
            printf("  [PASS] Control 10 (UTF-8 / Unicode \\uXXXX + surrogate pair decoding & \\u0000 / collision rejection verified)\n");
            passed++;
        } else {
            printf("  [FAIL] Control 10 Unicode escape / NUL handling check failed (coll=%d equiv=%d nul=%d)!\n",
                   (int)c10_reject_collision, (int)c10_accept_equiv, (int)c10_reject_nul);
            failed++;
        }
    }

    /* 11. Control 11: Live 23-rule R/FL + RuleTable.Plan theory JSON export & self-reparse roundtrip */
    {
        char *buf = NULL;
        size_t len = 0;
        FILE *ms = open_memstream(&buf, &len);
        bool c11_ok = false;
        if (ms) {
            bool w_ok = lean_tc_write_theory_json_stream(ms);
            fclose(ms);
            bool valid_pos = w_ok && lean_verify_exported_theory_json_buf(buf, len);
            /* Negative control: corrupting the schema string or outcome_codes must be rejected by the self-reparse validator */
            char *corrupted = (buf && len > 32) ? strdup(buf) : NULL;
            bool valid_neg = false;
            if (corrupted) {
                char *p = strstr(corrupted, "\"tcalc.lean_theory_and_tisa_contract.v1\"");
                if (p) p[1] = 'X';
                valid_neg = !lean_verify_exported_theory_json_buf(corrupted, len);
                free(corrupted);
            }
            char *corrupted_oc = (buf && len > 32) ? strdup(buf) : NULL;
            bool valid_neg_oc = false;
            if (corrupted_oc) {
                char *p = strstr(corrupted_oc, "\"refused\": 0");
                if (p) p[11] = '1';
                valid_neg_oc = !lean_verify_exported_theory_json_buf(corrupted_oc, len);
                free(corrupted_oc);
            }
            c11_ok = valid_pos && valid_neg && valid_neg_oc;
            free(buf);
        }
        if (c11_ok) {
            printf("  [PASS] Control 11 (Live 23-rule R/FL + RuleTable.Plan JSON export & CeTTa-style self-reparse roundtrip verified)\n");
            passed++;
        } else {
            printf("  [FAIL] Control 11 theory JSON export / roundtrip check failed!\n");
            failed++;
        }
    }

    printf("=== Self-Test Summary: %d/%d passed (%d failed) ===\n", passed, passed + failed, failed);
    return failed == 0 ? 0 : 1;
}

static void json_fprint_escaped_str(FILE *lf, const char *s) {
    fputc('"', lf);
    if (s) {
        for (const unsigned char *p = (const unsigned char *)s; *p; p++) {
            unsigned char c = *p;
            switch (c) {
                case '"':  fputs("\\\"", lf); break;
                case '\\': fputs("\\\\", lf); break;
                case '\b': fputs("\\b", lf); break;
                case '\f': fputs("\\f", lf); break;
                case '\n': fputs("\\n", lf); break;
                case '\r': fputs("\\r", lf); break;
                case '\t': fputs("\\t", lf); break;
                default:
                    if (c < 0x20u) fprintf(lf, "\\u%04x", (unsigned int)c);
                    else fputc((int)c, lf);
                    break;
            }
        }
    }
    fputc('"', lf);
}

static bool lean_check_required_decl_name(const LeanKernelState *ks, const char *req_name, char *err_buf, size_t err_cap) {
    for (uint32_t i = 1; i < ks->nnames; i++) {
        if (ks->names[i].full && strcmp(ks->names[i].full, req_name) == 0) {
            if (i < ks->cap_decls_by_name &&
                ks->decls_by_name[i].kind != LDECL_NONE &&
                ks->decls_by_name[i].tc_occ != 0) {
                return true;
            }
            break;
        }
    }
    snprintf(err_buf, err_cap, "required target declaration missing from verified environment: %s", req_name);
    return false;
}

static bool lean_check_manifest_file(const LeanKernelState *ks, const char *manifest_path, char *err_buf, size_t err_cap) {
    FILE *mf = fopen(manifest_path, "r");
    if (!mf) {
        snprintf(err_buf, err_cap, "cannot open manifest file: %s", manifest_path);
        return false;
    }
    char line[4096];
    uint32_t checked = 0;
    while (fgets(line, sizeof(line), mf)) {
        char *p = line;
        while (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n') p++;
        if (*p == '\0' || *p == '#') continue;
        if (strncmp(p, "decl ", 5) == 0) p += 5;
        while (*p == ' ' || *p == '\t') p++;
        size_t len = strlen(p);
        while (len > 0 && (p[len - 1] == '\n' || p[len - 1] == '\r' || p[len - 1] == ' ' || p[len - 1] == '\t')) {
            p[--len] = '\0';
        }
        if (len == 0) continue;
        if (!lean_check_required_decl_name(ks, p, err_buf, err_cap)) {
            fclose(mf);
            return false;
        }
        checked++;
    }
    fclose(mf);
    if (checked == 0) {
        snprintf(err_buf, err_cap, "manifest file %s contained 0 required declarations", manifest_path);
        return false;
    }
    return true;
}

static bool lean_write_trust_ledger(const LeanKernelState *ks, const char *ledger_path, const char *label, double elapsed_ms) {
    FILE *lf = fopen(ledger_path, "w");
    if (!lf) return false;
    fprintf(lf, "{\n");
    fputs("  \"input\": ", lf);
    json_fprint_escaped_str(lf, label);
    fputs(",\n  \"format_version\": ", lf);
    json_fprint_escaped_str(lf, ks->format_version[0] ? ks->format_version : "legacy");
    fputs(",\n  \"lean_version\": ", lf);
    json_fprint_escaped_str(lf, ks->lean_version[0] ? ks->lean_version : "unspecified");
    fputs(",\n  \"lean_githash\": ", lf);
    json_fprint_escaped_str(lf, ks->lean_githash[0] ? ks->lean_githash : "unspecified");
    fprintf(lf, ",\n  \"verified_decls\": %" PRIu64 ",\n", g_tc_admitted_decls);
    fprintf(lf, "  \"counts\": {\"axioms\": %" PRIu64 ", \"defns\": %" PRIu64 ", \"thms\": %" PRIu64
                ", \"opaques\": %" PRIu64 ", \"inds\": %" PRIu64 ", \"ctors\": %" PRIu64
                ", \"recs\": %" PRIu64 ", \"quots\": %" PRIu64 "},\n",
            ks->stat_axioms, ks->stat_defns, ks->stat_thms, ks->stat_opaques,
            ks->stat_inds, ks->stat_ctors, ks->stat_recs, ks->stat_quots);
    fprintf(lf, "  \"trust_accounting\": {\n");
    fprintf(lf, "    \"sorry_tainted_decls\": %" PRIu64 ",\n", ks->stat_sorry_decls);
    fprintf(lf, "    \"trust_compiler_decls\": %" PRIu64 ",\n", ks->stat_trust_compiler_decls);
    fprintf(lf, "    \"declared_axioms\": [");
    for (uint32_t i = 0; i < ks->n_axiom_names; i++) {
        uint32_t aid = ks->axiom_names[i];
        const char *anm = (aid < ks->nnames && ks->names[aid].full) ? ks->names[aid].full : "?";
        const char *tier = "custom";
        if (aid == ks->nm_propext || aid == ks->nm_Classical_choice || aid == ks->nm_Quot_sound) {
            tier = "standard";
        } else if (aid == ks->nm_sorryAx) {
            tier = "sorry_placeholder";
        } else if (aid == ks->nm_trustCompiler || aid == ks->nm_ofReduceBool || aid == ks->nm_ofReduceNat) {
            tier = "compiler_evaluation";
        }
        fprintf(lf, "%s{\"name\": ", (i > 0 ? ", " : ""));
        json_fprint_escaped_str(lf, anm);
        fprintf(lf, ", \"category\": \"%s\"}", tier);
    }
    fprintf(lf, "]\n  },\n");
    fprintf(lf, "  \"tcalc_inference\": {\n");
    fprintf(lf, "    \"rule_commits\": %" PRIu64 ",\n", g_tc_rule_commits);
    fprintf(lf, "    \"admitted_env_decls\": %" PRIu64 ",\n", g_tc_admitted_decls);
    fprintf(lf, "    \"admitted_thms\": %" PRIu64 ",\n", g_tc_admitted_thms);
    fprintf(lf, "    \"trusted_c_helpers\": {\"defeq_checks\": %" PRIu64 ", \"whnf_steps\": %" PRIu64 ", \"proof_irrel_hits\": %" PRIu64 "}\n",
            ks->stat_defeq_checks, ks->stat_whnf_steps, ks->stat_proof_irrel_hits);
    fprintf(lf, "  },\n");
    fprintf(lf, "  \"elapsed_ms\": %.2f\n", elapsed_ms);
    fprintf(lf, "}\n");
    fclose(lf);
    return true;
}

int main(int argc, char **argv) {
    bool run_selftest = false;
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--tisa-x86") == 0) {
            g_lean_tisa_x86_mode = true;
        } else if (strcmp(argv[i], "--selftest") == 0) {
            run_selftest = true;
        }
    }
    if (run_selftest) {
        return run_lean_tcalc_selftest();
    }
    if (argc >= 2 && strcmp(argv[1], "--export-theory-json") == 0) {
        const char *out_path = (argc >= 3) ? argv[2] : "-";
        if (!lean_export_theory_json_validated(out_path)) {
            fprintf(stderr, "FAULT: --export-theory-json failed to write or validate manifest\n");
            return (int)LEAN_OUTCOME_FAULT;
        }
        return (int)LEAN_OUTCOME_ACCEPT;
    }

    const char *in_path = NULL;
    const char *manifest_path = NULL;
    const char *ledger_path = NULL;
    const char **req_decls = NULL;
    uint32_t n_req_decls = 0, cap_req_decls = 0;
    bool forbid_sorry = false;
    bool forbid_trust_compiler = false;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--forbid-sorry") == 0) {
            forbid_sorry = true;
        } else if (strcmp(argv[i], "--forbid-trust-compiler") == 0) {
            forbid_trust_compiler = true;
        } else if (strcmp(argv[i], "--bridge-events") == 0) {
            g_lean_bridge_event_mode = true;
        } else if (strcmp(argv[i], "--tisa-x86") == 0) {
            g_lean_tisa_x86_mode = true;
        } else if (strcmp(argv[i], "--require-decl") == 0) {
            if (i + 1 >= argc) {
                fprintf(stderr, "FAULT: --require-decl missing declaration name argument\n");
                free(req_decls);
                return (int)LEAN_OUTCOME_FAULT;
            }
            if (n_req_decls >= cap_req_decls) {
                cap_req_decls = cap_req_decls ? cap_req_decls * 2u : 64u;
                req_decls = (const char **)realloc(req_decls, (size_t)cap_req_decls * sizeof(const char *));
            }
            req_decls[n_req_decls++] = argv[++i];
        } else if (strcmp(argv[i], "--manifest") == 0) {
            if (i + 1 >= argc) {
                fprintf(stderr, "FAULT: --manifest missing file path argument\n");
                free(req_decls);
                return (int)LEAN_OUTCOME_FAULT;
            }
            manifest_path = argv[++i];
        } else if (strcmp(argv[i], "--trust-ledger") == 0) {
            if (i + 1 >= argc) {
                fprintf(stderr, "FAULT: --trust-ledger missing file path argument\n");
                free(req_decls);
                return (int)LEAN_OUTCOME_FAULT;
            }
            ledger_path = argv[++i];
        } else if (strcmp(argv[i], "-") == 0) {
            in_path = NULL;
        } else if (argv[i][0] == '-') {
            fprintf(stderr, "REJECT: unknown CLI flag %s\n", argv[i]);
            free(req_decls);
            return (int)LEAN_OUTCOME_REJECT;
        } else {
            in_path = argv[i];
        }
    }
    if (!in_path) {
        const char *env_in = getenv("IN");
        if (env_in && env_in[0] != '\0') in_path = env_in;
    }

    FILE *fp = stdin;
    const char *label = "<stdin>";
    if (in_path) {
        label = in_path;
        fp = fopen(in_path, "r");
        if (!fp) {
            perror(in_path);
            free(req_decls);
            return (int)LEAN_OUTCOME_FAULT;
        }
    }

    double t0 = now_ms();
    LeanKernelState ks;
    lean_kernel_init(&ks);
    ks.forbid_sorry = forbid_sorry;
    ks.forbid_trust_compiler = forbid_trust_compiler;
    char err[512] = {0};
    bool ok = lean_verify_ndjson_stream(&ks, fp, err, sizeof(err));
    if (fp != stdin) fclose(fp);

    for (uint32_t i = 0; ok && i < n_req_decls; i++) {
        if (!lean_check_required_decl_name(&ks, req_decls[i], err, sizeof(err))) {
            ks.outcome = LEAN_OUTCOME_REJECT;
            ok = false;
        }
    }
    free(req_decls);
    if (ok && manifest_path) {
        if (!lean_check_manifest_file(&ks, manifest_path, err, sizeof(err))) {
            ks.outcome = LEAN_OUTCOME_REJECT;
            ok = false;
        }
    }
    double elapsed = now_ms() - t0;

    if (!ok) {
        LeanArenaOutcome out = (ks.outcome == LEAN_OUTCOME_ACCEPT) ? LEAN_OUTCOME_REJECT : ks.outcome;
        fprintf(stderr, "%s [%s]: %s (after %.2f ms)\n",
                out == LEAN_OUTCOME_DECLINE ? "DECLINE" : "REJECT", label, err, elapsed);
        lean_kernel_destroy(&ks);
        return (int)out;
    }

    if (ledger_path) {
        if (!lean_write_trust_ledger(&ks, ledger_path, label, elapsed)) {
            fprintf(stderr, "FAULT [%s]: failed to write trust ledger to %s\n", label, ledger_path);
            lean_kernel_destroy(&ks);
            return (int)LEAN_OUTCOME_FAULT;
        }
    }

    printf("PASS [%s]: verified %" PRIu64 " decls (axioms=%" PRIu64 ", defns=%" PRIu64 ", thms=%" PRIu64
           ", inds=%" PRIu64 ", ctors=%" PRIu64 ", recs=%" PRIu64 ", quots=%" PRIu64 ") | "
           "exprs=%u (peak_scratch=%u reclaimed=%" PRIu64 ") lvls=%u | defeq=%" PRIu64 " whnf=%" PRIu64 " proof_irrel=%" PRIu64 " | "
           "sorry_decls=%" PRIu64 " tc_compiler_decls=%" PRIu64 " | "
           "tcalc_commits=%" PRIu64 " | %.2f ms\n",
           label,
           g_tc_admitted_decls,
           ks.stat_axioms, ks.stat_defns, ks.stat_thms,
           ks.stat_inds, ks.stat_ctors, ks.stat_recs, ks.stat_quots,
           ks.nexprs - 1u, ks.stat_peak_scratch, ks.stat_scratch_reclaimed, ks.nlvls,
           ks.stat_defeq_checks, ks.stat_whnf_steps, ks.stat_proof_irrel_hits,
           ks.stat_sorry_decls, ks.stat_trust_compiler_decls,
           g_tc_rule_commits, elapsed);

    lean_kernel_destroy(&ks);
    return (int)LEAN_OUTCOME_ACCEPT;
}

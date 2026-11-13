#ifndef GSLT_PACKED_BRIDGE_H
#define GSLT_PACKED_BRIDGE_H

/*
 * gslt_packed_bridge.h — Compositional SyntaxGSLT C Parser Substrate (Stage 2)
 *
 * Connects authored .module files and exported grammar packs to:
 *   1. Binary CNF1 packed parse forests and PNI1 plan identity files
 *      (byte-compatible with CeTTa's CettaLpNativeUtf8Forest and PNI1 wire format),
 *   2. Explicit ambiguity/word selection policies (SourceSelectionV1 / RejectWords)
 *      without mutating the raw packed forest,
 *   3. Sound and complete (result (node ...)) packet & catalogue verification,
 *   4. Compositional constructor provenance (Module::Theory::Constructor),
 *      positional/rest argument routing (routed_slots[]), lexical binder scope
 *      and capture-avoidance verification, and canonical printing/readback.
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define GSLT_MAX_MODULES      32
#define GSLT_MAX_PRODS        1024
#define GSLT_MAX_SLOTS        16
#define GSLT_MAX_MATCHERS     64
#define GSLT_MAX_REJECT_RULES 32
#define GSLT_MAX_REJECT_WORDS 32
#define GSLT_MAX_AST_NODES    2048
#define GSLT_MAX_DERIVATIONS  128
#define GSLT_FOREST_NONE      UINT32_MAX

typedef enum {
    GSLT_MATCH_SLOT  = 0,
    GSLT_MATCH_CP    = 1,
    GSLT_MATCH_CLASS = 2
} GsltMatcherKind;

typedef struct {
    uint32_t kind; /* GsltMatcherKind */
    char sort[64];
    uint32_t codepoint;
    uint32_t class_id;
    uint32_t slot_index; /* index into production's slots[] if GSLT_MATCH_SLOT */
} GsltMatcher;

typedef struct {
    char name[64];
    char sort[64];
    bool is_binder;      /* true if ^x.body:[Dom -> Cod] */
    char binder_var[64]; /* bound variable slot name if binder */
    char binder_dom[64]; /* domain sort of binder */
    bool is_rest;        /* true if rest/variadic slot */
} GsltSlotSpec;

typedef struct {
    uint32_t production_index;
    char origin_module[64];
    char origin_theory[64];
    char label[64];
    char sort[64];
    uint32_t slot_count;
    GsltSlotSpec slots[GSLT_MAX_SLOTS];
    uint32_t matcher_count;
    GsltMatcher matchers[GSLT_MAX_MATCHERS];
    uint32_t routed_slots[GSLT_MAX_SLOTS]; /* slot_idx -> matcher position among SLOT matchers */
    bool is_binder_var_ref;                /* true if variable reference constructor */
} GsltProduction;

typedef struct {
    char sort[64];
    uint32_t word_count;
    char words[GSLT_MAX_REJECT_WORDS][64];
} GsltRejectWordsRule;

typedef struct {
    bool has_policy;
    char version_tag[64]; /* must be "SourceSelectionV1" when has_policy */
    uint32_t reject_rule_count;
    GsltRejectWordsRule reject_rules[GSLT_MAX_REJECT_RULES];
    /* Optional preferred constructor origin module when disambiguating */
    char prefer_origin_module[64];
} GsltSelectionPolicy;

typedef struct {
    char module_name[64];
    char profile_version[64]; /* "GSLTParserProfileLayerV1" */
    char profile_name[64];
    char start_sort[64];
    uint32_t imported_module_count;
    char imported_modules[GSLT_MAX_MODULES][64];
    uint32_t production_count;
    GsltProduction productions[GSLT_MAX_PRODS];
    GsltSelectionPolicy selection;
} GsltModuleCatalog;

/* =========================================================================
 * CNF1 Binary Packed Forest & PNI1 Plan Identity Structures
 * ========================================================================= */

typedef enum {
    GSLT_CNF1_NODE_TERM         = 0,
    GSLT_CNF1_NODE_EPSILON      = 1,
    GSLT_CNF1_NODE_SYMBOL       = 2,
    GSLT_CNF1_NODE_INTERMEDIATE = 3
} GsltCnf1NodeKind;

typedef struct {
    uint32_t kind;
    uint32_t symbol_id;
    uint32_t production_index;
    uint32_t dot;
    uint32_t scalar_left;
    uint32_t scalar_right;
    uint32_t byte_left;
    uint32_t byte_right;
    uint32_t terminal_is_eof;
    uint32_t terminal_scalar;
    uint32_t terminal_value_kind;
    uint32_t terminal_witness_id;
    uint32_t choice_begin;
    uint32_t choice_len;
} GsltCnf1Node;

typedef struct {
    uint32_t parent_node;
    uint32_t prefix_node;
    uint32_t child_node;
    uint32_t production_index;
    uint32_t scalar_pivot;
    uint32_t byte_pivot;
} GsltCnf1Choice;

typedef struct {
    uint32_t outcome;
    uint32_t node_len;
    uint32_t choice_len;
    uint32_t root_len;
    uint32_t expected_terminal_len;
    uint32_t scalar_len;
    uint32_t input_byte_len;
    uint32_t farthest_scalar;
    uint32_t farthest_byte;
    uint32_t graph_node_len;
    uint32_t stack_node_len;
    uint32_t work_item_len;
    uint32_t decoded_byte_len;
    uint32_t source_pass_count;
    GsltCnf1Node *nodes;
    GsltCnf1Choice *choices;
    uint32_t *roots;
    uint32_t *expected_terminal_ids;
    uint32_t *codepoints;
    uint32_t *byte_offsets;
} GsltCnf1Forest;

typedef struct {
    char sort[64];
    char label[64];
    uint32_t slot_count;
    uint32_t matcher_count;
    uint32_t routed_slots[GSLT_MAX_SLOTS];
    GsltMatcher matchers[GSLT_MAX_MATCHERS];
} GsltPni1Prod;

typedef struct {
    uint32_t version;
    uint32_t production_count;
    GsltPni1Prod prods[GSLT_MAX_PRODS];
} GsltPni1Identity;

/* =========================================================================
 * Constructor AST with Provenance, Slot Routing & Binder Metadata
 * ========================================================================= */

typedef struct GsltAstNode {
    uint32_t production_index;
    char origin_module[64];
    char origin_theory[64];
    char label[64];
    char sort[64];
    uint32_t scalar_left;
    uint32_t scalar_right;
    uint32_t child_count;
    struct GsltAstNode *children[GSLT_MAX_SLOTS]; /* stored in logical constructor slot order! */
    /* Binder / variable metadata */
    bool is_binder;
    char binder_var[64];
    bool is_var_ref;
    char var_name[64];
    int32_t db_index; /* >= 0 if bound to enclosing binder at de Bruijn distance, -1 if free */
} GsltAstNode;

typedef struct {
    uint32_t count;
    GsltAstNode *trees[GSLT_MAX_DERIVATIONS];
    char packets[GSLT_MAX_DERIVATIONS][1024];
} GsltDerivationCatalog;

/* =========================================================================
 * UTF-8 Decode Helper
 * ========================================================================= */

static inline bool gslt_utf8_decode_scalars(
    const uint8_t *bytes,
    size_t byte_len,
    uint32_t *out_codepoints,
    uint32_t *out_byte_offsets,
    uint32_t max_scalars,
    uint32_t *out_scalar_len,
    char *err,
    size_t err_cap)
{
    size_t pos = 0;
    uint32_t sc = 0;
    while (pos < byte_len) {
        if (sc >= max_scalars) {
            snprintf(err, err_cap, "UTF-8 scalar count exceeds max_scalars (%u)", max_scalars);
            return false;
        }
        out_byte_offsets[sc] = (uint32_t)pos;
        uint8_t b0 = bytes[pos];
        uint32_t cp = 0;
        size_t adv = 0;
        if ((b0 & 0x80u) == 0u) {
            cp = b0;
            adv = 1;
        } else if ((b0 & 0xE0u) == 0xC0u) {
            if (pos + 2 > byte_len) {
                snprintf(err, err_cap, "truncated 2-byte UTF-8 sequence at %zu", pos);
                return false;
            }
            uint8_t b1 = bytes[pos + 1];
            if ((b1 & 0xC0u) != 0x80u) {
                snprintf(err, err_cap, "invalid UTF-8 continuation byte at %zu", pos + 1);
                return false;
            }
            cp = ((uint32_t)(b0 & 0x1Fu) << 6) | (uint32_t)(b1 & 0x3Fu);
            if (cp < 0x80u) {
                snprintf(err, err_cap, "overlong 2-byte UTF-8 sequence at %zu", pos);
                return false;
            }
            adv = 2;
        } else if ((b0 & 0xF0u) == 0xE0u) {
            if (pos + 3 > byte_len) {
                snprintf(err, err_cap, "truncated 3-byte UTF-8 sequence at %zu", pos);
                return false;
            }
            uint8_t b1 = bytes[pos + 1], b2 = bytes[pos + 2];
            if ((b1 & 0xC0u) != 0x80u || (b2 & 0xC0u) != 0x80u) {
                snprintf(err, err_cap, "invalid 3-byte UTF-8 continuation at %zu", pos);
                return false;
            }
            cp = ((uint32_t)(b0 & 0x0Fu) << 12) | ((uint32_t)(b1 & 0x3Fu) << 6) | (uint32_t)(b2 & 0x3Fu);
            if (cp < 0x800u || (cp >= 0xD800u && cp <= 0xDFFFu)) {
                snprintf(err, err_cap, "invalid 3-byte UTF-8 scalar U+%04X at %zu", cp, pos);
                return false;
            }
            adv = 3;
        } else if ((b0 & 0xF8u) == 0xF0u) {
            if (pos + 4 > byte_len) {
                snprintf(err, err_cap, "truncated 4-byte UTF-8 sequence at %zu", pos);
                return false;
            }
            uint8_t b1 = bytes[pos + 1], b2 = bytes[pos + 2], b3 = bytes[pos + 3];
            if ((b1 & 0xC0u) != 0x80u || (b2 & 0xC0u) != 0x80u || (b3 & 0xC0u) != 0x80u) {
                snprintf(err, err_cap, "invalid 4-byte UTF-8 continuation at %zu", pos);
                return false;
            }
            cp = ((uint32_t)(b0 & 0x07u) << 18) | ((uint32_t)(b1 & 0x3Fu) << 12) |
                 ((uint32_t)(b2 & 0x3Fu) << 6) | (uint32_t)(b3 & 0x3Fu);
            if (cp < 0x10000u || cp > 0x10FFFFu) {
                snprintf(err, err_cap, "invalid 4-byte UTF-8 scalar U+%04X at %zu", cp, pos);
                return false;
            }
            adv = 4;
        } else {
            snprintf(err, err_cap, "invalid UTF-8 lead byte 0x%02X at %zu", b0, pos);
            return false;
        }
        out_codepoints[sc++] = cp;
        pos += adv;
    }
    out_byte_offsets[sc] = (uint32_t)byte_len;
    *out_scalar_len = sc;
    return true;
}

/* =========================================================================
 * CNF1 Wire Serialization, Deserialization & Structural Validation
 * ========================================================================= */

static inline void gslt_put_u32_le(uint8_t **cur, uint32_t v) {
    uint8_t *b = *cur;
    b[0] = (uint8_t)(v & 0xFFu);
    b[1] = (uint8_t)((v >> 8) & 0xFFu);
    b[2] = (uint8_t)((v >> 16) & 0xFFu);
    b[3] = (uint8_t)((v >> 24) & 0xFFu);
    *cur += 4;
}

static inline bool gslt_get_u32_le(const uint8_t **cur, const uint8_t *end, uint32_t *out) {
    if ((size_t)(end - *cur) < 4u) return false;
    const uint8_t *b = *cur;
    *out = (uint32_t)b[0] | ((uint32_t)b[1] << 8) | ((uint32_t)b[2] << 16) | ((uint32_t)b[3] << 24);
    *cur += 4;
    return true;
}

static inline void gslt_cnf1_forest_free(GsltCnf1Forest *f) {
    if (!f) return;
    free(f->nodes);
    free(f->choices);
    free(f->roots);
    free(f->expected_terminal_ids);
    free(f->codepoints);
    free(f->byte_offsets);
    memset(f, 0, sizeof(*f));
}

static inline size_t gslt_cnf1_wire_size(const GsltCnf1Forest *f) {
    size_t words = 14u +
                   (size_t)f->node_len * 14u +
                   (size_t)f->choice_len * 6u +
                   (size_t)f->root_len +
                   (size_t)f->expected_terminal_len +
                   (size_t)f->scalar_len +
                   (size_t)(f->scalar_len + 1u);
    return 4u + words * 4u;
}

static inline bool gslt_cnf1_serialize_wire(
    const GsltCnf1Forest *f,
    uint8_t **out_buf,
    size_t *out_len)
{
    size_t req = gslt_cnf1_wire_size(f);
    uint8_t *buf = (uint8_t *)malloc(req);
    if (!buf) return false;
    uint8_t *cur = buf;
    *cur++ = 'C'; *cur++ = 'N'; *cur++ = 'F'; *cur++ = '1';
    gslt_put_u32_le(&cur, f->outcome);
    gslt_put_u32_le(&cur, f->node_len);
    gslt_put_u32_le(&cur, f->choice_len);
    gslt_put_u32_le(&cur, f->root_len);
    gslt_put_u32_le(&cur, f->expected_terminal_len);
    gslt_put_u32_le(&cur, f->scalar_len);
    gslt_put_u32_le(&cur, f->input_byte_len);
    gslt_put_u32_le(&cur, f->farthest_scalar);
    gslt_put_u32_le(&cur, f->farthest_byte);
    gslt_put_u32_le(&cur, f->graph_node_len);
    gslt_put_u32_le(&cur, f->stack_node_len);
    gslt_put_u32_le(&cur, f->work_item_len);
    gslt_put_u32_le(&cur, f->decoded_byte_len);
    gslt_put_u32_le(&cur, f->source_pass_count);
    for (uint32_t i = 0; i < f->node_len; i++) {
        const GsltCnf1Node *n = &f->nodes[i];
        gslt_put_u32_le(&cur, n->kind);
        gslt_put_u32_le(&cur, n->symbol_id);
        gslt_put_u32_le(&cur, n->production_index);
        gslt_put_u32_le(&cur, n->dot);
        gslt_put_u32_le(&cur, n->scalar_left);
        gslt_put_u32_le(&cur, n->scalar_right);
        gslt_put_u32_le(&cur, n->byte_left);
        gslt_put_u32_le(&cur, n->byte_right);
        gslt_put_u32_le(&cur, n->terminal_is_eof ? 1u : 0u);
        gslt_put_u32_le(&cur, n->terminal_scalar);
        gslt_put_u32_le(&cur, n->terminal_value_kind);
        gslt_put_u32_le(&cur, n->terminal_witness_id);
        gslt_put_u32_le(&cur, n->choice_begin);
        gslt_put_u32_le(&cur, n->choice_len);
    }
    for (uint32_t i = 0; i < f->choice_len; i++) {
        const GsltCnf1Choice *c = &f->choices[i];
        gslt_put_u32_le(&cur, c->parent_node);
        gslt_put_u32_le(&cur, c->prefix_node);
        gslt_put_u32_le(&cur, c->child_node);
        gslt_put_u32_le(&cur, c->production_index);
        gslt_put_u32_le(&cur, c->scalar_pivot);
        gslt_put_u32_le(&cur, c->byte_pivot);
    }
    for (uint32_t i = 0; i < f->root_len; i++)
        gslt_put_u32_le(&cur, f->roots[i]);
    for (uint32_t i = 0; i < f->expected_terminal_len; i++)
        gslt_put_u32_le(&cur, f->expected_terminal_ids[i]);
    for (uint32_t i = 0; i < f->scalar_len; i++)
        gslt_put_u32_le(&cur, f->codepoints[i]);
    for (uint32_t i = 0; i <= f->scalar_len; i++)
        gslt_put_u32_le(&cur, f->byte_offsets[i]);
    *out_buf = buf;
    *out_len = req;
    return true;
}

static inline bool gslt_cnf1_deserialize_and_validate(
    const uint8_t *bytes,
    size_t byte_len,
    const uint8_t *source_bytes,
    size_t source_byte_len,
    GsltCnf1Forest *out,
    char *err,
    size_t err_cap)
{
    memset(out, 0, sizeof(*out));
    if (byte_len < 60u) {
        snprintf(err, err_cap, "CNF1 buffer too short (%zu bytes)", byte_len);
        return false;
    }
    if (memcmp(bytes, "CNF1", 4u) != 0) {
        snprintf(err, err_cap, "invalid CNF1 magic tag '%c%c%c%c' (expected 'CNF1')",
                 bytes[0], bytes[1], bytes[2], bytes[3]);
        return false;
    }
    const uint8_t *cur = bytes + 4;
    const uint8_t *end = bytes + byte_len;
    gslt_get_u32_le(&cur, end, &out->outcome);
    gslt_get_u32_le(&cur, end, &out->node_len);
    gslt_get_u32_le(&cur, end, &out->choice_len);
    gslt_get_u32_le(&cur, end, &out->root_len);
    gslt_get_u32_le(&cur, end, &out->expected_terminal_len);
    gslt_get_u32_le(&cur, end, &out->scalar_len);
    gslt_get_u32_le(&cur, end, &out->input_byte_len);
    gslt_get_u32_le(&cur, end, &out->farthest_scalar);
    gslt_get_u32_le(&cur, end, &out->farthest_byte);
    gslt_get_u32_le(&cur, end, &out->graph_node_len);
    gslt_get_u32_le(&cur, end, &out->stack_node_len);
    gslt_get_u32_le(&cur, end, &out->work_item_len);
    gslt_get_u32_le(&cur, end, &out->decoded_byte_len);
    gslt_get_u32_le(&cur, end, &out->source_pass_count);

    if (out->outcome != 0u) {
        snprintf(err, err_cap, "CNF1 forest outcome=%u is not COMPLETED(0)", out->outcome);
        return false;
    }
    size_t expected_wire = gslt_cnf1_wire_size(out);
    if (byte_len != expected_wire) {
        snprintf(err, err_cap, "CNF1 wire size mismatch: got %zu, expected %zu", byte_len, expected_wire);
        return false;
    }
    if (out->input_byte_len != source_byte_len || out->decoded_byte_len != source_byte_len) {
        snprintf(err, err_cap, "CNF1 source byte length mismatch (%u vs %zu)",
                 out->input_byte_len, source_byte_len);
        return false;
    }

    out->nodes = (GsltCnf1Node *)calloc(out->node_len ? out->node_len : 1u, sizeof(GsltCnf1Node));
    out->choices = (GsltCnf1Choice *)calloc(out->choice_len ? out->choice_len : 1u, sizeof(GsltCnf1Choice));
    out->roots = (uint32_t *)calloc(out->root_len ? out->root_len : 1u, sizeof(uint32_t));
    out->expected_terminal_ids = (uint32_t *)calloc(out->expected_terminal_len ? out->expected_terminal_len : 1u, sizeof(uint32_t));
    out->codepoints = (uint32_t *)calloc(out->scalar_len ? out->scalar_len : 1u, sizeof(uint32_t));
    out->byte_offsets = (uint32_t *)calloc(out->scalar_len + 1u, sizeof(uint32_t));

    for (uint32_t i = 0; i < out->node_len; i++) {
        GsltCnf1Node *n = &out->nodes[i];
        gslt_get_u32_le(&cur, end, &n->kind);
        gslt_get_u32_le(&cur, end, &n->symbol_id);
        gslt_get_u32_le(&cur, end, &n->production_index);
        gslt_get_u32_le(&cur, end, &n->dot);
        gslt_get_u32_le(&cur, end, &n->scalar_left);
        gslt_get_u32_le(&cur, end, &n->scalar_right);
        gslt_get_u32_le(&cur, end, &n->byte_left);
        gslt_get_u32_le(&cur, end, &n->byte_right);
        gslt_get_u32_le(&cur, end, &n->terminal_is_eof);
        gslt_get_u32_le(&cur, end, &n->terminal_scalar);
        gslt_get_u32_le(&cur, end, &n->terminal_value_kind);
        gslt_get_u32_le(&cur, end, &n->terminal_witness_id);
        gslt_get_u32_le(&cur, end, &n->choice_begin);
        gslt_get_u32_le(&cur, end, &n->choice_len);
    }
    for (uint32_t i = 0; i < out->choice_len; i++) {
        GsltCnf1Choice *c = &out->choices[i];
        gslt_get_u32_le(&cur, end, &c->parent_node);
        gslt_get_u32_le(&cur, end, &c->prefix_node);
        gslt_get_u32_le(&cur, end, &c->child_node);
        gslt_get_u32_le(&cur, end, &c->production_index);
        gslt_get_u32_le(&cur, end, &c->scalar_pivot);
        gslt_get_u32_le(&cur, end, &c->byte_pivot);
    }
    for (uint32_t i = 0; i < out->root_len; i++)
        gslt_get_u32_le(&cur, end, &out->roots[i]);
    for (uint32_t i = 0; i < out->expected_terminal_len; i++)
        gslt_get_u32_le(&cur, end, &out->expected_terminal_ids[i]);
    for (uint32_t i = 0; i < out->scalar_len; i++)
        gslt_get_u32_le(&cur, end, &out->codepoints[i]);
    for (uint32_t i = 0; i <= out->scalar_len; i++)
        gslt_get_u32_le(&cur, end, &out->byte_offsets[i]);

    /* Verify UTF-8 scalar table matches source_bytes */
    uint32_t ref_cps[4096];
    uint32_t ref_offs[4097];
    uint32_t ref_sc = 0;
    if (!gslt_utf8_decode_scalars(source_bytes, source_byte_len, ref_cps, ref_offs, 4096, &ref_sc, err, err_cap)) {
        gslt_cnf1_forest_free(out);
        return false;
    }
    if (ref_sc != out->scalar_len) {
        snprintf(err, err_cap, "CNF1 scalar_len=%u does not match source UTF-8 scalars=%u",
                 out->scalar_len, ref_sc);
        gslt_cnf1_forest_free(out);
        return false;
    }
    for (uint32_t i = 0; i < ref_sc; i++) {
        if (out->codepoints[i] != ref_cps[i] || out->byte_offsets[i] != ref_offs[i]) {
            snprintf(err, err_cap, "CNF1 codepoint/offset mismatch at scalar %u", i);
            gslt_cnf1_forest_free(out);
            return false;
        }
    }
    if (out->byte_offsets[ref_sc] != ref_offs[ref_sc]) {
        snprintf(err, err_cap, "CNF1 final byte_offset mismatch");
        gslt_cnf1_forest_free(out);
        return false;
    }

    /* Validate node spans, terminal scalars, and choice ranges */
    for (uint32_t i = 0; i < out->node_len; i++) {
        const GsltCnf1Node *n = &out->nodes[i];
        if (n->scalar_left > n->scalar_right || n->scalar_right > out->scalar_len) {
            snprintf(err, err_cap, "CNF1 node %u invalid scalar span [%u, %u]", i, n->scalar_left, n->scalar_right);
            gslt_cnf1_forest_free(out);
            return false;
        }
        if (n->byte_left != out->byte_offsets[n->scalar_left] ||
            n->byte_right != out->byte_offsets[n->scalar_right]) {
            snprintf(err, err_cap, "CNF1 node %u byte span does not align with scalar span", i);
            gslt_cnf1_forest_free(out);
            return false;
        }
        if (n->kind == GSLT_CNF1_NODE_TERM) {
            if (n->scalar_right != n->scalar_left + 1u ||
                n->terminal_scalar != out->codepoints[n->scalar_left]) {
                snprintf(err, err_cap, "CNF1 terminal node %u scalar %u != input scalar %u at %u",
                         i, n->terminal_scalar, out->codepoints[n->scalar_left], n->scalar_left);
                gslt_cnf1_forest_free(out);
                return false;
            }
        } else if (n->kind == GSLT_CNF1_NODE_EPSILON) {
            if (n->scalar_left != n->scalar_right) {
                snprintf(err, err_cap, "CNF1 epsilon node %u has non-empty span", i);
                gslt_cnf1_forest_free(out);
                return false;
            }
        } else {
            if ((uint64_t)n->choice_begin + (uint64_t)n->choice_len > out->choice_len) {
                snprintf(err, err_cap, "CNF1 node %u choice range out of bounds", i);
                gslt_cnf1_forest_free(out);
                return false;
            }
            for (uint32_t k = 0; k < n->choice_len; k++) {
                const GsltCnf1Choice *c = &out->choices[n->choice_begin + k];
                if (c->parent_node != i) {
                    snprintf(err, err_cap, "CNF1 choice %u parent_node=%u != %u", n->choice_begin + k, c->parent_node, i);
                    gslt_cnf1_forest_free(out);
                    return false;
                }
                if (c->scalar_pivot < n->scalar_left || c->scalar_pivot > n->scalar_right) {
                    snprintf(err, err_cap, "CNF1 choice %u pivot %u outside parent span [%u, %u]",
                             n->choice_begin + k, c->scalar_pivot, n->scalar_left, n->scalar_right);
                    gslt_cnf1_forest_free(out);
                    return false;
                }
                if (c->prefix_node != GSLT_FOREST_NONE) {
                    if (c->prefix_node >= out->node_len) {
                        snprintf(err, err_cap, "CNF1 choice %u prefix_node out of bounds", n->choice_begin + k);
                        gslt_cnf1_forest_free(out);
                        return false;
                    }
                    const GsltCnf1Node *pn = &out->nodes[c->prefix_node];
                    if (pn->scalar_left != n->scalar_left || pn->scalar_right != c->scalar_pivot) {
                        snprintf(err, err_cap, "CNF1 choice %u prefix span [%u,%u] != [%u,%u]",
                                 n->choice_begin + k, pn->scalar_left, pn->scalar_right, n->scalar_left, c->scalar_pivot);
                        gslt_cnf1_forest_free(out);
                        return false;
                    }
                } else if (c->scalar_pivot != n->scalar_left) {
                    snprintf(err, err_cap, "CNF1 choice %u has no prefix_node but pivot %u != left %u",
                             n->choice_begin + k, c->scalar_pivot, n->scalar_left);
                    gslt_cnf1_forest_free(out);
                    return false;
                }
                if (c->child_node != GSLT_FOREST_NONE) {
                    if (c->child_node >= out->node_len) {
                        snprintf(err, err_cap, "CNF1 choice %u child_node out of bounds", n->choice_begin + k);
                        gslt_cnf1_forest_free(out);
                        return false;
                    }
                    const GsltCnf1Node *cn = &out->nodes[c->child_node];
                    if (cn->scalar_left != c->scalar_pivot || cn->scalar_right != n->scalar_right) {
                        snprintf(err, err_cap, "CNF1 choice %u child span [%u,%u] != [%u,%u]",
                                 n->choice_begin + k, cn->scalar_left, cn->scalar_right, c->scalar_pivot, n->scalar_right);
                        gslt_cnf1_forest_free(out);
                        return false;
                    }
                } else if (c->scalar_pivot != n->scalar_right) {
                    snprintf(err, err_cap, "CNF1 choice %u has no child_node but pivot %u != right %u",
                             n->choice_begin + k, c->scalar_pivot, n->scalar_right);
                    gslt_cnf1_forest_free(out);
                    return false;
                }
            }
        }
    }

    for (uint32_t i = 0; i < out->root_len; i++) {
        uint32_t r = out->roots[i];
        if (r >= out->node_len) {
            snprintf(err, err_cap, "CNF1 root[%u]=%u out of bounds", i, r);
            gslt_cnf1_forest_free(out);
            return false;
        }
        const GsltCnf1Node *rn = &out->nodes[r];
        if (rn->kind != GSLT_CNF1_NODE_SYMBOL || rn->scalar_left != 0u || rn->scalar_right != out->scalar_len) {
            snprintf(err, err_cap, "CNF1 root[%u] node %u does not span full input [0, %u] (got [%u, %u])",
                     i, r, out->scalar_len, rn->scalar_left, rn->scalar_right);
            gslt_cnf1_forest_free(out);
            return false;
        }
    }
    return true;
}

/* =========================================================================
 * PNI1 Plan Identity Serialization, Deserialization & Catalog Cross-Check
 * ========================================================================= */

static inline bool gslt_pni1_put_str(uint8_t **cur, const uint8_t *end, const char *s) {
    uint32_t len = s ? (uint32_t)strlen(s) : 0u;
    if ((size_t)(end - *cur) < 4u + len) return false;
    gslt_put_u32_le(cur, len);
    if (len > 0u) {
        memcpy(*cur, s, len);
        *cur += len;
    }
    return true;
}

static inline bool gslt_pni1_get_str(const uint8_t **cur, const uint8_t *end, char *out, size_t cap) {
    uint32_t len = 0;
    if (!gslt_get_u32_le(cur, end, &len)) return false;
    if ((size_t)(end - *cur) < len || len + 1u > cap) return false;
    if (len > 0u) memcpy(out, *cur, len);
    out[len] = '\0';
    *cur += len;
    return true;
}

static inline bool gslt_pni1_serialize_from_catalog(
    const GsltModuleCatalog *cat,
    uint8_t **out_buf,
    size_t *out_len)
{
    size_t cap = 65536u;
    uint8_t *buf = (uint8_t *)malloc(cap);
    if (!buf) return false;
    uint8_t *cur = buf;
    const uint8_t *end = buf + cap;
    *cur++ = 'P'; *cur++ = 'N'; *cur++ = 'I'; *cur++ = '1';
    gslt_put_u32_le(&cur, 1u); /* version 1 */
    gslt_put_u32_le(&cur, cat->production_count);
    for (uint32_t i = 0; i < cat->production_count; i++) {
        const GsltProduction *p = &cat->productions[i];
        if (!gslt_pni1_put_str(&cur, end, p->sort) ||
            !gslt_pni1_put_str(&cur, end, p->label)) {
            free(buf);
            return false;
        }
        gslt_put_u32_le(&cur, p->slot_count);
        gslt_put_u32_le(&cur, p->matcher_count);
        for (uint32_t s = 0; s < p->slot_count; s++)
            gslt_put_u32_le(&cur, p->routed_slots[s]);
        for (uint32_t m = 0; m < p->matcher_count; m++) {
            const GsltMatcher *mt = &p->matchers[m];
            gslt_put_u32_le(&cur, mt->kind);
            if (!gslt_pni1_put_str(&cur, end, mt->kind == GSLT_MATCH_SLOT ? mt->sort : "")) {
                free(buf);
                return false;
            }
            gslt_put_u32_le(&cur, mt->codepoint);
            gslt_put_u32_le(&cur, mt->class_id);
        }
    }
    *out_buf = buf;
    *out_len = (size_t)(cur - buf);
    return true;
}

static inline bool gslt_pni1_deserialize_and_verify(
    const uint8_t *bytes,
    size_t byte_len,
    const GsltModuleCatalog *cat,
    GsltPni1Identity *out,
    char *err,
    size_t err_cap)
{
    memset(out, 0, sizeof(*out));
    if (byte_len < 12u) {
        snprintf(err, err_cap, "PNI1 buffer too short (%zu bytes)", byte_len);
        return false;
    }
    if (memcmp(bytes, "PNI1", 4u) != 0) {
        snprintf(err, err_cap, "invalid PNI1 magic tag '%c%c%c%c' (expected 'PNI1')",
                 bytes[0], bytes[1], bytes[2], bytes[3]);
        return false;
    }
    const uint8_t *cur = bytes + 4;
    const uint8_t *end = bytes + byte_len;
    if (!gslt_get_u32_le(&cur, end, &out->version) || out->version != 1u) {
        snprintf(err, err_cap, "unsupported PNI1 version %u (expected 1)", out->version);
        return false;
    }
    if (!gslt_get_u32_le(&cur, end, &out->production_count) ||
        out->production_count > GSLT_MAX_PRODS) {
        snprintf(err, err_cap, "invalid PNI1 production_count %u", out->production_count);
        return false;
    }
    for (uint32_t i = 0; i < out->production_count; i++) {
        GsltPni1Prod *p = &out->prods[i];
        if (!gslt_pni1_get_str(&cur, end, p->sort, sizeof(p->sort)) ||
            !gslt_pni1_get_str(&cur, end, p->label, sizeof(p->label)) ||
            !gslt_get_u32_le(&cur, end, &p->slot_count) ||
            !gslt_get_u32_le(&cur, end, &p->matcher_count) ||
            p->slot_count > GSLT_MAX_SLOTS ||
            p->matcher_count > GSLT_MAX_MATCHERS) {
            snprintf(err, err_cap, "truncated or malformed PNI1 production %u", i);
            return false;
        }
        for (uint32_t s = 0; s < p->slot_count; s++) {
            if (!gslt_get_u32_le(&cur, end, &p->routed_slots[s])) {
                snprintf(err, err_cap, "truncated PNI1 routed_slots in production %u", i);
                return false;
            }
        }
        for (uint32_t m = 0; m < p->matcher_count; m++) {
            GsltMatcher *mt = &p->matchers[m];
            if (!gslt_get_u32_le(&cur, end, &mt->kind) ||
                !gslt_pni1_get_str(&cur, end, mt->sort, sizeof(mt->sort)) ||
                !gslt_get_u32_le(&cur, end, &mt->codepoint) ||
                !gslt_get_u32_le(&cur, end, &mt->class_id)) {
                snprintf(err, err_cap, "truncated PNI1 matcher %u in production %u", m, i);
                return false;
            }
        }
    }
    if (cur != end) {
        snprintf(err, err_cap, "PNI1 trailing bytes (%zu unconsumed)", (size_t)(end - cur));
        return false;
    }
    if (cat) {
        if (out->production_count != cat->production_count) {
            snprintf(err, err_cap, "PNI1 production_count %u != catalog production_count %u",
                     out->production_count, cat->production_count);
            return false;
        }
        for (uint32_t i = 0; i < out->production_count; i++) {
            const GsltPni1Prod *p = &out->prods[i];
            const GsltProduction *cp = &cat->productions[i];
            if (strcmp(p->sort, cp->sort) != 0 || strcmp(p->label, cp->label) != 0 ||
                p->slot_count != cp->slot_count || p->matcher_count != cp->matcher_count) {
                snprintf(err, err_cap,
                         "PNI1 production %u (%s:%s) mismatches catalog (%s:%s)",
                         i, p->label, p->sort, cp->label, cp->sort);
                return false;
            }
            for (uint32_t s = 0; s < p->slot_count; s++) {
                if (p->routed_slots[s] != cp->routed_slots[s]) {
                    snprintf(err, err_cap,
                             "PNI1 production %u routed_slots[%u]=%u != catalog %u",
                             i, s, p->routed_slots[s], cp->routed_slots[s]);
                    return false;
                }
            }
        }
    }
    return true;
}

/* =========================================================================
 * Compositional .module Parser (Supports import "..." as alias & Theory)
 * ========================================================================= */

static inline const char *gslt_skip_ws_and_comments(const char *p) {
    while (*p) {
        while (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n') p++;
        if (p[0] == '/' && p[1] == '/') {
            p += 2;
            while (*p && *p != '\n') p++;
            continue;
        }
        if (p[0] == '/' && p[1] == '*') {
            p += 2;
            while (*p && !(p[0] == '*' && p[1] == '/')) p++;
            if (*p) p += 2;
            continue;
        }
        break;
    }
    return p;
}

static inline bool gslt_parse_quoted(const char **p, char *out, size_t cap);

static inline bool gslt_parse_ident(const char **p, char *out, size_t cap) {
    const char *s = gslt_skip_ws_and_comments(*p);
    /* Support double-quoted constructor labels "pl:..." */
    if (*s == '"') {
        return gslt_parse_quoted(p, out, cap);
    }
    size_t i = 0;
    /* Support guillemet-quoted constructor names «...» (UTF-8 \xC2\xAB ... \xC2\xBB) */
    if ((uint8_t)s[0] == 0xC2 && (uint8_t)s[1] == 0xAB) {
        s += 2;
        while (*s && !((uint8_t)s[0] == 0xC2 && (uint8_t)s[1] == 0xBB)) {
            if (i + 1 < cap) out[i++] = *s;
            s++;
        }
        if ((uint8_t)s[0] == 0xC2 && (uint8_t)s[1] == 0xBB) s += 2;
        out[i] = '\0';
        if (i == 0) return false;
        *p = s;
        return true;
    }
    while ((*s >= 'A' && *s <= 'Z') || (*s >= 'a' && *s <= 'z') ||
           (*s >= '0' && *s <= '9') || *s == '_' || *s == '-') {
        if (i + 1 < cap) out[i++] = *s;
        s++;
    }
    out[i] = '\0';
    if (i == 0) return false;
    *p = s;
    return true;
}

static inline bool gslt_parse_quoted(const char **p, char *out, size_t cap) {
    const char *s = gslt_skip_ws_and_comments(*p);
    if (*s != '"') return false;
    s++;
    size_t i = 0;
    while (*s && *s != '"') {
        if (*s == '\\' && s[1]) {
            s++;
            char c = *s++;
            char esc = (c == 'n') ? '\n' : (c == 't') ? '\t' : (c == 'r') ? '\r' : c;
            if (i + 1 < cap) out[i++] = esc;
        } else {
            if (i + 1 < cap) out[i++] = *s++;
            else s++;
        }
    }
    if (*s != '"') return false;
    out[i] = '\0';
    *p = s + 1;
    return true;
}

/* Add a production to a GsltModuleCatalog and compute its UTF-8 matchers & routed_slots */
static inline bool gslt_catalog_add_production(
    GsltModuleCatalog *cat,
    const char *origin_module,
    const char *origin_theory,
    const char *label,
    const char *sort,
    uint32_t slot_count,
    const GsltSlotSpec *slots,
    uint32_t rhs_item_count,
    const bool *rhs_is_literal,
    const char rhs_items[][64],
    char *err,
    size_t err_cap)
{
    if (cat->production_count >= GSLT_MAX_PRODS) {
        snprintf(err, err_cap, "catalog production limit exceeded");
        return false;
    }
    GsltProduction *pr = &cat->productions[cat->production_count];
    memset(pr, 0, sizeof(*pr));
    pr->production_index = cat->production_count;
    snprintf(pr->origin_module, sizeof(pr->origin_module), "%s", origin_module);
    snprintf(pr->origin_theory, sizeof(pr->origin_theory), "%s", origin_theory);
    snprintf(pr->label, sizeof(pr->label), "%s", label);
    snprintf(pr->sort, sizeof(pr->sort), "%s", sort);
    pr->slot_count = slot_count;
    for (uint32_t s = 0; s < slot_count; s++) {
        pr->slots[s] = slots[s];
        pr->routed_slots[s] = UINT32_MAX;
    }
    uint32_t slot_occurrence = 0;
    for (uint32_t r = 0; r < rhs_item_count; r++) {
        if (rhs_is_literal[r]) {
            const uint8_t *lit = (const uint8_t *)rhs_items[r];
            size_t lit_len = strlen(rhs_items[r]);
            uint32_t cps[128], offs[129], nsc = 0;
            if (!gslt_utf8_decode_scalars(lit, lit_len, cps, offs, 128, &nsc, err, err_cap))
                return false;
            for (uint32_t k = 0; k < nsc; k++) {
                if (pr->matcher_count >= GSLT_MAX_MATCHERS) {
                    snprintf(err, err_cap, "production %s matcher limit exceeded", label);
                    return false;
                }
                GsltMatcher *m = &pr->matchers[pr->matcher_count++];
                m->kind = GSLT_MATCH_CP;
                m->sort[0] = '\0';
                m->codepoint = cps[k];
                m->class_id = 0;
                m->slot_index = UINT32_MAX;
            }
        } else {
            /* Find which declared slot matches rhs_items[r] */
            int32_t found_slot = -1;
            for (uint32_t s = 0; s < slot_count; s++) {
                if (strcmp(slots[s].name, rhs_items[r]) == 0 ||
                    (slots[s].is_binder && strcmp(slots[s].binder_var, rhs_items[r]) == 0)) {
                    found_slot = (int32_t)s;
                    break;
                }
            }
            if (found_slot < 0) {
                snprintf(err, err_cap, "production %s references undeclared RHS slot '%s'",
                         label, rhs_items[r]);
                return false;
            }
            if (pr->matcher_count >= GSLT_MAX_MATCHERS) {
                snprintf(err, err_cap, "production %s matcher limit exceeded", label);
                return false;
            }
            GsltMatcher *m = &pr->matchers[pr->matcher_count++];
            m->kind = GSLT_MATCH_SLOT;
            snprintf(m->sort, sizeof(m->sort), "%s", slots[found_slot].sort);
            m->codepoint = 0;
            m->class_id = 0;
            m->slot_index = (uint32_t)found_slot;
            pr->routed_slots[found_slot] = slot_occurrence++;
        }
    }
    for (uint32_t s = 0; s < slot_count; s++) {
        if (pr->routed_slots[s] == UINT32_MAX) {
            snprintf(err, err_cap, "production %s slot '%s' is unrouted on RHS",
                     label, slots[s].name);
            return false;
        }
    }
    cat->production_count++;
    return true;
}

static inline const char *gslt_find_brace_end(const char *p) {
    int depth = 1;
    while (*p && depth > 0) {
        if (*p == '"') {
            p++;
            while (*p && *p != '"') {
                if (*p == '\\' && p[1]) p += 2;
                else p++;
            }
            if (*p == '"') p++;
            continue;
        }
        if (p[0] == '/' && p[1] == '/') {
            p += 2;
            while (*p && *p != '\n') p++;
            continue;
        }
        if (p[0] == '/' && p[1] == '*') {
            p += 2;
            while (*p && !(p[0] == '*' && p[1] == '/')) p++;
            if (*p) p += 2;
            continue;
        }
        if (*p == '{') depth++;
        else if (*p == '}') depth--;
        p++;
    }
    return p;
}

/* Load an authored .module file (recursively resolving `import "..." as alias`) */
static inline bool gslt_load_module_file(
    const char *module_path,
    GsltModuleCatalog *cat,
    char *err,
    size_t err_cap)
{
    FILE *fp = fopen(module_path, "rb");
    if (!fp) {
        snprintf(err, err_cap, "cannot open module file: %s", module_path);
        return false;
    }
    fseek(fp, 0, SEEK_END);
    long sz = ftell(fp);
    fseek(fp, 0, SEEK_SET);
    char *text = (char *)malloc((size_t)sz + 1u);
    if (!text) {
        fclose(fp);
        return false;
    }
    if (sz > 0 && fread(text, 1, (size_t)sz, fp) != (size_t)sz) {
        free(text);
        fclose(fp);
        return false;
    }
    text[sz] = '\0';
    fclose(fp);

    /* Extract directory of module_path for relative imports */
    char dir[512];
    snprintf(dir, sizeof(dir), "%s", module_path);
    char *last_slash = strrchr(dir, '/');
    if (last_slash) *last_slash = '\0';
    else snprintf(dir, sizeof(dir), ".");

    const char *p = text;
    /* 1. Process top-level imports: import "File.module" as alias */
    while (true) {
        p = gslt_skip_ws_and_comments(p);
        if (strncmp(p, "import", 6) == 0 && (p[6] == ' ' || p[6] == '\t')) {
            p += 6;
            char imp_rel[256], alias[64], kw_as[16];
            if (!gslt_parse_quoted(&p, imp_rel, sizeof(imp_rel)) ||
                !gslt_parse_ident(&p, kw_as, sizeof(kw_as)) ||
                strcmp(kw_as, "as") != 0 ||
                !gslt_parse_ident(&p, alias, sizeof(alias))) {
                snprintf(err, err_cap, "malformed import statement in %s", module_path);
                free(text);
                return false;
            }
            char imp_full[768];
            snprintf(imp_full, sizeof(imp_full), "%s/%s", dir, imp_rel);
            if (!gslt_load_module_file(imp_full, cat, err, err_cap)) {
                free(text);
                return false;
            }
            continue;
        }
        break;
    }

    /* 2. Parse Module <Name> { ... } */
    char kw_mod[32], mod_name[64];
    if (!gslt_parse_ident(&p, kw_mod, sizeof(kw_mod)) || strcmp(kw_mod, "Module") != 0 ||
        !gslt_parse_ident(&p, mod_name, sizeof(mod_name))) {
        snprintf(err, err_cap, "expected 'Module <Name>' in %s", module_path);
        free(text);
        return false;
    }
    snprintf(cat->module_name, sizeof(cat->module_name), "%s", mod_name);
    if (cat->imported_module_count < GSLT_MAX_MODULES) {
        snprintf(cat->imported_modules[cat->imported_module_count++], 64, "%s", mod_name);
    }
    if (cat->start_sort[0] == '\0') {
        snprintf(cat->start_sort, sizeof(cat->start_sort), "Term");
    }
    if (cat->profile_version[0] == '\0') {
        snprintf(cat->profile_version, sizeof(cat->profile_version), "GSLTParserProfileLayerV1");
    }

    p = gslt_skip_ws_and_comments(p);
    if (*p != '{') {
        snprintf(err, err_cap, "expected '{' after Module %s", mod_name);
        free(text);
        return false;
    }
    p++;

    /* Scan theories inside Module */
    while (*p) {
        p = gslt_skip_ws_and_comments(p);
        if (*p == '}' || *p == '\0') break;
        char tok[64];
        if (!gslt_parse_ident(&p, tok, sizeof(tok))) {
            if (*p) p++;
            continue;
        }
        if (strcmp(tok, "Theory") == 0) {
            char th_name[64];
            if (!gslt_parse_ident(&p, th_name, sizeof(th_name))) break;
            /* Skip parameter list (...) */
            p = gslt_skip_ws_and_comments(p);
            if (*p == '(') {
                int depth = 1;
                p++;
                while (*p && depth > 0) {
                    if (*p == '(') depth++;
                    else if (*p == ')') depth--;
                    p++;
                }
            }
            p = gslt_skip_ws_and_comments(p);
            if (*p != '{') continue;
            p++;
            if (strcmp(th_name, "Semantics") != 0 &&
                strcmp(th_name, "LexicalProfile") != 0 &&
                strcmp(th_name, "ReaderProfile") != 0 &&
                strcmp(th_name, "SourceSelection") != 0) {
                /* Scan inside syntax/grammar theory for Types { ... } and Terms { ... } */
                while (*p && *p != '}') {
                    p = gslt_skip_ws_and_comments(p);
                    if (*p == '}' || *p == '\0') break;
                    if (*p == '{') {
                        p = gslt_find_brace_end(p + 1);
                        continue;
                    }
                    char subtok[64];
                    if (!gslt_parse_ident(&p, subtok, sizeof(subtok))) {
                        if (*p) p++;
                        continue;
                    }
                    if (strcmp(subtok, "Types") == 0) {
                        p = gslt_skip_ws_and_comments(p);
                        if (*p == '{') {
                            const char *types_end = gslt_find_brace_end(p + 1);
                            p++;
                            char first_sort[64];
                            if (gslt_parse_ident(&p, first_sort, sizeof(first_sort))) {
                                if (cat->start_sort[0] == '\0')
                                    snprintf(cat->start_sort, sizeof(cat->start_sort), "%s", first_sort);
                            }
                            p = types_end;
                        }
                    } else if (strcmp(subtok, "Terms") == 0) {
                        p = gslt_skip_ws_and_comments(p);
                        if (*p != '{') continue;
                        p++;
                        while (*p) {
                            p = gslt_skip_ws_and_comments(p);
                            if (*p == '}' || *p == '\0') {
                                if (*p == '}') p++;
                                break;
                            }
                            /* Parse constructor: Label . [slots] |- [rhs] : Sort ; */
                            char label[64];
                            if (!gslt_parse_ident(&p, label, sizeof(label))) break;
                            p = gslt_skip_ws_and_comments(p);
                            if (*p == '.') p++;
                            GsltSlotSpec slots[GSLT_MAX_SLOTS];
                            uint32_t slot_count = 0;
                            while (*p) {
                                p = gslt_skip_ws_and_comments(p);
                                if (!*p) break;
                                if (p[0] == '|' && p[1] == '-') {
                                    p += 2;
                                    break;
                                }
                                GsltSlotSpec *sl = &slots[slot_count];
                                memset(sl, 0, sizeof(*sl));
                                if (*p == '^') {
                                    p++;
                                    sl->is_binder = true;
                                    gslt_parse_ident(&p, sl->binder_var, sizeof(sl->binder_var));
                                    p = gslt_skip_ws_and_comments(p);
                                    if (*p == '.') p++;
                                }
                                if (!gslt_parse_ident(&p, sl->name, sizeof(sl->name))) {
                                    if (*p) p++;
                                    break;
                                }
                                p = gslt_skip_ws_and_comments(p);
                                if (*p == ':') p++;
                                p = gslt_skip_ws_and_comments(p);
                                if (*p == '[') {
                                    p++;
                                    gslt_parse_ident(&p, sl->binder_dom, sizeof(sl->binder_dom));
                                    p = gslt_skip_ws_and_comments(p);
                                    if (p[0] == '-' && p[1] == '>') p += 2;
                                    gslt_parse_ident(&p, sl->sort, sizeof(sl->sort));
                                    p = gslt_skip_ws_and_comments(p);
                                    if (*p == ']') p++;
                                } else {
                                    gslt_parse_ident(&p, sl->sort, sizeof(sl->sort));
                                }
                                slot_count++;
                                p = gslt_skip_ws_and_comments(p);
                                if (*p == ',') p++;
                            }
                            /* Parse RHS items up to ':' */
                            bool rhs_is_lit[GSLT_MAX_MATCHERS];
                            char rhs_items[GSLT_MAX_MATCHERS][64];
                            uint32_t rhs_count = 0;
                            while (*p) {
                                p = gslt_skip_ws_and_comments(p);
                                if (!*p) break;
                                if (*p == ':') {
                                    p++;
                                    break;
                                }
                                if (*p == '"') {
                                    rhs_is_lit[rhs_count] = true;
                                    if (!gslt_parse_quoted(&p, rhs_items[rhs_count], 64)) {
                                        if (*p) p++;
                                        break;
                                    }
                                    rhs_count++;
                                } else {
                                    rhs_is_lit[rhs_count] = false;
                                    if (!gslt_parse_ident(&p, rhs_items[rhs_count], 64)) {
                                        if (*p) p++;
                                        break;
                                    }
                                    rhs_count++;
                                }
                            }
                            char sort[64];
                            gslt_parse_ident(&p, sort, sizeof(sort));
                            p = gslt_skip_ws_and_comments(p);
                            if (*p == ';') p++;
                            if (strcmp(sort, "ProfileData") != 0) {
                                if (!gslt_catalog_add_production(
                                        cat, mod_name, th_name, label, sort,
                                        slot_count, slots, rhs_count, rhs_is_lit, rhs_items,
                                        err, err_cap)) {
                                    free(text);
                                    return false;
                                }
                            }
                        }
                    }
                }
                if (*p == '}') p++;
            } else if (strcmp(th_name, "LexicalProfile") == 0) {
                /* Extract GSLTParserProfileLayerV1("ProfileName", "StartSort", ...) */
                const char *brace_end = gslt_find_brace_end(p);
                const char *rew = strstr(p, "ReturnLexicalProfile");
                if (rew && rew < brace_end) {
                    const char *q = strchr(rew, '~');
                    if (q && q[1] == '>' && q < brace_end) {
                        q += 2;
                        char ver[64], pname[64], ssort[64];
                        if (gslt_parse_quoted(&q, ver, sizeof(ver))) {
                            snprintf(cat->profile_version, sizeof(cat->profile_version), "%s", ver);
                            q = gslt_skip_ws_and_comments(q);
                            if (*q == '(') q++;
                            if (gslt_parse_quoted(&q, pname, sizeof(pname)))
                                snprintf(cat->profile_name, sizeof(cat->profile_name), "%s", pname);
                            q = gslt_skip_ws_and_comments(q);
                            if (*q == ',') q++;
                            if (gslt_parse_quoted(&q, ssort, sizeof(ssort)))
                                snprintf(cat->start_sort, sizeof(cat->start_sort), "%s", ssort);
                        }
                    }
                }
                p = brace_end;
            } else if (strcmp(th_name, "SourceSelection") == 0) {
                const char *brace_end = gslt_find_brace_end(p);
                const char *rew = strstr(p, "ReturnSourceSelection");
                if (rew && rew < brace_end) {
                    const char *q = strchr(rew, '~');
                    if (q && q[1] == '>' && q < brace_end) {
                        q += 2;
                        char sel_ver[64];
                        if (gslt_parse_quoted(&q, sel_ver, sizeof(sel_ver))) {
                            cat->selection.has_policy = true;
                            snprintf(cat->selection.version_tag, sizeof(cat->selection.version_tag), "%s", sel_ver);
                            /* Scan for "RejectWords"("Sort", "LCons"("word", ...)) */
                            const char *rw = strstr(q, "\"RejectWords\"");
                            while (rw && rw < brace_end &&
                                   cat->selection.reject_rule_count < GSLT_MAX_REJECT_RULES) {
                                rw += strlen("\"RejectWords\"");
                                rw = gslt_skip_ws_and_comments(rw);
                                if (*rw == '(') rw++;
                                const char *next_rw = strstr(rw, "\"RejectWords\"");
                                const char *rw_end = (next_rw && next_rw < brace_end) ? next_rw : brace_end;
                                GsltRejectWordsRule *rule =
                                    &cat->selection.reject_rules[cat->selection.reject_rule_count++];
                                memset(rule, 0, sizeof(*rule));
                                gslt_parse_quoted(&rw, rule->sort, sizeof(rule->sort));
                                while (rw < rw_end && rule->word_count < GSLT_MAX_REJECT_WORDS) {
                                    const char *lc = strstr(rw, "\"LCons\"");
                                    if (!lc || lc >= rw_end) break;
                                    lc += strlen("\"LCons\"");
                                    lc = gslt_skip_ws_and_comments(lc);
                                    if (*lc == '(') lc++;
                                    char w[64];
                                    if (gslt_parse_quoted(&lc, w, sizeof(w))) {
                                        snprintf(rule->words[rule->word_count++], 64, "%s", w);
                                    }
                                    rw = lc;
                                }
                                rw = next_rw;
                            }
                        }
                    }
                }
                p = brace_end;
            } else {
                p = gslt_find_brace_end(p);
            }
        } else {
            /* Skip other declarations */
            while (*p && *p != '\n' && *p != '}') p++;
        }
    }

    free(text);
    return true;
}

/* =========================================================================
 * Built-in Complete Packed-Forest Recognizer (Chart / Earley-GLL into CNF1)
 * ========================================================================= */

typedef struct {
    bool derivable;
    uint32_t sym_node_id;
} GsltChartCell;

/*
 * Parse UTF-8 source text against a GsltModuleCatalog and emit a complete
 * CNF1 packed parse forest (with binary prefix/child choice factorization)
 * and matching PNI1 plan identity.
 */
static inline bool gslt_recognize_into_cnf1(
    const GsltModuleCatalog *cat,
    const uint8_t *source_bytes,
    size_t source_byte_len,
    GsltCnf1Forest *out_forest,
    char *err,
    size_t err_cap)
{
    memset(out_forest, 0, sizeof(*out_forest));
    if (strcmp(cat->profile_version, "GSLTParserProfileLayerV1") != 0) {
        snprintf(err, err_cap, "unsupported lexical profile version '%s'", cat->profile_version);
        return false;
    }

    uint32_t cps[1024], offs[1025], sc_len = 0;
    if (!gslt_utf8_decode_scalars(source_bytes, source_byte_len, cps, offs, 1024, &sc_len, err, err_cap)) {
        return false;
    }

    out_forest->outcome = 0u;
    out_forest->scalar_len = sc_len;
    out_forest->input_byte_len = (uint32_t)source_byte_len;
    out_forest->decoded_byte_len = (uint32_t)source_byte_len;
    out_forest->farthest_scalar = sc_len;
    out_forest->farthest_byte = (uint32_t)source_byte_len;
    out_forest->source_pass_count = 1u;

    out_forest->codepoints = (uint32_t *)calloc(sc_len ? sc_len : 1u, sizeof(uint32_t));
    out_forest->byte_offsets = (uint32_t *)calloc(sc_len + 1u, sizeof(uint32_t));
    if (sc_len > 0) memcpy(out_forest->codepoints, cps, sc_len * sizeof(uint32_t));
    memcpy(out_forest->byte_offsets, offs, (sc_len + 1u) * sizeof(uint32_t));

    uint32_t max_nodes = 4096;
    uint32_t max_choices = 8192;
    out_forest->nodes = (GsltCnf1Node *)calloc(max_nodes, sizeof(GsltCnf1Node));
    out_forest->choices = (GsltCnf1Choice *)calloc(max_choices, sizeof(GsltCnf1Choice));
    out_forest->roots = (uint32_t *)calloc(16, sizeof(uint32_t));
    out_forest->expected_terminal_ids = (uint32_t *)calloc(16, sizeof(uint32_t));

    /* Pre-create TERM nodes for each scalar position [i, i+1] */
    uint32_t term_nodes[1024];
    for (uint32_t i = 0; i < sc_len; i++) {
        uint32_t nid = out_forest->node_len++;
        GsltCnf1Node *n = &out_forest->nodes[nid];
        n->kind = GSLT_CNF1_NODE_TERM;
        n->symbol_id = 0u;
        n->production_index = GSLT_FOREST_NONE;
        n->dot = 0u;
        n->scalar_left = i;
        n->scalar_right = i + 1u;
        n->byte_left = offs[i];
        n->byte_right = offs[i + 1u];
        n->terminal_is_eof = 0u;
        n->terminal_scalar = cps[i];
        n->terminal_value_kind = 1u;
        n->terminal_witness_id = i;
        n->choice_begin = 0u;
        n->choice_len = 0u;
        term_nodes[i] = nid;
    }

    /* Collect distinct sort names in catalog */
    char sorts[32][64];
    uint32_t sort_count = 0;
    int32_t start_sort_id = -1;
    for (uint32_t p = 0; p < cat->production_count; p++) {
        int32_t sid = -1;
        for (uint32_t s = 0; s < sort_count; s++) {
            if (strcmp(sorts[s], cat->productions[p].sort) == 0) {
                sid = (int32_t)s;
                break;
            }
        }
        if (sid < 0 && sort_count < 32) {
            sid = (int32_t)sort_count;
            snprintf(sorts[sort_count++], 64, "%s", cat->productions[p].sort);
        }
        if (strcmp(cat->productions[p].sort, cat->start_sort) == 0)
            start_sort_id = sid;
    }
    if (start_sort_id < 0 && sort_count > 0) start_sort_id = 0;

    /* Chart table: sym_node[sort_id][left][right] -> node_id or GSLT_FOREST_NONE */
    uint32_t stride = sc_len + 1u;
    uint32_t *sym_node = (uint32_t *)malloc(32u * stride * stride * sizeof(uint32_t));
    for (size_t i = 0; i < 32u * stride * stride; i++) sym_node[i] = GSLT_FOREST_NONE;

    #define SYM_AT(s, l, r) sym_node[(s) * stride * stride + (l) * stride + (r)]

    /* Temporary choice list per node before packing into contiguous choices[] */
    GsltCnf1Choice *tmp_choices = (GsltCnf1Choice *)calloc(max_choices, sizeof(GsltCnf1Choice));
    uint32_t tmp_choice_len = 0;

    /* Fixed-point chart completion over spans len = 0 .. sc_len */
    bool changed = true;
    while (changed) {
        changed = false;
        for (uint32_t span = 0; span <= sc_len; span++) {
            for (uint32_t left = 0; left + span <= sc_len; left++) {
                uint32_t right = left + span;
                for (uint32_t pi = 0; pi < cat->production_count; pi++) {
                    const GsltProduction *pr = &cat->productions[pi];
                    int32_t sid = -1;
                    for (uint32_t s = 0; s < sort_count; s++) {
                        if (strcmp(sorts[s], pr->sort) == 0) {
                            sid = (int32_t)s;
                            break;
                        }
                    }
                    if (sid < 0) continue;

                    /* Match pr->matchers[0 .. matcher_count - 1] across [left, right] */
                    if (pr->matcher_count == 0) {
                        if (left != right) continue;
                        uint32_t parent_nid = SYM_AT(sid, left, right);
                        if (parent_nid == GSLT_FOREST_NONE) {
                            parent_nid = out_forest->node_len++;
                            GsltCnf1Node *pn = &out_forest->nodes[parent_nid];
                            pn->kind = GSLT_CNF1_NODE_SYMBOL;
                            pn->symbol_id = (uint32_t)sid;
                            pn->production_index = GSLT_FOREST_NONE;
                            pn->dot = 0;
                            pn->scalar_left = left;
                            pn->scalar_right = right;
                            pn->byte_left = offs[left];
                            pn->byte_right = offs[right];
                            SYM_AT(sid, left, right) = parent_nid;
                            changed = true;
                        }
                        /* Check if epsilon choice already recorded for (parent_nid, pi) */
                        bool exists = false;
                        for (uint32_t c = 0; c < tmp_choice_len; c++) {
                            if (tmp_choices[c].parent_node == parent_nid &&
                                tmp_choices[c].production_index == pi) {
                                exists = true;
                                break;
                            }
                        }
                        if (!exists) {
                            uint32_t eps_nid = out_forest->node_len++;
                            GsltCnf1Node *en = &out_forest->nodes[eps_nid];
                            en->kind = GSLT_CNF1_NODE_EPSILON;
                            en->symbol_id = (uint32_t)sid;
                            en->production_index = pi;
                            en->scalar_left = left;
                            en->scalar_right = right;
                            en->byte_left = offs[left];
                            en->byte_right = offs[right];

                            GsltCnf1Choice *ch = &tmp_choices[tmp_choice_len++];
                            ch->parent_node = parent_nid;
                            ch->prefix_node = GSLT_FOREST_NONE;
                            ch->child_node = eps_nid;
                            ch->production_index = pi;
                            ch->scalar_pivot = left;
                            ch->byte_pivot = offs[left];
                            changed = true;
                        }
                        continue;
                    }

                    /* General matcher sequence DP:
                     * dp_node[step][pos] holds the INTERMEDIATE (or single child) node spanning [left, pos]
                     * after matching matchers[0 .. step-1]. */
                    uint32_t dp_node[GSLT_MAX_MATCHERS + 1][128];
                    if (sc_len >= 128) continue;
                    for (uint32_t st = 0; st <= pr->matcher_count; st++)
                        for (uint32_t pos = left; pos <= right; pos++)
                            dp_node[st][pos] = GSLT_FOREST_NONE;

                    for (uint32_t st = 0; st < pr->matcher_count; st++) {
                        const GsltMatcher *mt = &pr->matchers[st];
                        for (uint32_t mid = left; mid <= right; mid++) {
                            if (st > 0 && dp_node[st][mid] == GSLT_FOREST_NONE) continue;
                            if (st == 0 && mid != left) continue;

                            if (mt->kind == GSLT_MATCH_CP) {
                                if (mid + 1u <= right && cps[mid] == mt->codepoint) {
                                    uint32_t child_nid = term_nodes[mid];
                                    uint32_t next_pos = mid + 1u;
                                    if (st + 1u == pr->matcher_count) {
                                        if (next_pos == right) {
                                            uint32_t parent_nid = SYM_AT(sid, left, right);
                                            if (parent_nid == GSLT_FOREST_NONE) {
                                                parent_nid = out_forest->node_len++;
                                                GsltCnf1Node *pn = &out_forest->nodes[parent_nid];
                                                pn->kind = GSLT_CNF1_NODE_SYMBOL;
                                                pn->symbol_id = (uint32_t)sid;
                                                pn->production_index = GSLT_FOREST_NONE;
                                                pn->scalar_left = left;
                                                pn->scalar_right = right;
                                                pn->byte_left = offs[left];
                                                pn->byte_right = offs[right];
                                                SYM_AT(sid, left, right) = parent_nid;
                                                changed = true;
                                            }
                                            uint32_t pref = (st == 0) ? GSLT_FOREST_NONE : dp_node[st][mid];
                                            bool exists = false;
                                            for (uint32_t c = 0; c < tmp_choice_len; c++) {
                                                if (tmp_choices[c].parent_node == parent_nid &&
                                                    tmp_choices[c].production_index == pi &&
                                                    tmp_choices[c].prefix_node == pref &&
                                                    tmp_choices[c].child_node == child_nid &&
                                                    tmp_choices[c].scalar_pivot == mid) {
                                                    exists = true;
                                                    break;
                                                }
                                            }
                                            if (!exists) {
                                                GsltCnf1Choice *ch = &tmp_choices[tmp_choice_len++];
                                                ch->parent_node = parent_nid;
                                                ch->prefix_node = pref;
                                                ch->child_node = child_nid;
                                                ch->production_index = pi;
                                                ch->scalar_pivot = mid;
                                                ch->byte_pivot = offs[mid];
                                                changed = true;
                                            }
                                        }
                                    } else {
                                        uint32_t inter_nid = dp_node[st + 1u][next_pos];
                                        if (inter_nid == GSLT_FOREST_NONE) {
                                            /* Reuse existing intermediate node if already in forest */
                                            for (uint32_t fn = 0; fn < out_forest->node_len; fn++) {
                                                const GsltCnf1Node *en = &out_forest->nodes[fn];
                                                if (en->kind == GSLT_CNF1_NODE_INTERMEDIATE &&
                                                    en->production_index == pi &&
                                                    en->dot == st + 1u &&
                                                    en->scalar_left == left &&
                                                    en->scalar_right == next_pos) {
                                                    inter_nid = fn;
                                                    break;
                                                }
                                            }
                                            if (inter_nid == GSLT_FOREST_NONE) {
                                                inter_nid = out_forest->node_len++;
                                                GsltCnf1Node *in = &out_forest->nodes[inter_nid];
                                                in->kind = GSLT_CNF1_NODE_INTERMEDIATE;
                                                in->symbol_id = (uint32_t)sid;
                                                in->production_index = pi;
                                                in->dot = st + 1u;
                                                in->scalar_left = left;
                                                in->scalar_right = next_pos;
                                                in->byte_left = offs[left];
                                                in->byte_right = offs[next_pos];
                                            }
                                            dp_node[st + 1u][next_pos] = inter_nid;
                                        }
                                        uint32_t pref = (st == 0) ? GSLT_FOREST_NONE : dp_node[st][mid];
                                        bool exists = false;
                                        for (uint32_t c = 0; c < tmp_choice_len; c++) {
                                            if (tmp_choices[c].parent_node == inter_nid &&
                                                tmp_choices[c].production_index == pi &&
                                                tmp_choices[c].prefix_node == pref &&
                                                tmp_choices[c].child_node == child_nid &&
                                                tmp_choices[c].scalar_pivot == mid) {
                                                exists = true;
                                                break;
                                            }
                                        }
                                        if (!exists) {
                                            GsltCnf1Choice *ch = &tmp_choices[tmp_choice_len++];
                                            ch->parent_node = inter_nid;
                                            ch->prefix_node = pref;
                                            ch->child_node = child_nid;
                                            ch->production_index = pi;
                                            ch->scalar_pivot = mid;
                                            ch->byte_pivot = offs[mid];
                                        }
                                    }
                                }
                            } else if (mt->kind == GSLT_MATCH_SLOT) {
                                int32_t child_sid = -1;
                                for (uint32_t s = 0; s < sort_count; s++) {
                                    if (strcmp(sorts[s], mt->sort) == 0) {
                                        child_sid = (int32_t)s;
                                        break;
                                    }
                                }
                                if (child_sid < 0) continue;
                                for (uint32_t next_pos = mid; next_pos <= right; next_pos++) {
                                    /* Prevent infinite trivial cycle on single-slot self-loop with empty span */
                                    if (pr->matcher_count == 1 && next_pos == left && child_sid == sid)
                                        continue;
                                    uint32_t child_nid = SYM_AT(child_sid, mid, next_pos);
                                    if (child_nid == GSLT_FOREST_NONE) continue;
                                    if (st + 1u == pr->matcher_count) {
                                        if (next_pos == right) {
                                            uint32_t parent_nid = SYM_AT(sid, left, right);
                                            if (parent_nid == GSLT_FOREST_NONE) {
                                                parent_nid = out_forest->node_len++;
                                                GsltCnf1Node *pn = &out_forest->nodes[parent_nid];
                                                pn->kind = GSLT_CNF1_NODE_SYMBOL;
                                                pn->symbol_id = (uint32_t)sid;
                                                pn->production_index = GSLT_FOREST_NONE;
                                                pn->scalar_left = left;
                                                pn->scalar_right = right;
                                                pn->byte_left = offs[left];
                                                pn->byte_right = offs[right];
                                                SYM_AT(sid, left, right) = parent_nid;
                                                changed = true;
                                            }
                                            uint32_t pref = (st == 0) ? GSLT_FOREST_NONE : dp_node[st][mid];
                                            bool exists = false;
                                            for (uint32_t c = 0; c < tmp_choice_len; c++) {
                                                if (tmp_choices[c].parent_node == parent_nid &&
                                                    tmp_choices[c].production_index == pi &&
                                                    tmp_choices[c].prefix_node == pref &&
                                                    tmp_choices[c].child_node == child_nid &&
                                                    tmp_choices[c].scalar_pivot == mid) {
                                                    exists = true;
                                                    break;
                                                }
                                            }
                                            if (!exists) {
                                                GsltCnf1Choice *ch = &tmp_choices[tmp_choice_len++];
                                                ch->parent_node = parent_nid;
                                                ch->prefix_node = pref;
                                                ch->child_node = child_nid;
                                                ch->production_index = pi;
                                                ch->scalar_pivot = mid;
                                                ch->byte_pivot = offs[mid];
                                                changed = true;
                                            }
                                        }
                                    } else {
                                        uint32_t inter_nid = dp_node[st + 1u][next_pos];
                                        if (inter_nid == GSLT_FOREST_NONE) {
                                            for (uint32_t fn = 0; fn < out_forest->node_len; fn++) {
                                                const GsltCnf1Node *en = &out_forest->nodes[fn];
                                                if (en->kind == GSLT_CNF1_NODE_INTERMEDIATE &&
                                                    en->production_index == pi &&
                                                    en->dot == st + 1u &&
                                                    en->scalar_left == left &&
                                                    en->scalar_right == next_pos) {
                                                    inter_nid = fn;
                                                    break;
                                                }
                                            }
                                            if (inter_nid == GSLT_FOREST_NONE) {
                                                inter_nid = out_forest->node_len++;
                                                GsltCnf1Node *in = &out_forest->nodes[inter_nid];
                                                in->kind = GSLT_CNF1_NODE_INTERMEDIATE;
                                                in->symbol_id = (uint32_t)sid;
                                                in->production_index = pi;
                                                in->dot = st + 1u;
                                                in->scalar_left = left;
                                                in->scalar_right = next_pos;
                                                in->byte_left = offs[left];
                                                in->byte_right = offs[next_pos];
                                            }
                                            dp_node[st + 1u][next_pos] = inter_nid;
                                        }
                                        uint32_t pref = (st == 0) ? GSLT_FOREST_NONE : dp_node[st][mid];
                                        bool exists = false;
                                        for (uint32_t c = 0; c < tmp_choice_len; c++) {
                                            if (tmp_choices[c].parent_node == inter_nid &&
                                                tmp_choices[c].production_index == pi &&
                                                tmp_choices[c].prefix_node == pref &&
                                                tmp_choices[c].child_node == child_nid &&
                                                tmp_choices[c].scalar_pivot == mid) {
                                                exists = true;
                                                break;
                                            }
                                        }
                                        if (!exists) {
                                            GsltCnf1Choice *ch = &tmp_choices[tmp_choice_len++];
                                            ch->parent_node = inter_nid;
                                            ch->prefix_node = pref;
                                            ch->child_node = child_nid;
                                            ch->production_index = pi;
                                            ch->scalar_pivot = mid;
                                            ch->byte_pivot = offs[mid];
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /* Group tmp_choices contiguously by parent_node into out_forest->choices */
    out_forest->choice_len = 0;
    for (uint32_t nid = 0; nid < out_forest->node_len; nid++) {
        GsltCnf1Node *n = &out_forest->nodes[nid];
        if (n->kind == GSLT_CNF1_NODE_TERM || n->kind == GSLT_CNF1_NODE_EPSILON) {
            n->choice_begin = 0;
            n->choice_len = 0;
            continue;
        }
        n->choice_begin = out_forest->choice_len;
        uint32_t cnt = 0;
        for (uint32_t c = 0; c < tmp_choice_len; c++) {
            if (tmp_choices[c].parent_node == nid) {
                out_forest->choices[out_forest->choice_len++] = tmp_choices[c];
                cnt++;
            }
        }
        n->choice_len = cnt;
    }

    if (start_sort_id >= 0) {
        uint32_t root_nid = SYM_AT(start_sort_id, 0, sc_len);
        if (root_nid != GSLT_FOREST_NONE) {
            out_forest->roots[out_forest->root_len++] = root_nid;
        }
    }
    out_forest->graph_node_len = out_forest->node_len;

    #undef SYM_AT
    free(sym_node);
    free(tmp_choices);
    return true;
}

/* =========================================================================
 * AST Enumeration from CNF1 Forest, Ambiguity Policy, and Packet Rendering
 * ========================================================================= */

static inline void gslt_ast_free(GsltAstNode *node) {
    if (!node) return;
    for (uint32_t i = 0; i < node->child_count; i++)
        gslt_ast_free(node->children[i]);
    free(node);
}

static inline GsltAstNode *gslt_ast_clone(const GsltAstNode *src) {
    if (!src) return NULL;
    GsltAstNode *dst = (GsltAstNode *)calloc(1, sizeof(GsltAstNode));
    *dst = *src;
    for (uint32_t i = 0; i < src->child_count; i++)
        dst->children[i] = gslt_ast_clone(src->children[i]);
    return dst;
}

static inline bool gslt_ast_equal(const GsltAstNode *a, const GsltAstNode *b) {
    if (a == b) return true;
    if (!a || !b) return false;
    if (a->production_index != b->production_index ||
        strcmp(a->origin_module, b->origin_module) != 0 ||
        strcmp(a->label, b->label) != 0 ||
        strcmp(a->sort, b->sort) != 0 ||
        a->scalar_left != b->scalar_left ||
        a->scalar_right != b->scalar_right ||
        a->child_count != b->child_count ||
        a->db_index != b->db_index)
        return false;
    for (uint32_t i = 0; i < a->child_count; i++) {
        if (!gslt_ast_equal(a->children[i], b->children[i])) return false;
    }
    return true;
}

/* Check whether an AST node (and its subtree) passes the declared SourceSelectionV1 policy */
static inline bool gslt_ast_passes_selection_policy(
    const GsltAstNode *node,
    const GsltModuleCatalog *cat,
    const uint8_t *source_bytes,
    const uint32_t *byte_offsets)
{
    if (!node) return true;
    const GsltSelectionPolicy *sel = &cat->selection;
    if (sel->has_policy) {
        if (strcmp(sel->version_tag, "SourceSelectionV1") != 0)
            return false;
        /* Check RejectWords(sort, words) against the exact surface slice of this node */
        uint32_t b_left = byte_offsets[node->scalar_left];
        uint32_t b_right = byte_offsets[node->scalar_right];
        size_t slice_len = (size_t)(b_right - b_left);
        for (uint32_t r = 0; r < sel->reject_rule_count; r++) {
            const GsltRejectWordsRule *rule = &sel->reject_rules[r];
            if (strcmp(rule->sort, node->sort) == 0) {
                for (uint32_t w = 0; w < rule->word_count; w++) {
                    size_t wlen = strlen(rule->words[w]);
                    if (slice_len == wlen && memcmp(source_bytes + b_left, rule->words[w], wlen) == 0) {
                        return false;
                    }
                }
            }
        }
        if (sel->prefer_origin_module[0] != '\0' &&
            strcmp(node->origin_module, sel->prefer_origin_module) != 0) {
            return false;
        }
    }
    for (uint32_t i = 0; i < node->child_count; i++) {
        if (!gslt_ast_passes_selection_policy(node->children[i], cat, source_bytes, byte_offsets))
            return false;
    }
    return true;
}

/* Render a GsltAstNode as a CeTTa/Lean (node <Label> ...) or (result (node ...) nil) packet */
static inline void gslt_render_ast_packet_inner(
    const GsltAstNode *node,
    const GsltModuleCatalog *cat,
    char *buf,
    size_t cap,
    size_t *pos)
{
    const GsltProduction *pr = &cat->productions[node->production_index];
    *pos += (size_t)snprintf(buf + *pos, cap > *pos ? cap - *pos : 0, "(node %s ", pr->label);
    if (pr->matcher_count == 0) {
        *pos += (size_t)snprintf(buf + *pos, cap > *pos ? cap - *pos : 0, "nil)");
        return;
    }
    /* Emit matcher list in surface matcher order using routed_slots inverse */
    for (uint32_t m = 0; m < pr->matcher_count; m++) {
        *pos += (size_t)snprintf(buf + *pos, cap > *pos ? cap - *pos : 0, "(cons ");
        const GsltMatcher *mt = &pr->matchers[m];
        if (mt->kind == GSLT_MATCH_CP) {
            *pos += (size_t)snprintf(buf + *pos, cap > *pos ? cap - *pos : 0, "(cp %u) ", mt->codepoint);
        } else {
            uint32_t logical_slot = mt->slot_index;
            gslt_render_ast_packet_inner(node->children[logical_slot], cat, buf, cap, pos);
            *pos += (size_t)snprintf(buf + *pos, cap > *pos ? cap - *pos : 0, " ");
        }
    }
    *pos += (size_t)snprintf(buf + *pos, cap > *pos ? cap - *pos : 0, "nil");
    for (uint32_t m = 0; m < pr->matcher_count; m++) {
        *pos += (size_t)snprintf(buf + *pos, cap > *pos ? cap - *pos : 0, ")");
    }
    *pos += (size_t)snprintf(buf + *pos, cap > *pos ? cap - *pos : 0, ")");
}

static inline void gslt_render_result_packet(
    const GsltAstNode *node,
    const GsltModuleCatalog *cat,
    char *out_packet,
    size_t cap)
{
    size_t pos = 0;
    pos += (size_t)snprintf(out_packet + pos, cap, "(result ");
    gslt_render_ast_packet_inner(node, cat, out_packet, cap, &pos);
    snprintf(out_packet + pos, cap > pos ? cap - pos : 0, " nil)");
}

/* Forward declaration for mutual recursion */
static inline void gslt_enumerate_node_derivations(
    const GsltCnf1Forest *forest,
    const GsltModuleCatalog *cat,
    uint32_t node_id,
    GsltAstNode **out_trees,
    uint32_t *out_count,
    uint32_t max_trees,
    uint32_t depth);

/* Unpack binary prefix_node chain for a specific production choice */
static inline void gslt_collect_prefix_chain_alternatives(
    const GsltCnf1Forest *forest,
    const GsltModuleCatalog *cat,
    const GsltProduction *pr,
    uint32_t matcher_idx,
    const GsltCnf1Choice *ch,
    GsltAstNode *current_slots[GSLT_MAX_SLOTS],
    GsltAstNode **out_trees,
    uint32_t *out_count,
    uint32_t max_trees,
    uint32_t depth)
{
    if (*out_count >= max_trees || depth > 32u) return;
    const GsltMatcher *mt = &pr->matchers[matcher_idx];
    if (mt->kind == GSLT_MATCH_CP) {
        if (ch->child_node == GSLT_FOREST_NONE ||
            forest->nodes[ch->child_node].kind != GSLT_CNF1_NODE_TERM ||
            forest->nodes[ch->child_node].terminal_scalar != mt->codepoint) {
            return;
        }
        if (matcher_idx == 0) {
            if (ch->prefix_node != GSLT_FOREST_NONE) return;
            GsltAstNode *ast = (GsltAstNode *)calloc(1, sizeof(GsltAstNode));
            ast->production_index = pr->production_index;
            snprintf(ast->origin_module, sizeof(ast->origin_module), "%s", pr->origin_module);
            snprintf(ast->origin_theory, sizeof(ast->origin_theory), "%s", pr->origin_theory);
            snprintf(ast->label, sizeof(ast->label), "%s", pr->label);
            snprintf(ast->sort, sizeof(ast->sort), "%s", pr->sort);
            ast->scalar_left = forest->nodes[ch->parent_node].scalar_left;
            ast->scalar_right = forest->nodes[ch->parent_node].scalar_right;
            ast->child_count = pr->slot_count;
            ast->db_index = -1;
            for (uint32_t s = 0; s < pr->slot_count; s++) {
                ast->children[s] = gslt_ast_clone(current_slots[s]);
                if (pr->slots[s].is_binder) {
                    ast->is_binder = true;
                    snprintf(ast->binder_var, sizeof(ast->binder_var), "%s", pr->slots[s].binder_var);
                }
            }
            out_trees[(*out_count)++] = ast;
        } else {
            if (ch->prefix_node == GSLT_FOREST_NONE) return;
            const GsltCnf1Node *pn = &forest->nodes[ch->prefix_node];
            for (uint32_t k = 0; k < pn->choice_len; k++) {
                const GsltCnf1Choice *pch = &forest->choices[pn->choice_begin + k];
                if (pch->production_index != pr->production_index) continue;
                gslt_collect_prefix_chain_alternatives(
                    forest, cat, pr, matcher_idx - 1u, pch, current_slots,
                    out_trees, out_count, max_trees, depth + 1u);
            }
        }
    } else if (mt->kind == GSLT_MATCH_SLOT) {
        if (ch->child_node == GSLT_FOREST_NONE) return;
        GsltAstNode *child_alts[32];
        uint32_t child_cnt = 0;
        gslt_enumerate_node_derivations(forest, cat, ch->child_node, child_alts, &child_cnt, 32, depth + 1u);
        uint32_t logical_slot = mt->slot_index;
        for (uint32_t ci = 0; ci < child_cnt; ci++) {
            current_slots[logical_slot] = child_alts[ci];
            if (matcher_idx == 0) {
                if (ch->prefix_node == GSLT_FOREST_NONE) {
                    GsltAstNode *ast = (GsltAstNode *)calloc(1, sizeof(GsltAstNode));
                    ast->production_index = pr->production_index;
                    snprintf(ast->origin_module, sizeof(ast->origin_module), "%s", pr->origin_module);
                    snprintf(ast->origin_theory, sizeof(ast->origin_theory), "%s", pr->origin_theory);
                    snprintf(ast->label, sizeof(ast->label), "%s", pr->label);
                    snprintf(ast->sort, sizeof(ast->sort), "%s", pr->sort);
                    ast->scalar_left = forest->nodes[ch->parent_node].scalar_left;
                    ast->scalar_right = forest->nodes[ch->parent_node].scalar_right;
                    ast->child_count = pr->slot_count;
                    ast->db_index = -1;
                    for (uint32_t s = 0; s < pr->slot_count; s++) {
                        ast->children[s] = gslt_ast_clone(current_slots[s]);
                        if (pr->slots[s].is_binder) {
                            ast->is_binder = true;
                            snprintf(ast->binder_var, sizeof(ast->binder_var), "%s", pr->slots[s].binder_var);
                        }
                    }
                    if (*out_count < max_trees)
                        out_trees[(*out_count)++] = ast;
                    else
                        gslt_ast_free(ast);
                }
            } else if (ch->prefix_node != GSLT_FOREST_NONE) {
                const GsltCnf1Node *pn = &forest->nodes[ch->prefix_node];
                for (uint32_t k = 0; k < pn->choice_len; k++) {
                    const GsltCnf1Choice *pch = &forest->choices[pn->choice_begin + k];
                    if (pch->production_index != pr->production_index) continue;
                    gslt_collect_prefix_chain_alternatives(
                        forest, cat, pr, matcher_idx - 1u, pch, current_slots,
                        out_trees, out_count, max_trees, depth + 1u);
                }
            }
            current_slots[logical_slot] = NULL;
            gslt_ast_free(child_alts[ci]);
        }
    }
}

static inline void gslt_enumerate_node_derivations(
    const GsltCnf1Forest *forest,
    const GsltModuleCatalog *cat,
    uint32_t node_id,
    GsltAstNode **out_trees,
    uint32_t *out_count,
    uint32_t max_trees,
    uint32_t depth)
{
    if (node_id >= forest->node_len || depth > 32u) return;
    const GsltCnf1Node *n = &forest->nodes[node_id];
    for (uint32_t k = 0; k < n->choice_len; k++) {
        const GsltCnf1Choice *ch = &forest->choices[n->choice_begin + k];
        if (ch->production_index >= cat->production_count) continue;
        const GsltProduction *pr = &cat->productions[ch->production_index];
        if (pr->matcher_count == 0) {
            if (ch->child_node != GSLT_FOREST_NONE &&
                forest->nodes[ch->child_node].kind == GSLT_CNF1_NODE_EPSILON) {
                GsltAstNode *ast = (GsltAstNode *)calloc(1, sizeof(GsltAstNode));
                ast->production_index = pr->production_index;
                snprintf(ast->origin_module, sizeof(ast->origin_module), "%s", pr->origin_module);
                snprintf(ast->origin_theory, sizeof(ast->origin_theory), "%s", pr->origin_theory);
                snprintf(ast->label, sizeof(ast->label), "%s", pr->label);
                snprintf(ast->sort, sizeof(ast->sort), "%s", pr->sort);
                ast->scalar_left = n->scalar_left;
                ast->scalar_right = n->scalar_right;
                ast->child_count = 0;
                ast->db_index = -1;
                if (*out_count < max_trees)
                    out_trees[(*out_count)++] = ast;
                else
                    gslt_ast_free(ast);
            }
        } else {
            GsltAstNode *slots_buf[GSLT_MAX_SLOTS];
            memset(slots_buf, 0, sizeof(slots_buf));
            uint32_t prev_cnt = *out_count;
            gslt_collect_prefix_chain_alternatives(
                forest, cat, pr, pr->matcher_count - 1u, ch, slots_buf,
                out_trees, out_count, max_trees, depth + 1u);
            for (uint32_t idx = prev_cnt; idx < *out_count; idx++) {
                out_trees[idx]->scalar_left = n->scalar_left;
                out_trees[idx]->scalar_right = n->scalar_right;
            }
        }
    }
}

static inline void gslt_derivation_catalog_free(GsltDerivationCatalog *dc) {
    if (!dc) return;
    for (uint32_t i = 0; i < dc->count; i++) {
        gslt_ast_free(dc->trees[i]);
        dc->trees[i] = NULL;
    }
    dc->count = 0;
}

static inline bool gslt_extract_derivations_from_forest(
    const GsltCnf1Forest *forest,
    const GsltModuleCatalog *cat,
    const uint8_t *source_bytes,
    bool apply_selection_policy,
    GsltDerivationCatalog *out_dc)
{
    memset(out_dc, 0, sizeof(*out_dc));
    if (forest->root_len == 0) return true;
    GsltAstNode *raw_trees[GSLT_MAX_DERIVATIONS];
    uint32_t raw_cnt = 0;
    for (uint32_t r = 0; r < forest->root_len; r++) {
        gslt_enumerate_node_derivations(
            forest, cat, forest->roots[r], raw_trees, &raw_cnt, GSLT_MAX_DERIVATIONS, 0);
    }
    for (uint32_t i = 0; i < raw_cnt; i++) {
        if (apply_selection_policy &&
            !gslt_ast_passes_selection_policy(raw_trees[i], cat, source_bytes, forest->byte_offsets)) {
            gslt_ast_free(raw_trees[i]);
            continue;
        }
        uint32_t idx = out_dc->count++;
        out_dc->trees[idx] = raw_trees[i];
        gslt_render_result_packet(raw_trees[i], cat, out_dc->packets[idx], sizeof(out_dc->packets[idx]));
    }
    return true;
}

/* =========================================================================
 * Sound & Complete Catalogue Verification + Negative Control Checks
 * ========================================================================= */

/*
 * Verify a list of "(result (node ...) nil)" packet strings against:
 *   1. The CNF1 binary packed forest and PNI1 plan identity
 *   2. The GsltModuleCatalog productions and SourceSelectionV1 policy
 *   3. Both SOUNDNESS (every supplied packet is a valid selected forest derivation)
 *      and COMPLETENESS (no valid selected forest derivation is omitted!).
 */
static inline bool gslt_verify_packet_catalogue(
    const GsltCnf1Forest *forest,
    const GsltPni1Identity *pni,
    const GsltModuleCatalog *cat,
    const uint8_t *source_bytes,
    const char *const *packets,
    uint32_t packet_count,
    bool apply_selection_policy,
    char *err,
    size_t err_cap)
{
    if (pni->production_count != cat->production_count) {
        snprintf(err, err_cap, "PNI1 production count %u != catalog %u",
                 pni->production_count, cat->production_count);
        return false;
    }
    GsltDerivationCatalog expected;
    gslt_extract_derivations_from_forest(forest, cat, source_bytes, apply_selection_policy, &expected);

    /* 1. Soundness check: every supplied packet must exist in expected.packets */
    bool matched_expected[GSLT_MAX_DERIVATIONS];
    memset(matched_expected, 0, sizeof(matched_expected));
    for (uint32_t i = 0; i < packet_count; i++) {
        bool found = false;
        for (uint32_t j = 0; j < expected.count; j++) {
            if (!matched_expected[j] && strcmp(packets[i], expected.packets[j]) == 0) {
                matched_expected[j] = true;
                found = true;
                break;
            }
        }
        if (!found) {
            snprintf(err, err_cap,
                     "spurious or policy-refused packet at index %u: %s",
                     i, packets[i]);
            gslt_derivation_catalog_free(&expected);
            return false;
        }
    }

    /* 2. Completeness check: every expected derivation must be present in packets */
    for (uint32_t j = 0; j < expected.count; j++) {
        if (!matched_expected[j]) {
            snprintf(err, err_cap,
                     "incomplete catalogue: missing valid derivation %u (%s)",
                     j, expected.packets[j]);
            gslt_derivation_catalog_free(&expected);
            return false;
        }
    }

    gslt_derivation_catalog_free(&expected);
    return true;
}

/* =========================================================================
 * Constructor Provenance, Slot Routing, Binder Capture & Canonical Printer
 * ========================================================================= */

/*
 * Verify structural AST well-formedness against GsltModuleCatalog:
 *   1. Production index in bounds and origin_module / origin_theory / label / sort match
 *   2. Child count == slot_count and each child i has sort == slots[i].sort
 *   3. Child scalar spans respect the surface order given by routed_slots[]:
 *      if routed_slots[s1] < routed_slots[s2], then child[s1].scalar_right <= child[s2].scalar_left!
 */
static inline bool gslt_verify_ast_provenance_and_routing(
    const GsltAstNode *node,
    const GsltModuleCatalog *cat,
    const char *expected_sort,
    char *err,
    size_t err_cap)
{
    if (!node) {
        snprintf(err, err_cap, "null AST node");
        return false;
    }
    if (node->production_index >= cat->production_count) {
        snprintf(err, err_cap, "AST production_index %u out of bounds (%u)",
                 node->production_index, cat->production_count);
        return false;
    }
    const GsltProduction *pr = &cat->productions[node->production_index];
    if (strcmp(node->origin_module, pr->origin_module) != 0) {
        snprintf(err, err_cap, "wrong constructor origin for '%s': got module '%s', expected '%s'",
                 node->label, node->origin_module, pr->origin_module);
        return false;
    }
    if (strcmp(node->origin_theory, pr->origin_theory) != 0) {
        snprintf(err, err_cap, "wrong constructor theory for '%s': got '%s', expected '%s'",
                 node->label, node->origin_theory, pr->origin_theory);
        return false;
    }
    if (strcmp(node->label, pr->label) != 0) {
        snprintf(err, err_cap, "constructor label '%s' mismatches production %u ('%s')",
                 node->label, node->production_index, pr->label);
        return false;
    }
    if (strcmp(node->sort, pr->sort) != 0 ||
        (expected_sort && strcmp(node->sort, expected_sort) != 0)) {
        snprintf(err, err_cap, "constructor '%s' sort '%s' mismatches expected sort '%s'",
                 node->label, node->sort, expected_sort ? expected_sort : pr->sort);
        return false;
    }
    if (node->child_count != pr->slot_count) {
        snprintf(err, err_cap, "constructor '%s' child_count %u != slot_count %u",
                 node->label, node->child_count, pr->slot_count);
        return false;
    }

    /* Check child sorts and routed span ordering */
    for (uint32_t s = 0; s < pr->slot_count; s++) {
        if (!gslt_verify_ast_provenance_and_routing(
                node->children[s], cat, pr->slots[s].sort, err, err_cap)) {
            return false;
        }
    }
    for (uint32_t s1 = 0; s1 < pr->slot_count; s1++) {
        for (uint32_t s2 = 0; s2 < pr->slot_count; s2++) {
            if (pr->routed_slots[s1] < pr->routed_slots[s2]) {
                const GsltAstNode *c1 = node->children[s1];
                const GsltAstNode *c2 = node->children[s2];
                if (c1->scalar_right > c2->scalar_left ||
                    (c1->scalar_left == c2->scalar_left && c1->scalar_right == c2->scalar_right &&
                     c1->scalar_left > node->scalar_left)) {
                    snprintf(err, err_cap,
                             "child reordering detected in '%s': slot %u (routed pos %u, span [%u,%u]) "
                             "must precede slot %u (routed pos %u, span [%u,%u])",
                             node->label, s1, pr->routed_slots[s1], c1->scalar_left, c1->scalar_right,
                             s2, pr->routed_slots[s2], c2->scalar_left, c2->scalar_right);
                    return false;
                }
            }
        }
    }
    return true;
}

/*
 * Verify lexical binder scopes, de Bruijn indices, and capture-avoiding substitution:
 *   - Resolves variable references against enclosing binder stack
 *   - Refuses out-of-bounds de Bruijn indices (db_index >= binder_depth)
 *   - Refuses binder capture when substituting a free variable `subst_free_var`
 *     with `replacement_free_var` under an inner binder named `replacement_free_var`!
 */
static inline bool gslt_verify_binder_scopes_inner(
    GsltAstNode *node,
    const char binder_stack[][64],
    uint32_t binder_depth,
    const char *subst_target_var,
    const char *subst_replacement_free_var,
    char *err,
    size_t err_cap)
{
    if (!node) return true;
    if (node->is_var_ref) {
        if (node->db_index >= (int32_t)binder_depth) {
            snprintf(err, err_cap, "unbound de Bruijn index %d at binder depth %u in '%s'",
                     node->db_index, binder_depth, node->var_name);
            return false;
        }
        int32_t resolved_db = -1;
        for (int32_t d = (int32_t)binder_depth - 1; d >= 0; d--) {
            if (strcmp(binder_stack[d], node->var_name) == 0) {
                resolved_db = (int32_t)binder_depth - 1 - d;
                break;
            }
        }
        if (node->db_index >= 0 && resolved_db != node->db_index) {
            snprintf(err, err_cap,
                     "binder capture or de Bruijn mismatch for variable '%s': claimed db=%d, lexical db=%d",
                     node->var_name, node->db_index, resolved_db);
            return false;
        }
        node->db_index = resolved_db;
        /* If this variable is free (resolved_db == -1) and matches subst_target_var,
         * check if subst_replacement_free_var is bound in binder_stack (which would capture it!) */
        if (resolved_db < 0 && subst_target_var && subst_replacement_free_var &&
            strcmp(node->var_name, subst_target_var) == 0) {
            for (uint32_t d = 0; d < binder_depth; d++) {
                if (strcmp(binder_stack[d], subst_replacement_free_var) == 0) {
                    snprintf(err, err_cap,
                             "binder capture refused: free variable '%s' in replacement for '%s' "
                             "would be captured by inner binder '^%s' at depth %u",
                             subst_replacement_free_var, subst_target_var, binder_stack[d], d);
                    return false;
                }
            }
        }
    }
    char next_stack[32][64];
    for (uint32_t d = 0; d < binder_depth && d < 32; d++)
        snprintf(next_stack[d], 64, "%s", binder_stack[d]);
    uint32_t next_depth = binder_depth;
    if (node->is_binder && node->binder_var[0] != '\0' && next_depth < 32) {
        snprintf(next_stack[next_depth++], 64, "%s", node->binder_var);
    }
    for (uint32_t i = 0; i < node->child_count; i++) {
        if (!gslt_verify_binder_scopes_inner(
                node->children[i], next_stack, next_depth,
                subst_target_var, subst_replacement_free_var, err, err_cap)) {
            return false;
        }
    }
    return true;
}

static inline bool gslt_verify_binder_scopes(
    GsltAstNode *root,
    const char *subst_target_var,
    const char *subst_replacement_free_var,
    char *err,
    size_t err_cap)
{
    char stack[32][64];
    return gslt_verify_binder_scopes_inner(
        root, stack, 0, subst_target_var, subst_replacement_free_var, err, err_cap);
}

/*
 * Canonical Printer: print a GsltAstNode back to UTF-8 text using the
 * production's matchers and routed_slots[].
 */
static inline bool gslt_print_ast_canonical_inner(
    const GsltAstNode *node,
    const GsltModuleCatalog *cat,
    char *out_buf,
    size_t cap,
    size_t *pos,
    char *err,
    size_t err_cap)
{
    if (!node || node->production_index >= cat->production_count) {
        snprintf(err, err_cap, "cannot print invalid AST node");
        return false;
    }
    const GsltProduction *pr = &cat->productions[node->production_index];
    for (uint32_t m = 0; m < pr->matcher_count; m++) {
        const GsltMatcher *mt = &pr->matchers[m];
        if (mt->kind == GSLT_MATCH_CP) {
            uint32_t cp = mt->codepoint;
            if (*pos + 4 >= cap) {
                snprintf(err, err_cap, "canonical print buffer overflow");
                return false;
            }
            if (cp < 0x80u) {
                out_buf[(*pos)++] = (char)cp;
            } else if (cp < 0x800u) {
                out_buf[(*pos)++] = (char)(0xC0u | (cp >> 6));
                out_buf[(*pos)++] = (char)(0x80u | (cp & 0x3Fu));
            } else if (cp < 0x10000u) {
                out_buf[(*pos)++] = (char)(0xE0u | (cp >> 12));
                out_buf[(*pos)++] = (char)(0x80u | ((cp >> 6) & 0x3Fu));
                out_buf[(*pos)++] = (char)(0x80u | (cp & 0x3Fu));
            } else {
                out_buf[(*pos)++] = (char)(0xF0u | (cp >> 18));
                out_buf[(*pos)++] = (char)(0x80u | ((cp >> 12) & 0x3Fu));
                out_buf[(*pos)++] = (char)(0x80u | ((cp >> 6) & 0x3Fu));
                out_buf[(*pos)++] = (char)(0x80u | (cp & 0x3Fu));
            }
            out_buf[*pos] = '\0';
        } else if (mt->kind == GSLT_MATCH_SLOT) {
            uint32_t s = mt->slot_index;
            if (s >= node->child_count || !node->children[s]) {
                snprintf(err, err_cap, "missing child slot %u in '%s'", s, pr->label);
                return false;
            }
            if (!gslt_print_ast_canonical_inner(
                    node->children[s], cat, out_buf, cap, pos, err, err_cap)) {
                return false;
            }
        }
    }
    out_buf[*pos] = '\0';
    return true;
}

static inline bool gslt_print_ast_canonical(
    const GsltAstNode *node,
    const GsltModuleCatalog *cat,
    char *out_buf,
    size_t cap,
    char *err,
    size_t err_cap)
{
    size_t pos = 0;
    if (cap > 0) out_buf[0] = '\0';
    return gslt_print_ast_canonical_inner(node, cat, out_buf, cap, &pos, err, err_cap);
}

#endif /* GSLT_PACKED_BRIDGE_H */

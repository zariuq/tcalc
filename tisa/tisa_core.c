/*
 * tisa_core.c — Transform-Calculus-Native t-ISA Core:
 *   1. AST Arena & Builders
 *   2. Static Well-Formedness, Type, Liveness & Loop-Immutability Checker
 *   3. Overflow-Safe Capability & RW-Exclusivity Frame Validator
 *   4. Independent Structured Reference Evaluator (`tisa_eval_ref`)
 *   5. Real `tcalc`-Hosted Execution (`tisa_eval_tcalc`) firing actual
 *      `TAKE / KEEP / MAKE` transitions over `Cell(key, val)` occurrences
 *      (matching `Mettapedia/Machines/TIsa/Scalar.lean` and `Cells.lean`).
 */
#include "tisa.h"
#include <inttypes.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

/* =========================================================================
 * 1. AST Arena & Builders
 * ========================================================================= */

void tisa_arena_init(TcIsaArena *a, size_t initial_cap) {
    if (!a) return;
    if (initial_cap < 64u) initial_cap = 64u;
    a->stmts = (TcIsaStmt *)calloc(initial_cap, sizeof(TcIsaStmt));
    a->nstmts = 0;
    a->cap_stmts = a->stmts ? initial_cap : 0;
}

void tisa_arena_free(TcIsaArena *a) {
    if (!a) return;
    free(a->stmts);
    a->stmts = NULL;
    a->nstmts = 0;
    a->cap_stmts = 0;
}

static TcIsaStmt *tisa_arena_alloc(TcIsaArena *a) {
    if (!a || !a->stmts || a->nstmts >= a->cap_stmts) return NULL;
    TcIsaStmt *s = &a->stmts[a->nstmts++];
    memset(s, 0, sizeof(*s));
    return s;
}

TcIsaStmt *tisa_stmt_instr(TcIsaArena *a, TcIsaInstr ins) {
    TcIsaStmt *s = tisa_arena_alloc(a);
    if (!s) return NULL;
    s->kind = TISA_CTRL_INSTR;
    s->u.instr = ins;
    return s;
}

TcIsaStmt *tisa_stmt_seq(TcIsaArena *a, const TcIsaStmt *s1, const TcIsaStmt *s2) {
    if (!s1) return (TcIsaStmt *)s2;
    if (!s2) return (TcIsaStmt *)s1;
    TcIsaStmt *s = tisa_arena_alloc(a);
    if (!s) return NULL;
    s->kind = TISA_CTRL_SEQ;
    s->u.seq.first = s1;
    s->u.seq.second = s2;
    return s;
}

TcIsaStmt *tisa_stmt_if(TcIsaArena *a, uint8_t cond_reg, const TcIsaStmt *then_b, const TcIsaStmt *else_b) {
    TcIsaStmt *s = tisa_arena_alloc(a);
    if (!s) return NULL;
    s->kind = TISA_CTRL_IF;
    s->u.if_cond.cond_reg = cond_reg;
    s->u.if_cond.then_branch = then_b;
    s->u.if_cond.else_branch = else_b;
    return s;
}

TcIsaStmt *tisa_stmt_count_loop(TcIsaArena *a, uint8_t idx_reg, uint8_t bound_reg, uint32_t max_iters, const TcIsaStmt *body) {
    TcIsaStmt *s = tisa_arena_alloc(a);
    if (!s) return NULL;
    s->kind = TISA_CTRL_COUNT_LOOP;
    s->u.count_loop.idx_reg = idx_reg;
    s->u.count_loop.bound_reg = bound_reg;
    s->u.count_loop.max_iters = max_iters;
    s->u.count_loop.body = body;
    return s;
}

TcIsaStmt *tisa_stmt_early_exit_loop(TcIsaArena *a, uint8_t idx_reg, uint8_t bound_reg, uint8_t cont_reg, uint32_t max_iters, const TcIsaStmt *body) {
    TcIsaStmt *s = tisa_arena_alloc(a);
    if (!s) return NULL;
    s->kind = TISA_CTRL_EARLY_EXIT_LOOP;
    s->u.early_exit_loop.idx_reg = idx_reg;
    s->u.early_exit_loop.bound_reg = bound_reg;
    s->u.early_exit_loop.cont_reg = cont_reg;
    s->u.early_exit_loop.max_iters = max_iters;
    s->u.early_exit_loop.body = body;
    return s;
}

TcIsaStmt *tisa_stmt_return(TcIsaArena *a, TcIsaOutcome outcome, uint8_t ret_reg) {
    TcIsaStmt *s = tisa_arena_alloc(a);
    if (!s) return NULL;
    s->kind = TISA_CTRL_RETURN;
    s->u.ret.outcome = outcome;
    s->u.ret.ret_reg = ret_reg;
    return s;
}

/* =========================================================================
 * 2. Static Well-Formedness, Type, Liveness & Loop-Immutability Checker
 * ========================================================================= */

typedef struct {
    uint16_t     init_mask;
    TcIsaValType types[TISA_NUM_VREGS];
    uint8_t      ptr_region[TISA_NUM_VREGS];
    uint16_t     locked_loop_regs; /* Registers immutable inside active loop bodies */
} TcIsaTypeState;

static void tisa_set_err(char *err_buf, size_t err_cap, const char *fmt, ...) {
    if (!err_buf || err_cap == 0) return;
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(err_buf, err_cap, fmt, ap);
    va_end(ap);
}

static bool tisa_check_reg_init(const TcIsaTypeState *st, uint8_t r, char *err_buf, size_t err_cap) {
    if (r >= TISA_NUM_VREGS) {
        tisa_set_err(err_buf, err_cap, "register index %u out of logical v0..v11 range", (unsigned)r);
        return false;
    }
    if (!(st->init_mask & (1u << r)) || st->types[r] == TISA_TYPE_UNINIT) {
        tisa_set_err(err_buf, err_cap, "read of uninitialized register v%u", (unsigned)r);
        return false;
    }
    return true;
}

static bool tisa_check_reg_writable(const TcIsaTypeState *st, uint8_t r, char *err_buf, size_t err_cap) {
    if (r >= TISA_NUM_VREGS) {
        tisa_set_err(err_buf, err_cap, "destination register %u out of logical v0..v11 range", (unsigned)r);
        return false;
    }
    if (st->locked_loop_regs & (1u << r)) {
        tisa_set_err(err_buf, err_cap, "loop body attempts to overwrite locked loop controller/bound register v%u", (unsigned)r);
        return false;
    }
    return true;
}

static bool tisa_check_stmt_rec(const TcIsaProgram *prog,
                                const TcIsaStmt *stmt,
                                TcIsaTypeState *st,
                                TcIsaFootprint *fp,
                                char *err_buf, size_t err_cap) {
    if (!stmt) return true;
    switch (stmt->kind) {
        case TISA_CTRL_INSTR: {
            const TcIsaInstr *ins = &stmt->u.instr;
            uint16_t in_mask = 0;
            switch (ins->op) {
                case TISA_OP_IMM:
                    if (!tisa_check_reg_writable(st, ins->dst, err_buf, err_cap)) return false;
                    if (ins->ty == TISA_TYPE_BOOL && ins->imm64 > 1ull) {
                        tisa_set_err(err_buf, err_cap, "IMM BOOL value %" PRIu64 " outside {0,1}", ins->imm64);
                        return false;
                    }
                    if (ins->ty == TISA_TYPE_U32Z && ins->imm64 > 0xFFFFFFFFull) {
                        tisa_set_err(err_buf, err_cap, "IMM U32Z value exceeds 32 bits");
                        return false;
                    }
                    if (ins->ty == TISA_TYPE_PTR || ins->ty == TISA_TYPE_UNINIT) {
                        tisa_set_err(err_buf, err_cap, "IMM cannot forge a pointer or uninitialized type");
                        return false;
                    }
                    st->init_mask |= (uint16_t)(1u << ins->dst);
                    st->types[ins->dst] = ins->ty;
                    fp->write_reg_mask |= (uint16_t)(1u << ins->dst);
                    return true;

                case TISA_OP_MOV: {
                    if (!tisa_check_reg_init(st, ins->src1, err_buf, err_cap)) return false;
                    if (!tisa_check_reg_writable(st, ins->dst, err_buf, err_cap)) return false;
                    TcIsaValType dst_ty = (ins->ty != TISA_TYPE_UNINIT) ? ins->ty : st->types[ins->src1];
                    if (dst_ty == TISA_TYPE_BOOL && st->types[ins->src1] != TISA_TYPE_BOOL) {
                        tisa_set_err(err_buf, err_cap, "MOV BOOL requires BOOL source register v%u", (unsigned)ins->src1);
                        return false;
                    }
                    if (dst_ty == TISA_TYPE_PTR && st->types[ins->src1] != TISA_TYPE_PTR) {
                        tisa_set_err(err_buf, err_cap, "MOV PTR requires PTR source register v%u", (unsigned)ins->src1);
                        return false;
                    }
                    in_mask = (uint16_t)(1u << ins->src1);
                    fp->keep_reg_mask |= (uint16_t)(in_mask & ~(1u << ins->dst));
                    fp->write_reg_mask |= (uint16_t)(1u << ins->dst);
                    st->init_mask |= (uint16_t)(1u << ins->dst);
                    st->types[ins->dst] = dst_ty;
                    st->ptr_region[ins->dst] = (dst_ty == TISA_TYPE_PTR) ? st->ptr_region[ins->src1] : 0xFFu;
                    return true;
                }

                case TISA_OP_BIN:
                    if (!tisa_check_reg_init(st, ins->src1, err_buf, err_cap) ||
                        !tisa_check_reg_init(st, ins->src2, err_buf, err_cap)) return false;
                    if (!tisa_check_reg_writable(st, ins->dst, err_buf, err_cap)) return false;
                    if (ins->subop > TISA_BIN_MULLO) {
                        tisa_set_err(err_buf, err_cap, "invalid binary subop %u", (unsigned)ins->subop);
                        return false;
                    }
                    if (ins->ty == TISA_TYPE_BOOL) {
                        if ((ins->subop != TISA_BIN_AND && ins->subop != TISA_BIN_OR && ins->subop != TISA_BIN_XOR) ||
                            st->types[ins->src1] != TISA_TYPE_BOOL || st->types[ins->src2] != TISA_TYPE_BOOL) {
                            tisa_set_err(err_buf, err_cap, "BIN BOOL requires AND/OR/XOR on two BOOL registers");
                            return false;
                        }
                    } else if (ins->ty != TISA_TYPE_U64 && ins->ty != TISA_TYPE_U32Z && ins->ty != TISA_TYPE_I32S) {
                        tisa_set_err(err_buf, err_cap, "BIN requires U64/U32Z/I32S/BOOL result type");
                        return false;
                    }
                    in_mask = (uint16_t)((1u << ins->src1) | (1u << ins->src2));
                    fp->keep_reg_mask |= (uint16_t)(in_mask & ~(1u << ins->dst));
                    fp->write_reg_mask |= (uint16_t)(1u << ins->dst);
                    if (ins->dst == ins->src2 && ins->dst != ins->src1 &&
                        (ins->subop == TISA_BIN_SUB)) {
                        fp->scratch_reg_mask |= (uint16_t)(1u << 0); /* s0 (r14) used for non-commutative alias */
                    }
                    st->init_mask |= (uint16_t)(1u << ins->dst);
                    st->types[ins->dst] = ins->ty;
                    return true;

                case TISA_OP_SHIFT:
                    if (!tisa_check_reg_init(st, ins->src1, err_buf, err_cap)) return false;
                    if (!tisa_check_reg_writable(st, ins->dst, err_buf, err_cap)) return false;
                    if (ins->ty == TISA_TYPE_BOOL || ins->ty == TISA_TYPE_PTR || ins->ty == TISA_TYPE_UNINIT) {
                        tisa_set_err(err_buf, err_cap, "SHIFT requires U64/U32Z/I32S result type");
                        return false;
                    }
                    if (ins->subop > TISA_SHIFT_SHRS || ins->bit_width >= 64u) {
                        tisa_set_err(err_buf, err_cap, "invalid shift subop %u or shift amount %u >= 64",
                                     (unsigned)ins->subop, (unsigned)ins->bit_width);
                        return false;
                    }
                    if ((ins->ty == TISA_TYPE_U32Z || ins->ty == TISA_TYPE_I32S) && ins->bit_width >= 32u) {
                        tisa_set_err(err_buf, err_cap, "32-bit shift amount %u >= 32", (unsigned)ins->bit_width);
                        return false;
                    }
                    in_mask = (uint16_t)(1u << ins->src1);
                    fp->keep_reg_mask |= (uint16_t)(in_mask & ~(1u << ins->dst));
                    fp->write_reg_mask |= (uint16_t)(1u << ins->dst);
                    st->init_mask |= (uint16_t)(1u << ins->dst);
                    st->types[ins->dst] = ins->ty;
                    return true;

                case TISA_OP_EXTRACT:
                    if (!tisa_check_reg_init(st, ins->src1, err_buf, err_cap)) return false;
                    if (!tisa_check_reg_writable(st, ins->dst, err_buf, err_cap)) return false;
                    if (ins->ty == TISA_TYPE_BOOL || ins->ty == TISA_TYPE_PTR || ins->ty == TISA_TYPE_UNINIT) {
                        tisa_set_err(err_buf, err_cap, "EXTRACT requires U64/U32Z/I32S result type");
                        return false;
                    }
                    if (ins->bit_width == 0u || (uint32_t)ins->scale_lg2 + (uint32_t)ins->bit_width > 64u) {
                        tisa_set_err(err_buf, err_cap, "invalid extract lsb=%u width=%u",
                                     (unsigned)ins->scale_lg2, (unsigned)ins->bit_width);
                        return false;
                    }
                    in_mask = (uint16_t)(1u << ins->src1);
                    fp->keep_reg_mask |= (uint16_t)(in_mask & ~(1u << ins->dst));
                    fp->write_reg_mask |= (uint16_t)(1u << ins->dst);
                    st->init_mask |= (uint16_t)(1u << ins->dst);
                    st->types[ins->dst] = ins->ty;
                    return true;

                case TISA_OP_ADDR:
                    if (!tisa_check_reg_init(st, ins->src1, err_buf, err_cap)) return false;
                    if (ins->src2 != 0xFFu && !tisa_check_reg_init(st, ins->src2, err_buf, err_cap)) return false;
                    if (!tisa_check_reg_writable(st, ins->dst, err_buf, err_cap)) return false;
                    if (ins->scale_lg2 > 3u || ins->region_id >= prog->nregions) {
                        tisa_set_err(err_buf, err_cap, "invalid ADDR scale_lg2=%u or region=%u",
                                     (unsigned)ins->scale_lg2, (unsigned)ins->region_id);
                        return false;
                    }
                    if (st->types[ins->src1] != TISA_TYPE_PTR || st->ptr_region[ins->src1] != ins->region_id) {
                        tisa_set_err(err_buf, err_cap, "ADDR base v%u is not Ptr(%u)",
                                     (unsigned)ins->src1, (unsigned)ins->region_id);
                        return false;
                    }
                    in_mask = (uint16_t)(1u << ins->src1);
                    if (ins->src2 != 0xFFu) in_mask |= (uint16_t)(1u << ins->src2);
                    fp->keep_reg_mask |= (uint16_t)(in_mask & ~(1u << ins->dst));
                    fp->write_reg_mask |= (uint16_t)(1u << ins->dst);
                    fp->keep_region_mask |= (uint16_t)(1u << ins->region_id);
                    st->init_mask |= (uint16_t)(1u << ins->dst);
                    st->types[ins->dst] = TISA_TYPE_PTR;
                    st->ptr_region[ins->dst] = ins->region_id;
                    return true;

                case TISA_OP_LOAD:
                    if (!tisa_check_reg_init(st, ins->src1, err_buf, err_cap)) return false;
                    if (!tisa_check_reg_writable(st, ins->dst, err_buf, err_cap)) return false;
                    if (ins->region_id == TISA_REGION_FRAME) {
                        if (ins->src1 != TISA_V0 || ins->subop != TISA_MEM_U64 ||
                            ins->disp32 < 0 || (ins->disp32 % 8) != 0 ||
                            (size_t)ins->disp32 + 8u > sizeof(TcIsaRuntimeFrame)) {
                            tisa_set_err(err_buf, err_cap, "invalid frame LOAD disp=%d width=%u",
                                         (int)ins->disp32, (unsigned)ins->subop);
                            return false;
                        }
                        in_mask = (uint16_t)(1u << ins->src1);
                        fp->keep_reg_mask |= (uint16_t)(in_mask & ~(1u << ins->dst));
                        fp->write_reg_mask |= (uint16_t)(1u << ins->dst);
                        st->init_mask |= (uint16_t)(1u << ins->dst);
                        st->types[ins->dst] = ins->ty;
                        if (ins->ty == TISA_TYPE_PTR) {
                            uint8_t rid = (uint8_t)(ins->disp32 / 16);
                            if (ins->disp32 >= 144 || (ins->disp32 % 16) != 0 ||
                                rid >= prog->nregions || prog->regions[rid].mode == TISA_CAP_NONE) {
                                tisa_set_err(err_buf, err_cap, "frame pointer LOAD disp=%d does not name a valid region",
                                             (int)ins->disp32);
                                return false;
                            }
                            st->ptr_region[ins->dst] = rid;
                        }
                        return true;
                    }
                    if (ins->region_id >= prog->nregions ||
                        prog->regions[ins->region_id].mode == TISA_CAP_NONE) {
                        tisa_set_err(err_buf, err_cap, "LOAD from undeclared region %u", (unsigned)ins->region_id);
                        return false;
                    }
                    if (st->types[ins->src1] != TISA_TYPE_PTR || st->ptr_region[ins->src1] != ins->region_id) {
                        tisa_set_err(err_buf, err_cap, "LOAD base v%u is not Ptr(%u)",
                                     (unsigned)ins->src1, (unsigned)ins->region_id);
                        return false;
                    }
                    if (ins->subop != TISA_MEM_U8 && ins->subop != TISA_MEM_U32 && ins->subop != TISA_MEM_U64) {
                        tisa_set_err(err_buf, err_cap, "LOAD invalid byte width %u", (unsigned)ins->subop);
                        return false;
                    }
                    if (ins->ty == TISA_TYPE_PTR || ins->ty == TISA_TYPE_UNINIT) {
                        tisa_set_err(err_buf, err_cap, "user-region LOAD cannot forge a PTR or UNINIT type");
                        return false;
                    }
                    in_mask = (uint16_t)(1u << ins->src1);
                    fp->keep_reg_mask |= (uint16_t)(in_mask & ~(1u << ins->dst));
                    fp->write_reg_mask |= (uint16_t)(1u << ins->dst);
                    fp->keep_region_mask |= (uint16_t)(1u << ins->region_id);
                    st->init_mask |= (uint16_t)(1u << ins->dst);
                    st->types[ins->dst] = ins->ty;
                    st->ptr_region[ins->dst] = 0xFFu;
                    return true;

                case TISA_OP_STORE:
                    if (!tisa_check_reg_init(st, ins->src1, err_buf, err_cap) ||
                        !tisa_check_reg_init(st, ins->src2, err_buf, err_cap)) return false;
                    if (ins->region_id >= prog->nregions ||
                        prog->regions[ins->region_id].mode != TISA_CAP_RW) {
                        tisa_set_err(err_buf, err_cap, "STORE to non-writable region %u refused", (unsigned)ins->region_id);
                        return false;
                    }
                    if (st->types[ins->src1] != TISA_TYPE_PTR || st->ptr_region[ins->src1] != ins->region_id) {
                        tisa_set_err(err_buf, err_cap, "STORE base v%u is not Ptr(%u)",
                                     (unsigned)ins->src1, (unsigned)ins->region_id);
                        return false;
                    }
                    if (ins->subop != TISA_MEM_U8 && ins->subop != TISA_MEM_U32 && ins->subop != TISA_MEM_U64) {
                        tisa_set_err(err_buf, err_cap, "STORE invalid byte width %u", (unsigned)ins->subop);
                        return false;
                    }
                    fp->keep_reg_mask |= (uint16_t)((1u << ins->src1) | (1u << ins->src2));
                    fp->keep_region_mask |= (uint16_t)(1u << ins->region_id);
                    fp->write_region_mask |= (uint16_t)(1u << ins->region_id);
                    return true;

                case TISA_OP_CMP:
                    if (!tisa_check_reg_init(st, ins->src1, err_buf, err_cap)) return false;
                    if (ins->bit_width == 0u && !tisa_check_reg_init(st, ins->src2, err_buf, err_cap)) return false;
                    if (!tisa_check_reg_writable(st, ins->dst, err_buf, err_cap)) return false;
                    if (ins->subop > TISA_CMP_SLE) {
                        tisa_set_err(err_buf, err_cap, "invalid CMP condition %u", (unsigned)ins->subop);
                        return false;
                    }
                    in_mask = (uint16_t)(1u << ins->src1);
                    if (ins->bit_width == 0u) in_mask |= (uint16_t)(1u << ins->src2);
                    fp->keep_reg_mask |= (uint16_t)(in_mask & ~(1u << ins->dst));
                    fp->write_reg_mask |= (uint16_t)(1u << ins->dst);
                    if (ins->bit_width != 0u && (ins->imm64 > 0x7FFFFFFFull && ins->imm64 < 0xFFFFFFFF80000000ull)) {
                        fp->scratch_reg_mask |= (uint16_t)(1u << 0); /* s0 (r14) used for 64-bit imm compare */
                    }
                    st->init_mask |= (uint16_t)(1u << ins->dst);
                    st->types[ins->dst] = TISA_TYPE_BOOL;
                    return true;

                case TISA_OP_SELECT:
                    if (!tisa_check_reg_init(st, ins->src3, err_buf, err_cap) ||
                        !tisa_check_reg_init(st, ins->src1, err_buf, err_cap) ||
                        !tisa_check_reg_init(st, ins->src2, err_buf, err_cap)) return false;
                    if (!tisa_check_reg_writable(st, ins->dst, err_buf, err_cap)) return false;
                    if (ins->ty == TISA_TYPE_UNINIT) {
                        tisa_set_err(err_buf, err_cap, "SELECT result type cannot be UNINIT");
                        return false;
                    }
                    if (st->types[ins->src3] != TISA_TYPE_BOOL) {
                        tisa_set_err(err_buf, err_cap, "SELECT condition register v%u does not have BOOL type",
                                     (unsigned)ins->src3);
                        return false;
                    }
                    if (ins->ty == TISA_TYPE_BOOL &&
                        (st->types[ins->src1] != TISA_TYPE_BOOL || st->types[ins->src2] != TISA_TYPE_BOOL)) {
                        tisa_set_err(err_buf, err_cap, "SELECT BOOL requires BOOL true/false operands");
                        return false;
                    }
                    if (ins->ty == TISA_TYPE_PTR &&
                        (st->types[ins->src1] != TISA_TYPE_PTR || st->types[ins->src2] != TISA_TYPE_PTR ||
                         st->ptr_region[ins->src1] != st->ptr_region[ins->src2])) {
                        tisa_set_err(err_buf, err_cap, "SELECT PTR requires two PTR operands in the same region");
                        return false;
                    }
                    in_mask = (uint16_t)((1u << ins->src1) | (1u << ins->src2) | (1u << ins->src3));
                    fp->keep_reg_mask |= (uint16_t)(in_mask & ~(1u << ins->dst));
                    fp->write_reg_mask |= (uint16_t)(1u << ins->dst);
                    if (ins->dst == ins->src2 && ins->dst != ins->src1) {
                        fp->scratch_reg_mask |= (uint16_t)(1u << 0);
                    }
                    st->init_mask |= (uint16_t)(1u << ins->dst);
                    st->types[ins->dst] = ins->ty;
                    st->ptr_region[ins->dst] = (ins->ty == TISA_TYPE_PTR) ? st->ptr_region[ins->src1] : 0xFFu;
                    return true;

                default:
                    tisa_set_err(err_buf, err_cap, "unknown opcode %d", (int)ins->op);
                    return false;
            }
        }

        case TISA_CTRL_SEQ:
            if (!tisa_check_stmt_rec(prog, stmt->u.seq.first, st, fp, err_buf, err_cap)) return false;
            return tisa_check_stmt_rec(prog, stmt->u.seq.second, st, fp, err_buf, err_cap);

        case TISA_CTRL_IF: {
            uint8_t cr = stmt->u.if_cond.cond_reg;
            if (!tisa_check_reg_init(st, cr, err_buf, err_cap)) return false;
            if (st->types[cr] != TISA_TYPE_BOOL) {
                tisa_set_err(err_buf, err_cap, "IF condition register v%u must have BOOL type", (unsigned)cr);
                return false;
            }
            fp->keep_reg_mask |= (uint16_t)(1u << cr);
            TcIsaTypeState st_then = *st;
            TcIsaTypeState st_else = *st;
            TcIsaFootprint fp_then = *fp, fp_else = *fp;
            fp_then.has_return = false;
            fp_else.has_return = false;
            if (!tisa_check_stmt_rec(prog, stmt->u.if_cond.then_branch, &st_then, &fp_then, err_buf, err_cap)) return false;
            if (!tisa_check_stmt_rec(prog, stmt->u.if_cond.else_branch, &st_else, &fp_else, err_buf, err_cap)) return false;
            fp->keep_reg_mask = fp_then.keep_reg_mask | fp_else.keep_reg_mask;
            fp->write_reg_mask = fp_then.write_reg_mask | fp_else.write_reg_mask;
            fp->scratch_reg_mask = fp_then.scratch_reg_mask | fp_else.scratch_reg_mask;
            fp->keep_region_mask = fp_then.keep_region_mask | fp_else.keep_region_mask;
            fp->write_region_mask = fp_then.write_region_mask | fp_else.write_region_mask;
            if (fp_then.max_loop_bound + fp_else.max_loop_bound > fp->max_loop_bound) {
                fp->max_loop_bound = fp_then.max_loop_bound + fp_else.max_loop_bound;
            }
            if (fp_then.has_return && fp_else.has_return) {
                fp->has_return = true;
            } else if (fp_then.has_return && !fp_else.has_return) {
                *st = st_else;
            } else if (!fp_then.has_return && fp_else.has_return) {
                *st = st_then;
            } else {
                uint16_t common = (uint16_t)(st_then.init_mask & st_else.init_mask);
                uint16_t agreed = 0;
                for (int r = 0; r < TISA_NUM_VREGS; r++) {
                    if (common & (1u << r)) {
                        if (st_then.types[r] == st_else.types[r] &&
                            (st_then.types[r] != TISA_TYPE_PTR || st_then.ptr_region[r] == st_else.ptr_region[r])) {
                            agreed |= (uint16_t)(1u << r);
                            st->types[r] = st_then.types[r];
                            st->ptr_region[r] = st_then.ptr_region[r];
                        } else {
                            st->types[r] = TISA_TYPE_UNINIT;
                        }
                    } else {
                        st->types[r] = TISA_TYPE_UNINIT;
                    }
                }
                st->init_mask = agreed;
            }
            return true;
        }

        case TISA_CTRL_COUNT_LOOP: {
            uint8_t ir = stmt->u.count_loop.idx_reg;
            uint8_t br = stmt->u.count_loop.bound_reg;
            if (!tisa_check_reg_init(st, br, err_buf, err_cap)) return false;
            if (!tisa_check_reg_writable(st, ir, err_buf, err_cap)) return false;
            if (ir == br) {
                tisa_set_err(err_buf, err_cap, "COUNT_LOOP idx_reg and bound_reg cannot alias (v%u)", (unsigned)ir);
                return false;
            }
            if (stmt->u.count_loop.max_iters == 0u) {
                tisa_set_err(err_buf, err_cap, "COUNT_LOOP max_iters must be >= 1");
                return false;
            }
            fp->keep_reg_mask |= (uint16_t)(1u << br);
            fp->write_reg_mask |= (uint16_t)(1u << ir);
            fp->max_loop_bound += stmt->u.count_loop.max_iters;
            st->init_mask |= (uint16_t)(1u << ir);
            st->types[ir] = TISA_TYPE_U64;

            TcIsaTypeState st_body = *st;
            st_body.locked_loop_regs |= (uint16_t)((1u << ir) | (1u << br));
            bool prev_ret = fp->has_return;
            if (!tisa_check_stmt_rec(prog, stmt->u.count_loop.body, &st_body, fp, err_buf, err_cap)) {
                return false;
            }
            fp->has_return = prev_ret;
            return true;
        }

        case TISA_CTRL_EARLY_EXIT_LOOP: {
            uint8_t ir = stmt->u.early_exit_loop.idx_reg;
            uint8_t br = stmt->u.early_exit_loop.bound_reg;
            uint8_t cr = stmt->u.early_exit_loop.cont_reg;
            if (!tisa_check_reg_init(st, br, err_buf, err_cap) ||
                !tisa_check_reg_init(st, cr, err_buf, err_cap)) return false;
            if (st->types[cr] != TISA_TYPE_BOOL) {
                tisa_set_err(err_buf, err_buf ? err_cap : 0, "EARLY_EXIT_LOOP cont_reg v%u must have BOOL type", (unsigned)cr);
                return false;
            }
            if (!tisa_check_reg_writable(st, ir, err_buf, err_cap)) return false;
            if (ir == br || ir == cr || br == cr) {
                tisa_set_err(err_buf, err_cap, "EARLY_EXIT_LOOP idx/bound/cont registers must be distinct");
                return false;
            }
            if (stmt->u.early_exit_loop.max_iters == 0u) {
                tisa_set_err(err_buf, err_cap, "EARLY_EXIT_LOOP max_iters must be >= 1");
                return false;
            }
            fp->keep_reg_mask |= (uint16_t)((1u << br) | (1u << cr));
            fp->write_reg_mask |= (uint16_t)(1u << ir);
            fp->max_loop_bound += stmt->u.early_exit_loop.max_iters;
            st->init_mask |= (uint16_t)(1u << ir);
            st->types[ir] = TISA_TYPE_U64;

            TcIsaTypeState st_body = *st;
            st_body.locked_loop_regs |= (uint16_t)((1u << ir) | (1u << br));
            bool prev_ret = fp->has_return;
            if (!tisa_check_stmt_rec(prog, stmt->u.early_exit_loop.body, &st_body, fp, err_buf, err_cap)) {
                return false;
            }
            fp->has_return = prev_ret;
            return true;
        }

        case TISA_CTRL_RETURN: {
            uint8_t rr = stmt->u.ret.ret_reg;
            if (!tisa_check_reg_init(st, rr, err_buf, err_cap)) return false;
            fp->keep_reg_mask |= (uint16_t)(1u << rr);
            fp->has_return = true;
            return true;
        }

        case TISA_CTRL_FUND:
            tisa_set_err(err_buf, err_cap, "FUND belongs to t-ISA profile p1 (tisa_ref.c)");
            return false;

        default:
            tisa_set_err(err_buf, err_cap, "unknown control kind %d", (int)stmt->kind);
            return false;
    }
}

bool tisa_check_program(TcIsaProgram *prog, char *err_buf, size_t err_cap) {
    if (!prog || !prog->root) {
        tisa_set_err(err_buf, err_cap, "null program or root statement");
        return false;
    }
    if (prog->nregions > TISA_MAX_REGIONS) {
        tisa_set_err(err_buf, err_cap, "nregions %u exceeds TISA_MAX_REGIONS (%u)",
                     (unsigned)prog->nregions, TISA_MAX_REGIONS);
        return false;
    }
    /* Public ABI entry signature supplies only v0..v5 (rdi, rsi, rdx, rcx, r8, r9).
     * Registers v6..v11 must be initialized by program instructions before reading. */
    if (prog->init_reg_mask & ~0x003Fu) {
        tisa_set_err(err_buf, err_cap, "init_reg_mask 0x%04x references non-entry registers outside v0..v5",
                     (unsigned)prog->init_reg_mask);
        return false;
    }
    TcIsaTypeState st;
    memset(&st, 0, sizeof(st));
    st.init_mask = prog->init_reg_mask;
    st.locked_loop_regs = (1u << TISA_V0); /* v0 (frame pointer) is immutable */
    for (int r = 0; r < TISA_NUM_VREGS; r++) {
        if (st.init_mask & (1u << r)) {
            st.types[r] = prog->init_reg_types[r];
            st.ptr_region[r] = prog->init_reg_region[r];
        }
    }
    TcIsaFootprint fp;
    memset(&fp, 0, sizeof(fp));
    if (!tisa_check_stmt_rec(prog, prog->root, &st, &fp, err_buf, err_cap)) {
        return false;
    }
    if (!fp.has_return) {
        tisa_set_err(err_buf, err_cap, "program control flow does not end with an explicit RETURN");
        return false;
    }
    /* Set false before native emission; tisa_compile_x86 sets true only after
     * validating emitted body spans, register operands, scratch mask, and fixups. */
    fp.no_spill_verified = false;
    prog->footprint = fp;
    return true;
}

/* =========================================================================
 * 3. Overflow-Safe Capability & RW-Exclusivity Frame Validator
 * ========================================================================= */

TcIsaOutcome tisa_validate_frame(const TcIsaProgram *prog,
                                 const TcIsaRuntimeFrame *frame,
                                 const uint64_t init_regs[TISA_NUM_VREGS],
                                 char *err_buf, size_t err_cap) {
    if (!prog || !frame) {
        tisa_set_err(err_buf, err_cap, "null program or runtime frame");
        return TISA_OUTCOME_INVALID_INPUT;
    }
    const uint64_t *raw_slices = &frame->s0_ptr;
    uint64_t base[TISA_MAX_REGIONS] = {0};
    uint64_t len[TISA_MAX_REGIONS]  = {0};

    for (uint8_t r = 0; r < prog->nregions; r++) {
        TcIsaCapMode mode = prog->regions[r].mode;
        if (mode == TISA_CAP_NONE) continue;
        base[r] = raw_slices[r * 2u];
        len[r]  = raw_slices[r * 2u + 1u];
        if (len[r] < prog->regions[r].min_byte_len) {
            tisa_set_err(err_buf, err_cap, "region %u (%s) byte length %" PRIu64 " < min_byte_len %u",
                         (unsigned)r, prog->regions[r].name ? prog->regions[r].name : "?",
                         len[r], prog->regions[r].min_byte_len);
            return TISA_OUTCOME_INVALID_INPUT;
        }
        if (len[r] > 0 && base[r] == 0) {
            tisa_set_err(err_buf, err_cap, "region %u has non-zero length %" PRIu64 " with NULL base pointer",
                         (unsigned)r, len[r]);
            return TISA_OUTCOME_INVALID_INPUT;
        }
        /* Overflow-safe bound check: base + len must not wrap around 2^64 */
        if (base[r] > UINT64_MAX - len[r]) {
            tisa_set_err(err_buf, err_cap, "region %u base 0x%" PRIx64 " + len %" PRIu64 " overflows 64-bit address space",
                         (unsigned)r, base[r], len[r]);
            return TISA_OUTCOME_INVALID_INPUT;
        }
        uint32_t align = prog->regions[r].align_bytes;
        if (align > 1u && (base[r] % (uint64_t)align) != 0ull) {
            tisa_set_err(err_buf, err_cap, "region %u base 0x%" PRIx64 " is not %u-byte aligned",
                         (unsigned)r, base[r], align);
            return TISA_OUTCOME_INVALID_INPUT;
        }
    }

    /* Writable ranges must have exclusive ownership (disjoint from all other live ranges) */
    for (uint8_t r1 = 0; r1 < prog->nregions; r1++) {
        if (prog->regions[r1].mode == TISA_CAP_NONE || len[r1] == 0) continue;
        for (uint8_t r2 = (uint8_t)(r1 + 1u); r2 < prog->nregions; r2++) {
            if (prog->regions[r2].mode == TISA_CAP_NONE || len[r2] == 0) continue;
            if (prog->regions[r1].mode == TISA_CAP_RW || prog->regions[r2].mode == TISA_CAP_RW) {
                uint64_t end1 = base[r1] + len[r1];
                uint64_t end2 = base[r2] + len[r2];
                if (!(end1 <= base[r2] || end2 <= base[r1])) {
                    tisa_set_err(err_buf, err_cap,
                                 "writable capability overlap between region %u [0x%" PRIx64 ", 0x%" PRIx64 ") and region %u [0x%" PRIx64 ", 0x%" PRIx64 ")",
                                 (unsigned)r1, base[r1], end1, (unsigned)r2, base[r2], end2);
                    return TISA_OUTCOME_INVALID_INPUT;
                }
            }
        }
    }

    /* Frame descriptor self-alias protection:
     *   - User RW regions cannot overlap any part of TcIsaRuntimeFrame [frame_base, frame_end).
     *   - User RO regions cannot overlap engine-written frame fields [frame_mut_base, frame_end)
     *     (status, ret_val, fuel_used). */
    uint64_t frame_base     = (uint64_t)(uintptr_t)frame;
    uint64_t frame_end      = frame_base + (uint64_t)sizeof(TcIsaRuntimeFrame);
    uint64_t frame_mut_base = frame_base + (uint64_t)offsetof(TcIsaRuntimeFrame, status);
    for (uint8_t r = 0; r < prog->nregions; r++) {
        TcIsaCapMode mode = prog->regions[r].mode;
        if (mode == TISA_CAP_NONE || len[r] == 0) continue;
        uint64_t end_r = base[r] + len[r];
        if (mode == TISA_CAP_RW) {
            if (!(end_r <= frame_base || frame_end <= base[r])) {
                tisa_set_err(err_buf, err_cap,
                             "writable region %u [0x%" PRIx64 ", 0x%" PRIx64 ") overlaps TcIsaRuntimeFrame [0x%" PRIx64 ", 0x%" PRIx64 ")",
                             (unsigned)r, base[r], end_r, frame_base, frame_end);
                return TISA_OUTCOME_INVALID_INPUT;
            }
        } else if (mode == TISA_CAP_RO) {
            if (!(end_r <= frame_mut_base || frame_end <= base[r])) {
                tisa_set_err(err_buf, err_cap,
                             "read-only region %u [0x%" PRIx64 ", 0x%" PRIx64 ") overlaps mutable TcIsaRuntimeFrame fields [0x%" PRIx64 ", 0x%" PRIx64 ")",
                             (unsigned)r, base[r], end_r, frame_mut_base, frame_end);
                return TISA_OUTCOME_INVALID_INPUT;
            }
        }
    }

    if (init_regs) {
        if ((prog->init_reg_mask & (1u << TISA_V0)) && init_regs[TISA_V0] != frame_base) {
            tisa_set_err(err_buf, err_cap, "initial v0 (0x%" PRIx64 ") does not match TcIsaRuntimeFrame pointer (0x%" PRIx64 ")",
                         init_regs[TISA_V0], frame_base);
            return TISA_OUTCOME_INVALID_INPUT;
        }
        for (int reg = 0; reg < TISA_NUM_VREGS; reg++) {
            if (!(prog->init_reg_mask & (1u << reg))) continue;
            TcIsaValType ty = prog->init_reg_types[reg];
            uint64_t v = init_regs[reg];
            if (ty == TISA_TYPE_BOOL && v > 1ull) {
                tisa_set_err(err_buf, err_cap, "initial register v%d has invalid BOOL value %" PRIu64, reg, v);
                return TISA_OUTCOME_INVALID_INPUT;
            }
            if (ty == TISA_TYPE_U32Z && v > 0xFFFFFFFFull) {
                tisa_set_err(err_buf, err_cap, "initial register v%d has non-canonical U32Z value 0x%" PRIx64, reg, v);
                return TISA_OUTCOME_INVALID_INPUT;
            }
            if (ty == TISA_TYPE_I32S && (uint64_t)(int64_t)(int32_t)(uint32_t)v != v) {
                tisa_set_err(err_buf, err_cap, "initial register v%d has non-canonical I32S value 0x%" PRIx64, reg, v);
                return TISA_OUTCOME_INVALID_INPUT;
            }
            if (ty == TISA_TYPE_PTR) {
                uint8_t rid = prog->init_reg_region[reg];
                if (rid >= prog->nregions || v < base[rid] || (v - base[rid]) > len[rid]) {
                    tisa_set_err(err_buf, err_cap, "initial pointer register v%d outside region %u bounds", reg, (unsigned)rid);
                    return TISA_OUTCOME_INVALID_INPUT;
                }
            }
        }
    }

    return TISA_OUTCOME_FIRED;
}

/* =========================================================================
 * 4. Pure Scalar Algebra (`tisa_scalar_eval`) & Memory Bounds Helper
 * ========================================================================= */

static inline uint64_t tisa_norm_type(TcIsaValType ty, uint64_t raw) {
    switch (ty) {
        case TISA_TYPE_U32Z: return (uint64_t)(uint32_t)raw;
        case TISA_TYPE_I32S: return (uint64_t)(int64_t)(int32_t)(uint32_t)raw;
        case TISA_TYPE_BOOL: return raw & 1ull;
        default:             return raw;
    }
}

bool tisa_scalar_eval(const TcIsaInstr *ins,
                      const uint64_t regs[TISA_NUM_VREGS],
                      uint64_t *out_val) {
    if (!ins || !regs || !out_val) return false;
    switch (ins->op) {
        case TISA_OP_IMM:
            if (ins->ty == TISA_TYPE_BOOL && ins->imm64 > 1ull) return false;
            *out_val = tisa_norm_type(ins->ty, ins->imm64);
            return true;

        case TISA_OP_MOV:
            if (ins->ty == TISA_TYPE_BOOL && regs[ins->src1] > 1ull) return false;
            *out_val = tisa_norm_type(ins->ty, regs[ins->src1]);
            return true;

        case TISA_OP_BIN: {
            uint64_t a = regs[ins->src1];
            uint64_t b = regs[ins->src2];
            if (ins->ty == TISA_TYPE_BOOL && (a > 1ull || b > 1ull)) return false;
            uint64_t r = 0;
            switch (ins->subop) {
                case TISA_BIN_ADD:   r = a + b; break;
                case TISA_BIN_SUB:   r = a - b; break;
                case TISA_BIN_AND:   r = a & b; break;
                case TISA_BIN_OR:    r = a | b; break;
                case TISA_BIN_XOR:   r = a ^ b; break;
                case TISA_BIN_MULLO: r = a * b; break;
                default: return false;
            }
            *out_val = tisa_norm_type(ins->ty, r);
            return true;
        }

        case TISA_OP_SHIFT: {
            uint8_t sh = ins->bit_width;
            if (sh >= 64u) return false;
            if (ins->ty == TISA_TYPE_U32Z) {
                if (sh >= 32u) return false;
                uint32_t a32 = (uint32_t)regs[ins->src1];
                uint32_t r32 = 0;
                if (ins->subop == TISA_SHIFT_SHL)       r32 = a32 << sh;
                else if (ins->subop == TISA_SHIFT_SHRU) r32 = a32 >> sh;
                else if (ins->subop == TISA_SHIFT_SHRS) r32 = (uint32_t)((int32_t)a32 >> sh);
                else return false;
                *out_val = (uint64_t)r32;
                return true;
            }
            if (ins->ty == TISA_TYPE_I32S) {
                if (sh >= 32u) return false;
                int32_t s32 = (int32_t)(uint32_t)regs[ins->src1];
                int32_t r32 = 0;
                if (ins->subop == TISA_SHIFT_SHL)       r32 = (int32_t)((uint32_t)s32 << sh);
                else if (ins->subop == TISA_SHIFT_SHRU) r32 = (int32_t)((uint32_t)s32 >> sh);
                else if (ins->subop == TISA_SHIFT_SHRS) r32 = s32 >> sh;
                else return false;
                *out_val = (uint64_t)(int64_t)r32;
                return true;
            }
            uint64_t a = regs[ins->src1];
            uint64_t r = 0;
            if (ins->subop == TISA_SHIFT_SHL)       r = a << sh;
            else if (ins->subop == TISA_SHIFT_SHRU) r = a >> sh;
            else if (ins->subop == TISA_SHIFT_SHRS) r = (uint64_t)((int64_t)a >> sh);
            else return false;
            *out_val = r;
            return true;
        }

        case TISA_OP_EXTRACT: {
            uint8_t lsb = ins->scale_lg2;
            uint8_t wid = ins->bit_width;
            if (wid == 0u || (uint32_t)lsb + (uint32_t)wid > 64u) return false;
            uint64_t a = regs[ins->src1] >> lsb;
            uint64_t mask = (wid == 64u) ? UINT64_MAX : ((1ull << wid) - 1ull);
            *out_val = tisa_norm_type(ins->ty, a & mask);
            return true;
        }

        case TISA_OP_ADDR: {
            if (ins->scale_lg2 > 3u) return false;
            uint64_t base = regs[ins->src1];
            uint64_t idx  = (ins->src2 == 0xFFu) ? 0ull : regs[ins->src2];
            if (ins->scale_lg2 > 0u && (idx >> (64u - ins->scale_lg2)) != 0ull) return false;
            uint64_t scaled = idx << ins->scale_lg2;
            if (scaled > UINT64_MAX - base) return false;
            uint64_t mid = base + scaled;
            if (ins->disp32 >= 0) {
                uint64_t d = (uint64_t)ins->disp32;
                if (d > UINT64_MAX - mid) return false;
                *out_val = mid + d;
            } else {
                uint64_t d = (uint64_t)(-(int64_t)ins->disp32);
                if (d > mid) return false;
                *out_val = mid - d;
            }
            return true;
        }

        case TISA_OP_CMP: {
            uint64_t a = regs[ins->src1];
            uint64_t b = (ins->bit_width != 0u) ? ins->imm64 : regs[ins->src2];
            bool res = false;
            if (ins->ty == TISA_TYPE_U32Z || ins->ty == TISA_TYPE_I32S) {
                uint32_t au = (uint32_t)a;
                uint32_t bu = (uint32_t)b;
                int32_t  as = (int32_t)au;
                int32_t  bs = (int32_t)bu;
                switch (ins->subop) {
                    case TISA_CMP_EQ:  res = (au == bu); break;
                    case TISA_CMP_NE:  res = (au != bu); break;
                    case TISA_CMP_ULT: res = (au < bu);  break;
                    case TISA_CMP_ULE: res = (au <= bu); break;
                    case TISA_CMP_SLT: res = (as < bs);  break;
                    case TISA_CMP_SLE: res = (as <= bs); break;
                    default: return false;
                }
            } else {
                switch (ins->subop) {
                    case TISA_CMP_EQ:  res = (a == b); break;
                    case TISA_CMP_NE:  res = (a != b); break;
                    case TISA_CMP_ULT: res = (a < b);  break;
                    case TISA_CMP_ULE: res = (a <= b); break;
                    case TISA_CMP_SLT: res = ((int64_t)a < (int64_t)b);  break;
                    case TISA_CMP_SLE: res = ((int64_t)a <= (int64_t)b); break;
                    default: return false;
                }
            }
            *out_val = res ? 1ull : 0ull;
            return true;
        }

        case TISA_OP_SELECT: {
            uint64_t c = regs[ins->src3];
            if (c > 1ull) return false;
            if (ins->ty == TISA_TYPE_BOOL && (regs[ins->src1] > 1ull || regs[ins->src2] > 1ull)) return false;
            uint64_t chosen = (c == 1ull) ? regs[ins->src1] : regs[ins->src2];
            *out_val = tisa_norm_type(ins->ty, chosen);
            return true;
        }

        default:
            return false;
    }
}

static bool tisa_check_mem_offset_words(uint64_t base,
                                        uint64_t len,
                                        uint64_t ptr_val,
                                        int32_t disp32,
                                        uint8_t width,
                                        uint64_t *out_rel_off) {
    if (ptr_val < base) return false;
    uint64_t base_off = ptr_val - base;
    if (base_off > len) return false;
    uint64_t rel_off = 0;
    if (disp32 >= 0) {
        uint64_t d = (uint64_t)disp32;
        if (d > len - base_off) return false;
        rel_off = base_off + d;
    } else {
        uint64_t d = (uint64_t)(-(int64_t)disp32);
        if (d > base_off) return false;
        rel_off = base_off - d;
    }
    if (width > len || rel_off > len - width) return false;
    *out_rel_off = rel_off;
    return true;
}

static bool tisa_check_mem_offset(const TcIsaRuntimeFrame *frame,
                                  uint8_t region_id,
                                  uint64_t ptr_val,
                                  int32_t disp32,
                                  uint8_t width,
                                  uint64_t *out_rel_off) {
    if (region_id >= TISA_MAX_REGIONS) return false;
    const uint64_t *raw = &frame->s0_ptr;
    uint64_t base = raw[region_id * 2u];
    uint64_t len  = raw[region_id * 2u + 1u];
    return tisa_check_mem_offset_words(base, len, ptr_val, disp32, width, out_rel_off);
}

/* =========================================================================
 * 5. Independent Structured Reference Evaluator (`tisa_eval_ref`)
 * ========================================================================= */

typedef struct {
    const TcIsaProgram *prog;
    TcIsaRuntimeFrame  *frame;
    uint64_t           *regs;
    bool                returned;
    TcIsaOutcome        outcome;
} TcIsaRefCtx;

static inline void tisa_fail_ref(TcIsaRefCtx *ctx, TcIsaOutcome oc) {
    ctx->outcome = oc;
    if (ctx->frame) {
        ctx->frame->status  = (uint64_t)oc;
        ctx->frame->ret_val = (uint64_t)oc;
    }
    ctx->returned = true;
}

static bool tisa_consume_fuel(TcIsaRuntimeFrame *frame) {
    if (frame->fuel_budget > 0 && frame->fuel_used >= frame->fuel_budget) {
        frame->status  = TISA_OUTCOME_EXHAUSTED;
        frame->ret_val = TISA_OUTCOME_EXHAUSTED;
        return false;
    }
    frame->fuel_used++;
    return true;
}

static void tisa_eval_ref_stmt(TcIsaRefCtx *ctx, const TcIsaStmt *stmt) {
    if (!stmt || ctx->returned) return;
    switch (stmt->kind) {
        case TISA_CTRL_INSTR: {
            if (!tisa_consume_fuel(ctx->frame)) {
                tisa_fail_ref(ctx, TISA_OUTCOME_EXHAUSTED);
                return;
            }
            const TcIsaInstr *ins = &stmt->u.instr;
            if (ins->op == TISA_OP_LOAD) {
                if (ins->region_id == TISA_REGION_FRAME) {
                    if (ins->disp32 < 0 || (ins->disp32 % 8) != 0 ||
                        (size_t)ins->disp32 + 8u > sizeof(TcIsaRuntimeFrame)) {
                        tisa_fail_ref(ctx, TISA_OUTCOME_INVALID_INPUT);
                        return;
                    }
                    uint64_t v = ((const uint64_t *)&ctx->frame->s0_ptr)[ins->disp32 / 8];
                    ctx->regs[ins->dst] = tisa_norm_type(ins->ty, v);
                    return;
                }
                uint64_t rel_off = 0;
                if (!tisa_check_mem_offset(ctx->frame, ins->region_id, ctx->regs[ins->src1],
                                           ins->disp32, ins->subop, &rel_off)) {
                    tisa_fail_ref(ctx, TISA_OUTCOME_INVALID_INPUT);
                    return;
                }
                const uint8_t *p = (const uint8_t *)(uintptr_t)(&ctx->frame->s0_ptr)[ins->region_id * 2u] + rel_off;
                uint64_t v = 0;
                for (uint8_t b = 0; b < ins->subop; b++) {
                    v |= ((uint64_t)p[b]) << (b * 8u);
                }
                ctx->regs[ins->dst] = tisa_norm_type(ins->ty, v);
                return;
            }
            if (ins->op == TISA_OP_STORE) {
                uint64_t rel_off = 0;
                if (!tisa_check_mem_offset(ctx->frame, ins->region_id, ctx->regs[ins->src1],
                                           ins->disp32, ins->subop, &rel_off)) {
                    tisa_fail_ref(ctx, TISA_OUTCOME_INVALID_INPUT);
                    return;
                }
                uint8_t *p = (uint8_t *)(uintptr_t)(&ctx->frame->s0_ptr)[ins->region_id * 2u] + rel_off;
                uint64_t v = ctx->regs[ins->src2];
                for (uint8_t b = 0; b < ins->subop; b++) {
                    p[b] = (uint8_t)((v >> (b * 8u)) & 0xFFu);
                }
                return;
            }
            if (ins->op == TISA_OP_ADDR) {
                uint64_t base_ptr = (&ctx->frame->s0_ptr)[ins->region_id * 2u];
                uint64_t len_bytes = (&ctx->frame->s0_ptr)[ins->region_id * 2u + 1u];
                uint64_t cur_ptr = ctx->regs[ins->src1];
                uint64_t idx = (ins->src2 == 0xFFu) ? 0ull : ctx->regs[ins->src2];
                if (ins->scale_lg2 > 3u || cur_ptr < base_ptr || (cur_ptr - base_ptr) > len_bytes) {
                    tisa_fail_ref(ctx, TISA_OUTCOME_INVALID_INPUT);
                    return;
                }
                if (ins->scale_lg2 > 0u && (idx >> (64u - ins->scale_lg2)) != 0ull) {
                    tisa_fail_ref(ctx, TISA_OUTCOME_INVALID_INPUT);
                    return;
                }
                uint64_t scaled = idx << ins->scale_lg2;
                uint64_t base_off = cur_ptr - base_ptr;
                if (scaled > len_bytes - base_off) {
                    tisa_fail_ref(ctx, TISA_OUTCOME_INVALID_INPUT);
                    return;
                }
                uint64_t after_idx = base_off + scaled;
                if (ins->disp32 >= 0) {
                    if ((uint64_t)ins->disp32 > len_bytes - after_idx) {
                        tisa_fail_ref(ctx, TISA_OUTCOME_INVALID_INPUT);
                        return;
                    }
                } else {
                    if ((uint64_t)(-(int64_t)ins->disp32) > after_idx) {
                        tisa_fail_ref(ctx, TISA_OUTCOME_INVALID_INPUT);
                        return;
                    }
                }
            }
            uint64_t out_val = 0;
            if (!tisa_scalar_eval(ins, ctx->regs, &out_val)) {
                tisa_fail_ref(ctx, TISA_OUTCOME_INVALID_INPUT);
                return;
            }
            ctx->regs[ins->dst] = out_val;
            return;
        }

        case TISA_CTRL_SEQ:
            tisa_eval_ref_stmt(ctx, stmt->u.seq.first);
            if (!ctx->returned) tisa_eval_ref_stmt(ctx, stmt->u.seq.second);
            return;

        case TISA_CTRL_IF: {
            uint64_t c = ctx->regs[stmt->u.if_cond.cond_reg];
            if (c > 1ull) {
                tisa_fail_ref(ctx, TISA_OUTCOME_INVALID_INPUT);
                return;
            }
            if (c == 1ull) tisa_eval_ref_stmt(ctx, stmt->u.if_cond.then_branch);
            else if (stmt->u.if_cond.else_branch) tisa_eval_ref_stmt(ctx, stmt->u.if_cond.else_branch);
            return;
        }

        case TISA_CTRL_COUNT_LOOP: {
            uint8_t ir = stmt->u.count_loop.idx_reg;
            uint8_t br = stmt->u.count_loop.bound_reg;
            uint64_t bound = ctx->regs[br];
            if (bound > (uint64_t)stmt->u.count_loop.max_iters) {
                tisa_fail_ref(ctx, TISA_OUTCOME_UNSUPPORTED);
                return;
            }
            ctx->regs[ir] = 0ull;
            while (ctx->regs[ir] < bound) {
                tisa_eval_ref_stmt(ctx, stmt->u.count_loop.body);
                if (ctx->returned) return;
                ctx->regs[ir] += 1ull;
            }
            return;
        }

        case TISA_CTRL_EARLY_EXIT_LOOP: {
            uint8_t ir = stmt->u.early_exit_loop.idx_reg;
            uint8_t br = stmt->u.early_exit_loop.bound_reg;
            uint8_t cr = stmt->u.early_exit_loop.cont_reg;
            uint64_t bound = ctx->regs[br];
            if (bound > (uint64_t)stmt->u.early_exit_loop.max_iters) {
                tisa_fail_ref(ctx, TISA_OUTCOME_UNSUPPORTED);
                return;
            }
            ctx->regs[ir] = 0ull;
            while (ctx->regs[ir] < bound) {
                uint64_t cont = ctx->regs[cr];
                if (cont > 1ull) {
                    tisa_fail_ref(ctx, TISA_OUTCOME_INVALID_INPUT);
                    return;
                }
                if (cont == 0ull) break;
                tisa_eval_ref_stmt(ctx, stmt->u.early_exit_loop.body);
                if (ctx->returned) return;
                cont = ctx->regs[cr];
                if (cont > 1ull) {
                    tisa_fail_ref(ctx, TISA_OUTCOME_INVALID_INPUT);
                    return;
                }
                if (cont == 0ull) break;
                ctx->regs[ir] += 1ull;
            }
            return;
        }

        case TISA_CTRL_RETURN:
            ctx->outcome = stmt->u.ret.outcome;
            ctx->frame->status = stmt->u.ret.outcome;
            ctx->frame->ret_val = ctx->regs[stmt->u.ret.ret_reg];
            ctx->returned = true;
            return;
        case TISA_CTRL_FUND:   /* profile p1 (tisa_ref.c); p0 has no funded points */
            tisa_fail_ref(ctx, TISA_OUTCOME_UNSUPPORTED);
            return;
    }
}

TcIsaOutcome tisa_eval_ref(const TcIsaProgram *prog,
                           TcIsaRuntimeFrame *frame,
                           uint64_t regs[TISA_NUM_VREGS]) {
    char err[256] = {0};
    TcIsaOutcome vrc = tisa_validate_frame(prog, frame, regs, err, sizeof(err));
    if (vrc != TISA_OUTCOME_FIRED) {
        if (frame) {
            frame->status = vrc;
            frame->ret_val = vrc;
        }
        return vrc;
    }
    frame->fuel_used = 0;
    TcIsaRefCtx ctx = {
        .prog = prog,
        .frame = frame,
        .regs = regs,
        .returned = false,
        .outcome = TISA_OUTCOME_REFUSED
    };
    tisa_eval_ref_stmt(&ctx, prog->root);
    return ctx.outcome;
}

/* =========================================================================
 * 5b. Continuation-Contextual Semantic-PC Recipe Lowering (`tisa_lower_recipes`)
 *
 * Lowers a validated structured `TcIsaProgram` into an immutable table of
 * semantic-PC recipes (`TcIsaRecipeTable`) matching:
 *   - `Mettapedia/Machines/TIsa/Control.lean`
 *   - `Mettapedia/Machines/TIsa/Continuation.lean`
 *   - `Mettapedia/Machines/TIsa/Branch.lean`
 *   - `Mettapedia/Machines/TIsa/Loop.lean`
 * ========================================================================= */

#define TISA_POINT_PH_TAG   (1ull << 61)
#define TISA_POINT_FAIL_TAG (1ull << 59)

static bool tisa_alloc_recipe_point(TcIsaRecipeTable *out,
                                    TcIsaRecipeKind kind,
                                    uint32_t *out_pt,
                                    char *err_buf, size_t err_cap) {
    if (out->npoints >= TISA_MAX_RECIPE_POINTS) {
        tisa_set_err(err_buf, err_cap, "recipe table exceeded TISA_MAX_RECIPE_POINTS (%u)",
                     (unsigned)TISA_MAX_RECIPE_POINTS);
        return false;
    }
    uint32_t pt = out->npoints++;
    TcIsaPointRecipe *r = &out->recipes[pt];
    memset(r, 0, sizeof(*r));
    r->point      = pt;
    r->kind       = kind;
    r->cond_reg   = 0xFFu;
    r->idx_reg    = 0xFFu;
    r->bound_reg  = 0xFFu;
    r->ret_reg    = 0xFFu;
    r->next_point = UINT64_MAX;
    r->alt_point  = UINT64_MAX;
    r->fail_point = UINT64_MAX;
    *out_pt = pt;
    return true;
}

static void tisa_resolve_placeholder(TcIsaRecipeTable *out,
                                     uint32_t from_idx,
                                     uint32_t to_idx,
                                     uint64_t ph_token,
                                     uint64_t target_point) {
    for (uint32_t i = from_idx; i < to_idx && i < out->npoints; i++) {
        if (out->recipes[i].next_point == ph_token) out->recipes[i].next_point = target_point;
        if (out->recipes[i].alt_point  == ph_token) out->recipes[i].alt_point  = target_point;
        if (out->recipes[i].fail_point == ph_token) out->recipes[i].fail_point = target_point;
    }
}

static bool tisa_lower_stmt_rec(const TcIsaProgram *prog,
                                const TcIsaStmt *stmt,
                                uint64_t cont_point,
                                TcIsaRecipeTable *out,
                                uint32_t *next_ph_id,
                                char *err_buf, size_t err_cap) {
    if (!stmt) return true;
    switch (stmt->kind) {
        case TISA_CTRL_INSTR: {
            const TcIsaInstr *ins = &stmt->u.instr;
            uint32_t p_fuel = 0;
            if (!tisa_alloc_recipe_point(out, TISA_RECIPE_FUEL, &p_fuel, err_buf, err_cap)) return false;
            out->recipes[p_fuel].charges_fuel = true;
            out->recipes[p_fuel].fail_point   = TISA_POINT_FAIL_TAG | (uint64_t)TISA_OUTCOME_EXHAUSTED;

            if (ins->op != TISA_OP_STORE) {
                uint32_t p_ins = 0;
                if (!tisa_alloc_recipe_point(out, TISA_RECIPE_INSTR, &p_ins, err_buf, err_cap)) return false;
                out->recipes[p_fuel].next_point = (uint64_t)p_ins;
                out->recipes[p_ins].charges_fuel = false;
                out->recipes[p_ins].instr        = *ins;
                out->recipes[p_ins].next_point   = cont_point;
                out->recipes[p_ins].fail_point   = TISA_POINT_FAIL_TAG | (uint64_t)TISA_OUTCOME_INVALID_INPUT;
                return true;
            }

            uint8_t w = ins->subop;
            if (w != TISA_MEM_U8 && w != TISA_MEM_U32 && w != TISA_MEM_U64) {
                tisa_set_err(err_buf, err_cap, "invalid STORE byte width %u in recipe lowering", (unsigned)w);
                return false;
            }
            uint32_t first_store = out->npoints;
            for (uint8_t phase = 0; phase < w; phase++) {
                uint32_t p_sb = 0;
                if (!tisa_alloc_recipe_point(out, TISA_RECIPE_STORE_BYTE, &p_sb, err_buf, err_cap)) return false;
                out->recipes[p_sb].charges_fuel = false;
                out->recipes[p_sb].instr        = *ins;
                out->recipes[p_sb].byte_phase   = phase;
                out->recipes[p_sb].byte_width   = w;
                out->recipes[p_sb].next_point   = (phase + 1u < w) ? (uint64_t)(p_sb + 1u) : cont_point;
                out->recipes[p_sb].fail_point   = TISA_POINT_FAIL_TAG | (uint64_t)TISA_OUTCOME_INVALID_INPUT;
            }
            out->recipes[p_fuel].next_point = (uint64_t)first_store;
            return true;
        }

        case TISA_CTRL_SEQ: {
            if (!stmt->u.seq.first) {
                return tisa_lower_stmt_rec(prog, stmt->u.seq.second, cont_point, out, next_ph_id, err_buf, err_cap);
            }
            if (!stmt->u.seq.second) {
                return tisa_lower_stmt_rec(prog, stmt->u.seq.first, cont_point, out, next_ph_id, err_buf, err_cap);
            }
            uint32_t start_first = out->npoints;
            uint64_t ph = TISA_POINT_PH_TAG | (uint64_t)((*next_ph_id)++);
            if (!tisa_lower_stmt_rec(prog, stmt->u.seq.first, ph, out, next_ph_id, err_buf, err_cap)) {
                return false;
            }
            uint32_t sec_entry = out->npoints;
            tisa_resolve_placeholder(out, start_first, sec_entry, ph, (uint64_t)sec_entry);
            return tisa_lower_stmt_rec(prog, stmt->u.seq.second, cont_point, out, next_ph_id, err_buf, err_cap);
        }

        case TISA_CTRL_IF: {
            uint32_t p_br = 0;
            if (!tisa_alloc_recipe_point(out, TISA_RECIPE_BRANCH, &p_br, err_buf, err_cap)) return false;
            out->recipes[p_br].cond_reg   = stmt->u.if_cond.cond_reg;
            out->recipes[p_br].fail_point = TISA_POINT_FAIL_TAG | (uint64_t)TISA_OUTCOME_INVALID_INPUT;

            uint64_t then_entry = cont_point;
            if (stmt->u.if_cond.then_branch) {
                then_entry = (uint64_t)out->npoints;
                if (!tisa_lower_stmt_rec(prog, stmt->u.if_cond.then_branch, cont_point, out, next_ph_id, err_buf, err_cap)) {
                    return false;
                }
            }
            uint64_t else_entry = cont_point;
            if (stmt->u.if_cond.else_branch) {
                else_entry = (uint64_t)out->npoints;
                if (!tisa_lower_stmt_rec(prog, stmt->u.if_cond.else_branch, cont_point, out, next_ph_id, err_buf, err_cap)) {
                    return false;
                }
            }
            out->recipes[p_br].next_point = then_entry;
            out->recipes[p_br].alt_point  = else_entry;
            return true;
        }

        case TISA_CTRL_COUNT_LOOP: {
            uint8_t ir = stmt->u.count_loop.idx_reg;
            uint8_t br = stmt->u.count_loop.bound_reg;
            uint32_t max_it = stmt->u.count_loop.max_iters;

            uint32_t p_entry = 0, p_hdr = 0;
            if (!tisa_alloc_recipe_point(out, TISA_RECIPE_LOOP_ENTRY,  &p_entry, err_buf, err_cap)) return false;
            if (!tisa_alloc_recipe_point(out, TISA_RECIPE_LOOP_HEADER, &p_hdr,   err_buf, err_cap)) return false;

            out->recipes[p_entry].idx_reg    = ir;
            out->recipes[p_entry].bound_reg  = br;
            out->recipes[p_entry].max_iters  = max_it;
            out->recipes[p_entry].next_point = (uint64_t)p_hdr;
            out->recipes[p_entry].fail_point = TISA_POINT_FAIL_TAG | (uint64_t)TISA_OUTCOME_UNSUPPORTED;

            out->recipes[p_hdr].idx_reg    = ir;
            out->recipes[p_hdr].bound_reg  = br;
            out->recipes[p_hdr].max_iters  = max_it;
            out->recipes[p_hdr].alt_point  = cont_point;
            out->recipes[p_hdr].fail_point = TISA_POINT_FAIL_TAG | (uint64_t)TISA_OUTCOME_INVALID_INPUT;

            uint64_t ph_latch = TISA_POINT_PH_TAG | (uint64_t)((*next_ph_id)++);
            uint32_t body_start = out->npoints;
            if (stmt->u.count_loop.body) {
                if (!tisa_lower_stmt_rec(prog, stmt->u.count_loop.body, ph_latch, out, next_ph_id, err_buf, err_cap)) {
                    return false;
                }
            }
            uint32_t p_latch = 0;
            if (!tisa_alloc_recipe_point(out, TISA_RECIPE_LOOP_LATCH, &p_latch, err_buf, err_cap)) return false;
            out->recipes[p_latch].idx_reg    = ir;
            out->recipes[p_latch].bound_reg  = br;
            out->recipes[p_latch].max_iters  = max_it;
            out->recipes[p_latch].next_point = (uint64_t)p_hdr;
            out->recipes[p_latch].fail_point = TISA_POINT_FAIL_TAG | (uint64_t)TISA_OUTCOME_INVALID_INPUT;

            out->recipes[p_hdr].next_point = stmt->u.count_loop.body ? (uint64_t)body_start : (uint64_t)p_latch;
            tisa_resolve_placeholder(out, body_start, p_latch, ph_latch, (uint64_t)p_latch);
            return true;
        }

        case TISA_CTRL_EARLY_EXIT_LOOP: {
            uint8_t ir = stmt->u.early_exit_loop.idx_reg;
            uint8_t br = stmt->u.early_exit_loop.bound_reg;
            uint8_t cr = stmt->u.early_exit_loop.cont_reg;
            uint32_t max_it = stmt->u.early_exit_loop.max_iters;

            uint32_t p_entry = 0, p_hdr = 0, p_pre_cont = 0;
            if (!tisa_alloc_recipe_point(out, TISA_RECIPE_LOOP_ENTRY,  &p_entry,    err_buf, err_cap)) return false;
            if (!tisa_alloc_recipe_point(out, TISA_RECIPE_LOOP_HEADER, &p_hdr,      err_buf, err_cap)) return false;
            if (!tisa_alloc_recipe_point(out, TISA_RECIPE_BRANCH,      &p_pre_cont, err_buf, err_cap)) return false;

            out->recipes[p_entry].idx_reg    = ir;
            out->recipes[p_entry].bound_reg  = br;
            out->recipes[p_entry].max_iters  = max_it;
            out->recipes[p_entry].next_point = (uint64_t)p_hdr;
            out->recipes[p_entry].fail_point = TISA_POINT_FAIL_TAG | (uint64_t)TISA_OUTCOME_UNSUPPORTED;

            out->recipes[p_hdr].idx_reg    = ir;
            out->recipes[p_hdr].bound_reg  = br;
            out->recipes[p_hdr].max_iters  = max_it;
            out->recipes[p_hdr].next_point = (uint64_t)p_pre_cont;
            out->recipes[p_hdr].alt_point  = cont_point;
            out->recipes[p_hdr].fail_point = TISA_POINT_FAIL_TAG | (uint64_t)TISA_OUTCOME_INVALID_INPUT;

            out->recipes[p_pre_cont].cond_reg   = cr;
            out->recipes[p_pre_cont].alt_point  = cont_point;
            out->recipes[p_pre_cont].fail_point = TISA_POINT_FAIL_TAG | (uint64_t)TISA_OUTCOME_INVALID_INPUT;

            uint64_t ph_post_cont = TISA_POINT_PH_TAG | (uint64_t)((*next_ph_id)++);
            uint32_t body_start = out->npoints;
            if (stmt->u.early_exit_loop.body) {
                if (!tisa_lower_stmt_rec(prog, stmt->u.early_exit_loop.body, ph_post_cont, out, next_ph_id, err_buf, err_cap)) {
                    return false;
                }
            }
            uint32_t p_post_cont = 0, p_latch = 0;
            if (!tisa_alloc_recipe_point(out, TISA_RECIPE_BRANCH,     &p_post_cont, err_buf, err_cap)) return false;
            if (!tisa_alloc_recipe_point(out, TISA_RECIPE_LOOP_LATCH, &p_latch,     err_buf, err_cap)) return false;

            out->recipes[p_post_cont].cond_reg   = cr;
            out->recipes[p_post_cont].next_point = (uint64_t)p_latch;
            out->recipes[p_post_cont].alt_point  = cont_point;
            out->recipes[p_post_cont].fail_point = TISA_POINT_FAIL_TAG | (uint64_t)TISA_OUTCOME_INVALID_INPUT;

            out->recipes[p_latch].idx_reg    = ir;
            out->recipes[p_latch].bound_reg  = br;
            out->recipes[p_latch].max_iters  = max_it;
            out->recipes[p_latch].next_point = (uint64_t)p_hdr;
            out->recipes[p_latch].fail_point = TISA_POINT_FAIL_TAG | (uint64_t)TISA_OUTCOME_INVALID_INPUT;

            out->recipes[p_pre_cont].next_point = stmt->u.early_exit_loop.body ? (uint64_t)body_start : (uint64_t)p_post_cont;
            tisa_resolve_placeholder(out, body_start, p_post_cont, ph_post_cont, (uint64_t)p_post_cont);
            return true;
        }

        case TISA_CTRL_RETURN: {
            uint32_t p_st = 0, p_rv = 0;
            if (!tisa_alloc_recipe_point(out, TISA_RECIPE_FINALIZE_STATUS, &p_st, err_buf, err_cap)) return false;
            if (!tisa_alloc_recipe_point(out, TISA_RECIPE_FINALIZE_RETVAL, &p_rv, err_buf, err_cap)) return false;

            out->recipes[p_st].outcome    = stmt->u.ret.outcome;
            out->recipes[p_st].ret_reg    = stmt->u.ret.ret_reg;
            out->recipes[p_st].next_point = (uint64_t)p_rv;

            out->recipes[p_rv].outcome    = stmt->u.ret.outcome;
            out->recipes[p_rv].ret_reg    = stmt->u.ret.ret_reg;
            out->recipes[p_rv].next_point = TISA_POINT_HALT(stmt->u.ret.outcome);
            return true;
        }

        default:
            tisa_set_err(err_buf, err_cap, "unknown control kind %d in recipe lowering", (int)stmt->kind);
            return false;
    }
}

bool tisa_lower_recipes(const TcIsaProgram *prog,
                        TcIsaRecipeTable *out,
                        char *err_buf, size_t err_cap) {
    if (!prog || !out) {
        tisa_set_err(err_buf, err_cap, "null program or recipe table output");
        return false;
    }
    memset(out, 0, sizeof(*out));
    TcIsaProgram checked = *prog;
    if (!tisa_check_program(&checked, err_buf, err_cap)) {
        return false;
    }

    uint32_t next_ph_id = 1u;
    out->entry_point = 0ull;
    uint64_t root_cont = TISA_POINT_FAIL_TAG | (uint64_t)TISA_OUTCOME_REFUSED;
    if (!tisa_lower_stmt_rec(&checked, checked.root, root_cont, out, &next_ph_id, err_buf, err_cap)) {
        return false;
    }

    /* Allocate 2-point failure finalize sequences (FINALIZE_STATUS -> FINALIZE_RETVAL -> HALT)
     * for all 5 outcomes so any guard/fuel/bound refusal transitions on the tcalc board. */
    for (int oc = 0; oc < 5; oc++) {
        uint32_t p_st = 0, p_rv = 0;
        if (!tisa_alloc_recipe_point(out, TISA_RECIPE_FINALIZE_STATUS, &p_st, err_buf, err_cap)) return false;
        if (!tisa_alloc_recipe_point(out, TISA_RECIPE_FINALIZE_RETVAL, &p_rv, err_buf, err_cap)) return false;
        out->recipes[p_st].outcome    = (TcIsaOutcome)oc;
        out->recipes[p_st].ret_reg    = 0xFFu;
        out->recipes[p_st].next_point = (uint64_t)p_rv;
        out->recipes[p_rv].outcome    = (TcIsaOutcome)oc;
        out->recipes[p_rv].ret_reg    = 0xFFu;
        out->recipes[p_rv].next_point = TISA_POINT_HALT((TcIsaOutcome)oc);
        out->fail_status_point[oc]    = (uint64_t)p_st;
    }

    for (int oc = 0; oc < 5; oc++) {
        tisa_resolve_placeholder(out, 0u, out->npoints,
                                 TISA_POINT_FAIL_TAG | (uint64_t)oc,
                                 out->fail_status_point[oc]);
    }

    /* Final invariant check: all point indices must be resolved and within [0, npoints) or HALT */
    for (uint32_t i = 0; i < out->npoints; i++) {
        const TcIsaPointRecipe *r = &out->recipes[i];
        if (r->point != i) {
            tisa_set_err(err_buf, err_cap, "recipe point index mismatch at %u", (unsigned)i);
            return false;
        }
        uint64_t targets[3] = { r->next_point, r->alt_point, r->fail_point };
        for (int t = 0; t < 3; t++) {
            uint64_t tgt = targets[t];
            if (tgt == UINT64_MAX) continue;
            if ((tgt & TISA_POINT_PH_TAG) != 0ull || (tgt & TISA_POINT_FAIL_TAG) != 0ull) {
                tisa_set_err(err_buf, err_cap, "unresolved continuation placeholder at recipe %u", (unsigned)i);
                return false;
            }
            if (TISA_POINT_IS_HALT(tgt)) {
                if ((uint32_t)TISA_POINT_HALT_OUTCOME(tgt) >= 5u) {
                    tisa_set_err(err_buf, err_cap, "invalid halt outcome at recipe %u", (unsigned)i);
                    return false;
                }
                continue;
            }
            if (tgt >= (uint64_t)out->npoints) {
                tisa_set_err(err_buf, err_cap, "out-of-range target %" PRIu64 " at recipe %u", tgt, (unsigned)i);
                return false;
            }
        }
    }
    return true;
}


/* =========================================================================
 * 6. Real `tcalc`-Hosted Execution (`tisa_eval_tcalc`)
 *
 * Hosts `t-ISA` as a profile of `tcalc` resource transitions (matching
 * `Mettapedia/Machines/TIsa/Cells.lean`, `Admission.lean`, `CheckedAdmission.lean`,
 * `Continuation.lean`, `Branch.lean`, `Loop.lean`, `RegisterBlock.lean`) over two
 * protected spaces:
 *   STATE    Cell(kind, key, val): the control cell (kind CTRL, key 0, val = the current
 *            point) and one data cell per register, frame word and region byte; its only
 *            producers are the STEP rules;
 *   PROGRAM  Instr(prog, pc, iid, form, dkind, dkey, k1..k4, imm, disp, a1, a2, next, alt, fail):
 *            the immutable recipe of each point, posted before the seal (no producers).
 * Every word is a literal of the word sort. One executed point is one firing of a STEP rule.
 * A form has one STEP rule per case (and, for a case that writes, per alias set of the
 * destination among the cells it reads); the case's guards (sealed predicates of matched words)
 * select it. STEP takes the control cell and, when the case writes, the destination cell; keeps
 * Instr and the cells the recipe reads; computes the case's operations (sealed functions, one per
 * meaning); checks the written word's type and a store's address; and makes the control cell at
 * the case's next (an Instr field) and the destination holding the value.
 * No caller supplies a word: every made hole is matched, computed, or fixed by the rule (the
 * kernel checks range restriction and that every producer's input list is empty), so the cell a
 * step makes is the protected value fact: a sealed function's value at matched words, in a space
 * only the steps write. The control cell is the activation's one linear token.
 * ========================================================================= */

#define TISA_SPACE_STATE   1
#define TISA_SPACE_PROGRAM 2

enum {
    TISA_KEY_KIND_CTRL  = 0, /* Location.inl activation */
    TISA_KEY_KIND_REG   = 1, /* Location.inr (Key.reg r) */
    TISA_KEY_KIND_BYTE  = 2, /* Location.inr (Key.byte phys_addr) — full 64-bit U64 */
    TISA_KEY_KIND_FRAME = 3, /* Location.inr (Key.frame word_idx) */
    TISA_KEY_KIND_NONE  = 0xFF
};
enum { TISA_CASE_UPDATE = 1, TISA_CASE_CTRL = 2 };   /* the case writes its destination / moves control only */
enum { TI_PROG, TI_PC, TI_IID, TI_FORM, TI_DKIND, TI_DKEY, TI_K1, TI_K2, TI_K3, TI_K4,
       TI_IMM, TI_DISP, TI_A1, TI_A2, TI_NEXT, TI_ALT, TI_FAIL, TI_N };

/* ---- 6a. The sealed functions ----
   Registered C, trusted until a proved native image replaces it; each is a TcFn
   (const uint64_t *in, uint64_t *out) -> bool, i.e. SysV RDI = in, RSI = out, result in AL.
   Operations write out[0] and return true, or return false (no value); guards decide. */

static inline uint64_t tisa_zext32(uint64_t x) { return (uint64_t)(uint32_t)x; }
static inline uint64_t tisa_sext32(uint64_t x) { return (uint64_t)(int64_t)(int32_t)(uint32_t)x; }

/* add64, sub64, and64, or64 and xor64 are proved native images, not C (tisa/native_alu.S): each the
   34 bytes of tisa/native_alu/NAME.bin, with its expected copy for the check at registration. */
extern bool tisa_native_add64(const uint64_t *in, uint64_t *out);
extern bool tisa_native_sub64(const uint64_t *in, uint64_t *out);
extern bool tisa_native_and64(const uint64_t *in, uint64_t *out);
extern bool tisa_native_or64(const uint64_t *in, uint64_t *out);
extern bool tisa_native_xor64(const uint64_t *in, uint64_t *out);
extern const uint8_t tisa_native_add64_expected[34], tisa_native_sub64_expected[34], tisa_native_and64_expected[34],
                     tisa_native_or64_expected[34], tisa_native_xor64_expected[34];

#define TISA_OP2(nm, expr) \
    static bool tisa_fn_##nm(const uint64_t *in, uint64_t *out) { uint64_t x = in[0], y = in[1]; out[0] = (expr); return true; }
TISA_OP2(mul64, x * y)
TISA_OP2(add32z, tisa_zext32(x + y))
TISA_OP2(sub32z, tisa_zext32(x - y))
TISA_OP2(and32z, tisa_zext32(x & y))
TISA_OP2(or32z, tisa_zext32(x | y))
TISA_OP2(xor32z, tisa_zext32(x ^ y))
TISA_OP2(mul32z, tisa_zext32(x * y))
TISA_OP2(add32s, tisa_sext32(x + y))
TISA_OP2(sub32s, tisa_sext32(x - y))
TISA_OP2(and32s, tisa_sext32(x & y))
TISA_OP2(or32s, tisa_sext32(x | y))
TISA_OP2(xor32s, tisa_sext32(x ^ y))
TISA_OP2(mul32s, tisa_sext32(x * y))
TISA_OP2(eq64, x == y ? 1u : 0u)
TISA_OP2(ne64, x != y ? 1u : 0u)
TISA_OP2(ult64, x < y ? 1u : 0u)
TISA_OP2(ule64, x <= y ? 1u : 0u)
TISA_OP2(slt64, (int64_t)x < (int64_t)y ? 1u : 0u)
TISA_OP2(sle64, (int64_t)x <= (int64_t)y ? 1u : 0u)
TISA_OP2(eq32, (uint32_t)x == (uint32_t)y ? 1u : 0u)
TISA_OP2(ne32, (uint32_t)x != (uint32_t)y ? 1u : 0u)
TISA_OP2(ult32, (uint32_t)x < (uint32_t)y ? 1u : 0u)
TISA_OP2(ule32, (uint32_t)x <= (uint32_t)y ? 1u : 0u)
TISA_OP2(slt32, (int32_t)(uint32_t)x < (int32_t)(uint32_t)y ? 1u : 0u)
TISA_OP2(sle32, (int32_t)(uint32_t)x <= (int32_t)(uint32_t)y ? 1u : 0u)
#undef TISA_OP2
/* Shifts: in[0] = x, in[1] = the amount; no value for an amount at or past the width. */
#define TISA_SHIFT(nm, lim, expr) \
    static bool tisa_fn_##nm(const uint64_t *in, uint64_t *out) { uint64_t x = in[0], n = in[1]; if (n >= (lim)) return false; out[0] = (expr); return true; }
TISA_SHIFT(shl64, 64u, x << n)
TISA_SHIFT(shru64, 64u, x >> n)
TISA_SHIFT(shrs64, 64u, (uint64_t)((int64_t)x >> n))
TISA_SHIFT(shl32z, 32u, (uint64_t)(uint32_t)((uint32_t)x << n))
TISA_SHIFT(shru32z, 32u, (uint64_t)((uint32_t)x >> n))
TISA_SHIFT(shrs32z, 32u, (uint64_t)(uint32_t)((int32_t)(uint32_t)x >> n))
TISA_SHIFT(shl32s, 32u, (uint64_t)(int64_t)(int32_t)((uint32_t)x << n))
TISA_SHIFT(shru32s, 32u, (uint64_t)(int64_t)(int32_t)((uint32_t)x >> n))
TISA_SHIFT(shrs32s, 32u, (uint64_t)(int64_t)((int32_t)(uint32_t)x >> n))
#undef TISA_SHIFT
#define TISA_OP1(nm, expr) \
    static bool tisa_fn_##nm(const uint64_t *in, uint64_t *out) { uint64_t x = in[0]; out[0] = (expr); return true; }
TISA_OP1(zext32, tisa_zext32(x))
TISA_OP1(sext32, tisa_sext32(x))
TISA_OP1(lowbit, x & 1u)
TISA_OP1(inc64, x + 1u)
#undef TISA_OP1
/* in: x, lsb, width; (x >> lsb) masked to width bits; no value unless 1 <= width and lsb + width <= 64 */
static bool tisa_fn_extract(const uint64_t *in, uint64_t *out) {
    uint64_t x = in[0], lsb = in[1], w = in[2];
    if (w == 0u || w > 64u || lsb > 64u - w) return false;
    out[0] = (x >> lsb) & (w == 64u ? UINT64_MAX : ((1ull << w) - 1u));
    return true;
}
/* in: pointer, index, scale, disp (32-bit, sign-extended); pointer + (index << scale) + disp, wrapping;
   no value for a scale above 3 */
static bool tisa_fn_addr_index(const uint64_t *in, uint64_t *out) {
    if (in[2] > 3u) return false;
    out[0] = in[0] + (in[1] << in[2]) + (uint64_t)(int64_t)(int32_t)(int64_t)in[3];
    return true;
}
/* in: pointer, disp; pointer + disp, wrapping */
static bool tisa_fn_addr_noidx(const uint64_t *in, uint64_t *out) {
    out[0] = in[0] + (uint64_t)(int64_t)(int32_t)(int64_t)in[1];
    return true;
}
/* in: b0 .. b(w-1); their little-endian word; no value unless each is a byte */
static bool tisa_pack(const uint64_t *in, int w, uint64_t *out) {
    uint64_t v = 0;
    for (int b = 0; b < w; b++) { if (in[b] > 0xFFu) return false; v |= in[b] << (8 * b); }
    out[0] = v;
    return true;
}
static bool tisa_fn_pack1(const uint64_t *in, uint64_t *out) { return tisa_pack(in, 1, out); }
static bool tisa_fn_pack4(const uint64_t *in, uint64_t *out) { return tisa_pack(in, 4, out); }
static bool tisa_fn_pack8(const uint64_t *in, uint64_t *out) { return tisa_pack(in, 8, out); }
/* in: x, k; byte k of x (little-endian); no value for k above 7 */
static bool tisa_fn_byte_of(const uint64_t *in, uint64_t *out) {
    if (in[1] > 7u) return false;
    out[0] = (in[0] >> (8u * in[1])) & 0xFFu;
    return true;
}

/* Guards: predicates of words. */
#define TISA_G1(nm, expr) static bool tisa_g_##nm(const uint64_t *in, uint64_t *out) { (void)out; uint64_t x = in[0]; return (expr); }
#define TISA_G2(nm, expr) static bool tisa_g_##nm(const uint64_t *in, uint64_t *out) { (void)out; uint64_t x = in[0], y = in[1]; return (expr); }
TISA_G1(is_zero, x == 0u)
TISA_G1(is_one, x == 1u)
TISA_G1(is_bool, x <= 1u)
TISA_G1(above_one, x > 1u)
TISA_G1(valid_byte, x <= 0xFFu)
TISA_G1(valid_u32z, x <= 0xFFFFFFFFull)
TISA_G1(valid_i32s, x == tisa_sext32(x))
TISA_G2(eq, x == y)
TISA_G2(ne, x != y)
TISA_G2(ult, x < y)
TISA_G2(ule, x <= y)
TISA_G2(fuel_available, x == 0u || y < x)    /* in: budget, used (Fuel.lean fuelAvailable) */
TISA_G2(fuel_exhausted, x != 0u && y >= x)
#undef TISA_G1
#undef TISA_G2
/* The hosted ADDR admission: tisa_eval_recipe_instr_guard's capability checks and tisa_scalar_eval's
   overflow checks, over the region [base, base + len). */
static bool tisa_addr_admitted(uint64_t ptr, uint64_t idx, uint64_t scale, uint64_t disp_word,
                               uint64_t base, uint64_t len) {
    int32_t disp = (int32_t)(int64_t)disp_word;
    if (scale > 3u || ptr < base || ptr - base > len) return false;
    if (scale > 0u && (idx >> (64u - scale)) != 0ull) return false;
    uint64_t scaled = idx << scale, base_off = ptr - base;
    if (scaled > len - base_off) return false;
    uint64_t after_idx = base_off + scaled;
    if (disp >= 0) { if ((uint64_t)disp > len - after_idx) return false; }
    else if ((uint64_t)(-(int64_t)disp) > after_idx) return false;
    if (scaled > UINT64_MAX - ptr) return false;
    uint64_t mid = ptr + scaled;
    if (disp >= 0) { if ((uint64_t)disp > UINT64_MAX - mid) return false; }
    else if ((uint64_t)(-(int64_t)disp) > mid) return false;
    return true;
}
/* in: pointer, index, base, len, scale, disp */
static bool tisa_g_addr_admitted(const uint64_t *in, uint64_t *out) { (void)out; return tisa_addr_admitted(in[0], in[1], in[4], in[5], in[2], in[3]); }
static bool tisa_g_addr_refused(const uint64_t *in, uint64_t *out) { (void)out; return !tisa_addr_admitted(in[0], in[1], in[4], in[5], in[2], in[3]); }
/* in: pointer, base, len, disp (no index) */
static bool tisa_g_addr_noidx_admitted(const uint64_t *in, uint64_t *out) { (void)out; return tisa_addr_admitted(in[0], 0, 0, in[3], in[1], in[2]); }
static bool tisa_g_addr_noidx_refused(const uint64_t *in, uint64_t *out) { (void)out; return !tisa_addr_admitted(in[0], 0, 0, in[3], in[1], in[2]); }
/* in: base, len, pointer, disp; the w bytes at pointer + disp lie inside [base, base + len)
   (tisa_check_mem_offset_words) */
static bool tisa_access(const uint64_t *in, uint8_t w) {
    uint64_t rel = 0;
    return tisa_check_mem_offset_words(in[0], in[1], in[2], (int32_t)(int64_t)in[3], w, &rel);
}
static bool tisa_g_access_in1(const uint64_t *in, uint64_t *out) { (void)out; return tisa_access(in, 1); }
static bool tisa_g_access_in4(const uint64_t *in, uint64_t *out) { (void)out; return tisa_access(in, 4); }
static bool tisa_g_access_in8(const uint64_t *in, uint64_t *out) { (void)out; return tisa_access(in, 8); }
static bool tisa_g_access_out1(const uint64_t *in, uint64_t *out) { (void)out; return !tisa_access(in, 1); }
static bool tisa_g_access_out4(const uint64_t *in, uint64_t *out) { (void)out; return !tisa_access(in, 4); }
static bool tisa_g_access_out8(const uint64_t *in, uint64_t *out) { (void)out; return !tisa_access(in, 8); }
/* in: pointer, disp, k0 .. k(w-1); k_i = pointer + disp + i (wrapping) */
static bool tisa_keys(const uint64_t *in, int w) {
    uint64_t a = in[0] + (uint64_t)(int64_t)(int32_t)(int64_t)in[1];
    for (int i = 0; i < w; i++) if (in[2 + i] != a + (uint64_t)i) return false;
    return true;
}
static bool tisa_g_load_keys1(const uint64_t *in, uint64_t *out) { (void)out; return tisa_keys(in, 1); }
static bool tisa_g_load_keys4(const uint64_t *in, uint64_t *out) { (void)out; return tisa_keys(in, 4); }
static bool tisa_g_load_keys8(const uint64_t *in, uint64_t *out) { (void)out; return tisa_keys(in, 8); }
/* in: pointer, disp, k, key; key = pointer + disp + k (wrapping) */
static bool tisa_g_store_key(const uint64_t *in, uint64_t *out) {
    (void)out;
    return in[3] == in[0] + (uint64_t)(int64_t)(int32_t)(int64_t)in[1] + in[2];
}

typedef enum {
    TFN_ADD64, TFN_SUB64, TFN_AND64, TFN_OR64, TFN_XOR64, TFN_MUL64,
    TFN_ADD32Z, TFN_SUB32Z, TFN_AND32Z, TFN_OR32Z, TFN_XOR32Z, TFN_MUL32Z,
    TFN_ADD32S, TFN_SUB32S, TFN_AND32S, TFN_OR32S, TFN_XOR32S, TFN_MUL32S,
    TFN_EQ64, TFN_NE64, TFN_ULT64, TFN_ULE64, TFN_SLT64, TFN_SLE64,
    TFN_EQ32, TFN_NE32, TFN_ULT32, TFN_ULE32, TFN_SLT32, TFN_SLE32,
    TFN_SHL64, TFN_SHRU64, TFN_SHRS64, TFN_SHL32Z, TFN_SHRU32Z, TFN_SHRS32Z, TFN_SHL32S, TFN_SHRU32S, TFN_SHRS32S,
    TFN_ZEXT32, TFN_SEXT32, TFN_LOWBIT, TFN_INC64, TFN_EXTRACT, TFN_ADDR_INDEX, TFN_ADDR_NOIDX,
    TFN_PACK1, TFN_PACK4, TFN_PACK8, TFN_BYTE_OF,
    TFN_G_IS_ZERO, TFN_G_IS_ONE, TFN_G_IS_BOOL, TFN_G_ABOVE_ONE, TFN_G_VALID_BYTE, TFN_G_VALID_U32Z, TFN_G_VALID_I32S,
    TFN_G_EQ, TFN_G_NE, TFN_G_ULT, TFN_G_ULE, TFN_G_FUEL_AVAILABLE, TFN_G_FUEL_EXHAUSTED,
    TFN_G_ADDR_ADMITTED, TFN_G_ADDR_REFUSED, TFN_G_ADDR_NOIDX_ADMITTED, TFN_G_ADDR_NOIDX_REFUSED,
    TFN_G_ACCESS_IN1, TFN_G_ACCESS_IN4, TFN_G_ACCESS_IN8, TFN_G_ACCESS_OUT1, TFN_G_ACCESS_OUT4, TFN_G_ACCESS_OUT8,
    TFN_G_LOAD_KEYS1, TFN_G_LOAD_KEYS4, TFN_G_LOAD_KEYS8, TFN_G_STORE_KEY,
    TFN_COUNT
} TisaFnSlot;

typedef struct {
    const char *name;       /* the registry name: the contract statement the hash stands for */
    const char *statement;  /* the Lean definition it is meant to compute (provenance) */
    uint8_t     kind, nin, nout;
    TcFn        fn;
    const char *meaning;    /* in -> out, or the predicate */
} TisaFnDecl;

#define SCALAR "Mettapedia.Machines.TIsa.Scalar.evaluate"        /* 64-bit words */
#define SCALAR32 "Mettapedia.Machines.TIsa.Scalar.evaluate32"    /* low 32 bits, zero- or sign-extended */
#define NORM "Mettapedia.Machines.TIsa.ScalarType.normalize"
#define OPD(nm, nin, stmt, mean) { "tisa.op." #nm, stmt, TC_FN_OP, nin, 1, tisa_fn_##nm, mean }
#define NATIVE_OPD(nm, nin, stmt, mean) { "tisa.op." #nm, stmt, TC_FN_OP, nin, 1, tisa_native_##nm, mean }
#define GD(nm, nin, stmt, mean) { "tisa.guard." #nm, stmt, TC_FN_GUARD, nin, 0, tisa_g_##nm, mean }
static const TisaFnDecl TISA_FNS[TFN_COUNT] = {
    [TFN_ADD64] = NATIVE_OPD(add64, 2, SCALAR, "in=[x,y] out=[(x+y) mod 2^64]"),
    [TFN_SUB64] = NATIVE_OPD(sub64, 2, SCALAR, "in=[x,y] out=[(x-y) mod 2^64]"),
    [TFN_AND64] = NATIVE_OPD(and64, 2, SCALAR, "in=[x,y] out=[x AND y]"),
    [TFN_OR64]  = NATIVE_OPD(or64, 2, SCALAR, "in=[x,y] out=[x OR y]"),
    [TFN_XOR64] = NATIVE_OPD(xor64, 2, SCALAR, "in=[x,y] out=[x XOR y]"),
    [TFN_MUL64] = OPD(mul64, 2, SCALAR, "in=[x,y] out=[(x*y) mod 2^64]"),
    [TFN_ADD32Z] = OPD(add32z, 2, SCALAR32, "in=[x,y] out=[(x+y) mod 2^32]"),
    [TFN_SUB32Z] = OPD(sub32z, 2, SCALAR32, "in=[x,y] out=[(x-y) mod 2^32]"),
    [TFN_AND32Z] = OPD(and32z, 2, SCALAR32, "in=[x,y] out=[(x AND y) mod 2^32]"),
    [TFN_OR32Z]  = OPD(or32z, 2, SCALAR32, "in=[x,y] out=[(x OR y) mod 2^32]"),
    [TFN_XOR32Z] = OPD(xor32z, 2, SCALAR32, "in=[x,y] out=[(x XOR y) mod 2^32]"),
    [TFN_MUL32Z] = OPD(mul32z, 2, SCALAR32, "in=[x,y] out=[(x*y) mod 2^32]"),
    [TFN_ADD32S] = OPD(add32s, 2, SCALAR32, "in=[x,y] out=[sext32((x+y) mod 2^32)]"),
    [TFN_SUB32S] = OPD(sub32s, 2, SCALAR32, "in=[x,y] out=[sext32((x-y) mod 2^32)]"),
    [TFN_AND32S] = OPD(and32s, 2, SCALAR32, "in=[x,y] out=[sext32((x AND y) mod 2^32)]"),
    [TFN_OR32S]  = OPD(or32s, 2, SCALAR32, "in=[x,y] out=[sext32((x OR y) mod 2^32)]"),
    [TFN_XOR32S] = OPD(xor32s, 2, SCALAR32, "in=[x,y] out=[sext32((x XOR y) mod 2^32)]"),
    [TFN_MUL32S] = OPD(mul32s, 2, SCALAR32, "in=[x,y] out=[sext32((x*y) mod 2^32)]"),
    [TFN_EQ64]  = OPD(eq64, 2, SCALAR, "in=[x,y] out=[x=y ? 1 : 0]"),
    [TFN_NE64]  = OPD(ne64, 2, SCALAR, "in=[x,y] out=[x!=y ? 1 : 0]"),
    [TFN_ULT64] = OPD(ult64, 2, SCALAR, "in=[x,y] out=[x<y unsigned ? 1 : 0]"),
    [TFN_ULE64] = OPD(ule64, 2, SCALAR, "in=[x,y] out=[x<=y unsigned ? 1 : 0]"),
    [TFN_SLT64] = OPD(slt64, 2, SCALAR, "in=[x,y] out=[x<y signed 64-bit ? 1 : 0]"),
    [TFN_SLE64] = OPD(sle64, 2, SCALAR, "in=[x,y] out=[x<=y signed 64-bit ? 1 : 0]"),
    [TFN_EQ32]  = OPD(eq32, 2, SCALAR32, "in=[x,y] out=[low32(x)=low32(y) ? 1 : 0]"),
    [TFN_NE32]  = OPD(ne32, 2, SCALAR32, "in=[x,y] out=[low32(x)!=low32(y) ? 1 : 0]"),
    [TFN_ULT32] = OPD(ult32, 2, SCALAR32, "in=[x,y] out=[low32(x)<low32(y) unsigned ? 1 : 0]"),
    [TFN_ULE32] = OPD(ule32, 2, SCALAR32, "in=[x,y] out=[low32(x)<=low32(y) unsigned ? 1 : 0]"),
    [TFN_SLT32] = OPD(slt32, 2, SCALAR32, "in=[x,y] out=[low32(x)<low32(y) signed 32-bit ? 1 : 0]"),
    [TFN_SLE32] = OPD(sle32, 2, SCALAR32, "in=[x,y] out=[low32(x)<=low32(y) signed 32-bit ? 1 : 0]"),
    [TFN_SHL64]   = OPD(shl64, 2, SCALAR, "in=[x,n] out=[(x << n) mod 2^64]; no value for n >= 64"),
    [TFN_SHRU64]  = OPD(shru64, 2, SCALAR, "in=[x,n] out=[x >> n logical]; no value for n >= 64"),
    [TFN_SHRS64]  = OPD(shrs64, 2, SCALAR, "in=[x,n] out=[x >> n arithmetic, 64-bit]; no value for n >= 64"),
    [TFN_SHL32Z]  = OPD(shl32z, 2, SCALAR32, "in=[x,n] out=[(low32(x) << n) mod 2^32]; no value for n >= 32"),
    [TFN_SHRU32Z] = OPD(shru32z, 2, SCALAR32, "in=[x,n] out=[low32(x) >> n logical]; no value for n >= 32"),
    [TFN_SHRS32Z] = OPD(shrs32z, 2, SCALAR32, "in=[x,n] out=[(low32(x) >> n arithmetic, 32-bit) mod 2^32]; no value for n >= 32"),
    [TFN_SHL32S]  = OPD(shl32s, 2, SCALAR32, "in=[x,n] out=[sext32((low32(x) << n) mod 2^32)]; no value for n >= 32"),
    [TFN_SHRU32S] = OPD(shru32s, 2, SCALAR32, "in=[x,n] out=[sext32(low32(x) >> n logical)]; no value for n >= 32"),
    [TFN_SHRS32S] = OPD(shrs32s, 2, SCALAR32, "in=[x,n] out=[sext32(low32(x) >> n arithmetic, 32-bit)]; no value for n >= 32"),
    [TFN_ZEXT32] = OPD(zext32, 1, NORM, "in=[x] out=[x mod 2^32]"),
    [TFN_SEXT32] = OPD(sext32, 1, NORM, "in=[x] out=[sext32(x mod 2^32)]"),
    [TFN_LOWBIT] = OPD(lowbit, 1, NORM, "in=[x] out=[x AND 1]"),
    [TFN_INC64]  = OPD(inc64, 1, "Mettapedia.Machines.TIsa.Control.Loop.latch", "in=[x] out=[(x+1) mod 2^64]"),
    [TFN_EXTRACT] = OPD(extract, 3, SCALAR, "in=[x,lsb,w] out=[(x >> lsb) mod 2^w]; no value unless 1<=w and lsb+w<=64"),
    [TFN_ADDR_INDEX] = OPD(addr_index, 4, SCALAR,
                           "in=[p,i,s,d] out=[(p + (i << s) + sext32(d)) mod 2^64]; no value for s > 3"),
    [TFN_ADDR_NOIDX] = OPD(addr_noidx, 2, SCALAR, "in=[p,d] out=[(p + sext32(d)) mod 2^64]"),
    [TFN_PACK1] = OPD(pack1, 1, "Mettapedia.Machines.TIsa.packBytes", "in=[b0] out=[b0]; no value unless b0 <= 255"),
    [TFN_PACK4] = OPD(pack4, 4, "Mettapedia.Machines.TIsa.packBytes", "in=[b0..b3] out=[sum b_i << 8i]; no value unless each b_i <= 255"),
    [TFN_PACK8] = OPD(pack8, 8, "Mettapedia.Machines.TIsa.packBytes", "in=[b0..b7] out=[sum b_i << 8i]; no value unless each b_i <= 255"),
    [TFN_BYTE_OF] = OPD(byte_of, 2, "Mettapedia.Machines.TIsa.unpackBytes", "in=[x,k] out=[(x >> 8k) AND 255]; no value for k > 7"),
    [TFN_G_IS_ZERO]   = GD(is_zero, 1, "Mettapedia.Machines.TIsa.Control.Branch.target?", "x = 0"),
    [TFN_G_IS_ONE]    = GD(is_one, 1, "Mettapedia.Machines.TIsa.Control.Branch.target?", "x = 1"),
    [TFN_G_IS_BOOL]   = GD(is_bool, 1, "Mettapedia.Machines.TIsa.ScalarType.ValidWord", "x <= 1"),
    [TFN_G_ABOVE_ONE] = GD(above_one, 1, "Mettapedia.Machines.TIsa.ScalarType.ValidWord", "x > 1"),
    [TFN_G_VALID_BYTE] = GD(valid_byte, 1, "Mettapedia.Machines.TIsa.Memory.readByteWords?", "x <= 255"),
    [TFN_G_VALID_U32Z] = GD(valid_u32z, 1, "Mettapedia.Machines.TIsa.ScalarType.ValidWord", "x < 2^32"),
    [TFN_G_VALID_I32S] = GD(valid_i32s, 1, "Mettapedia.Machines.TIsa.ScalarType.ValidWord", "x = sext32(x mod 2^32)"),
    [TFN_G_EQ]  = GD(eq, 2, "Mettapedia.Machines.TIsa.Control.Loop.headerTarget", "x = y"),
    [TFN_G_NE]  = GD(ne, 2, "Mettapedia.Machines.TIsa.frameLayout", "x != y"),
    [TFN_G_ULT] = GD(ult, 2, "Mettapedia.Machines.TIsa.Control.Loop.headerTarget", "x < y unsigned"),
    [TFN_G_ULE] = GD(ule, 2, "Mettapedia.Machines.TIsa.Control.Loop.headerTarget", "x <= y unsigned"),
    [TFN_G_FUEL_AVAILABLE] = GD(fuel_available, 2, "Mettapedia.Machines.TIsa.fuelAvailable", "in=[budget,used]: budget = 0 or used < budget"),
    [TFN_G_FUEL_EXHAUSTED] = GD(fuel_exhausted, 2, "Mettapedia.Machines.TIsa.fuelAvailable", "in=[budget,used]: budget != 0 and used >= budget"),
    [TFN_G_ADDR_ADMITTED] = GD(addr_admitted, 6, "Mettapedia.Machines.TIsa.checkedAddress?",
        "in=[p,i,base,len,s,d]: s <= 3, base <= p <= base+len, i << s does not overflow, p-base+(i << s) <= len, "
        "p-base+(i << s)+sext32(d) lies in [0,len], and neither p+(i << s) nor p+(i << s)+sext32(d) wraps "
        "(tisa_eval_recipe_instr_guard and tisa_scalar_eval of ADDR)"),
    [TFN_G_ADDR_REFUSED] = GD(addr_refused, 6, "Mettapedia.Machines.TIsa.checkedAddress?", "in=[p,i,base,len,s,d]: not addr_admitted"),
    [TFN_G_ADDR_NOIDX_ADMITTED] = GD(addr_noidx_admitted, 4, "Mettapedia.Machines.TIsa.checkedAddress?",
        "in=[p,base,len,d]: addr_admitted(p,0,base,len,0,d)"),
    [TFN_G_ADDR_NOIDX_REFUSED] = GD(addr_noidx_refused, 4, "Mettapedia.Machines.TIsa.checkedAddress?", "in=[p,base,len,d]: not addr_noidx_admitted"),
    [TFN_G_ACCESS_IN1] = GD(access_in1, 4, "Mettapedia.Machines.TIsa.Memory.access?", "in=[base,len,p,d]: base <= p <= base+len and the 1 byte at p+sext32(d) lies in [base,base+len) (tisa_check_mem_offset_words)"),
    [TFN_G_ACCESS_IN4] = GD(access_in4, 4, "Mettapedia.Machines.TIsa.Memory.access?", "in=[base,len,p,d]: base <= p <= base+len and the 4 bytes at p+sext32(d) lie in [base,base+len) (tisa_check_mem_offset_words)"),
    [TFN_G_ACCESS_IN8] = GD(access_in8, 4, "Mettapedia.Machines.TIsa.Memory.access?", "in=[base,len,p,d]: base <= p <= base+len and the 8 bytes at p+sext32(d) lie in [base,base+len) (tisa_check_mem_offset_words)"),
    [TFN_G_ACCESS_OUT1] = GD(access_out1, 4, "Mettapedia.Machines.TIsa.Memory.access?", "in=[base,len,p,d]: not access_in1"),
    [TFN_G_ACCESS_OUT4] = GD(access_out4, 4, "Mettapedia.Machines.TIsa.Memory.access?", "in=[base,len,p,d]: not access_in4"),
    [TFN_G_ACCESS_OUT8] = GD(access_out8, 4, "Mettapedia.Machines.TIsa.Memory.access?", "in=[base,len,p,d]: not access_in8"),
    [TFN_G_LOAD_KEYS1] = GD(load_keys1, 3, "Mettapedia.Machines.TIsa.Memory.byteKeys", "in=[p,d,k0]: k0 = p+sext32(d) mod 2^64"),
    [TFN_G_LOAD_KEYS4] = GD(load_keys4, 6, "Mettapedia.Machines.TIsa.Memory.byteKeys", "in=[p,d,k0..k3]: k_i = p+sext32(d)+i mod 2^64"),
    [TFN_G_LOAD_KEYS8] = GD(load_keys8, 10, "Mettapedia.Machines.TIsa.Memory.byteKeys", "in=[p,d,k0..k7]: k_i = p+sext32(d)+i mod 2^64"),
    [TFN_G_STORE_KEY] = GD(store_key, 4, "Mettapedia.Machines.TIsa.Memory.byteKeys", "in=[p,d,k,key]: key = p+sext32(d)+k mod 2^64"),
};
#undef OPD
#undef NATIVE_OPD
#undef GD

/* The native entries: each image's expected bytes and its proved SHA-256 (tisa/native_alu/SHA256SUMS,
   the digests that came with the proofs; tisa/native_alu/check.sh holds every build to them). */
#define TISA_NATIVE_LEN 34
static const struct { uint8_t slot; const uint8_t *expected; const char *image_sha256; } TISA_NATIVE[] = {
    { TFN_ADD64, tisa_native_add64_expected, "8bd7d062bf7f730f611796bd212315ba680feb8984f5ec6081b76211c53f24a9" },
    { TFN_SUB64, tisa_native_sub64_expected, "e2cfe0775fa459842ea3140031fb64f17d40eaf806cf5e615907f2dd96dca279" },
    { TFN_AND64, tisa_native_and64_expected, "2a22ecb14ea43bc7e9810ca532682a4837ae7b5d09613d6bb9a7b388c25da71e" },
    { TFN_OR64,  tisa_native_or64_expected,  "eff126e2b53dc45dcb4ecbfb8b7f2b10a320fc1e09e096392db3f2b20bcf0a93" },
    { TFN_XOR64, tisa_native_xor64_expected, "78db2ff38f0480ac82acd15769322742ea83f5c7eb5b2cf02fc0030a35242329" },
};
#define TISA_NNATIVE (int)(sizeof TISA_NATIVE / sizeof TISA_NATIVE[0])
/* The native entry of slot, or -1 for a C entry. */
static int tisa_native_of(int slot) {
    for (int i = 0; i < TISA_NNATIVE; i++) if (TISA_NATIVE[i].slot == slot) return i;
    return -1;
}
/* Whether the bytes at fn are native entry k's image. */
static bool tisa_native_bytes_ok(int k, TcFn fn) {
    return memcmp((const void *)(uintptr_t)fn, TISA_NATIVE[k].expected, TISA_NATIVE_LEN) == 0;
}
#undef SCALAR
#undef SCALAR32
#undef NORM

/* The contract text of a registered function; its SHA-256 is the registry's contract hash. */
static int tisa_fn_contract(int slot, char *buf, size_t cap) {
    const TisaFnDecl *d = &TISA_FNS[slot];
    return snprintf(buf, cap, "%s/1 %s nin=%u nout=%u: %s. Layout: TcFn(const uint64_t *in, uint64_t *out) -> bool, "
                    "SysV RDI=in RSI=out AL=result%s. Statement: %s. Trusted C until a proved native image replaces it.",
                    d->name, d->kind == TC_FN_OP ? "operation" : "guard", (unsigned)d->nin, (unsigned)d->nout, d->meaning,
                    d->kind == TC_FN_OP ? " (true: out[0] written; false: no value)" : " (true: holds)", d->statement);
}

/* SHA-256 (FIPS 180-4), for the contract hashes. */
static void tisa_sha256(const uint8_t *data, size_t len, uint8_t digest[32]) {
    static const uint32_t K[64] = {
        0x428a2f98u, 0x71374491u, 0xb5c0fbcfu, 0xe9b5dba5u, 0x3956c25bu, 0x59f111f1u, 0x923f82a4u, 0xab1c5ed5u,
        0xd807aa98u, 0x12835b01u, 0x243185beu, 0x550c7dc3u, 0x72be5d74u, 0x80deb1feu, 0x9bdc06a7u, 0xc19bf174u,
        0xe49b69c1u, 0xefbe4786u, 0x0fc19dc6u, 0x240ca1ccu, 0x2de92c6fu, 0x4a7484aau, 0x5cb0a9dcu, 0x76f988dau,
        0x983e5152u, 0xa831c66du, 0xb00327c8u, 0xbf597fc7u, 0xc6e00bf3u, 0xd5a79147u, 0x06ca6351u, 0x14292967u,
        0x27b70a85u, 0x2e1b2138u, 0x4d2c6dfcu, 0x53380d13u, 0x650a7354u, 0x766a0abbu, 0x81c2c92eu, 0x92722c85u,
        0xa2bfe8a1u, 0xa81a664bu, 0xc24b8b70u, 0xc76c51a3u, 0xd192e819u, 0xd6990624u, 0xf40e3585u, 0x106aa070u,
        0x19a4c116u, 0x1e376c08u, 0x2748774cu, 0x34b0bcb5u, 0x391c0cb3u, 0x4ed8aa4au, 0x5b9cca4fu, 0x682e6ff3u,
        0x748f82eeu, 0x78a5636fu, 0x84c87814u, 0x8cc70208u, 0x90befffau, 0xa4506cebu, 0xbef9a3f7u, 0xc67178f2u
    };
    uint32_t h[8] = { 0x6a09e667u, 0xbb67ae85u, 0x3c6ef372u, 0xa54ff53au,
                      0x510e527fu, 0x9b05688cu, 0x1f83d9abu, 0x5be0cd19u };
    uint8_t block[64];
    uint64_t total = (uint64_t)len * 8u;
    size_t pos = 0;
    bool padded = false, done = false;
    while (!done) {
        size_t n = 0;
        while (n < 64 && pos < len) block[n++] = data[pos++];
        if (n < 64 && !padded) { block[n++] = 0x80u; padded = true; }
        if (padded && n <= 56) {
            while (n < 56) block[n++] = 0;
            for (int i = 0; i < 8; i++) block[56 + i] = (uint8_t)(total >> (56 - 8 * i));
            n = 64; done = true;
        }
        while (n < 64) block[n++] = 0;
        uint32_t w[64];
        for (int i = 0; i < 16; i++)
            w[i] = (uint32_t)block[4 * i] << 24 | (uint32_t)block[4 * i + 1] << 16 |
                   (uint32_t)block[4 * i + 2] << 8 | (uint32_t)block[4 * i + 3];
        for (int i = 16; i < 64; i++) {
            uint32_t s0 = (w[i - 15] >> 7 | w[i - 15] << 25) ^ (w[i - 15] >> 18 | w[i - 15] << 14) ^ (w[i - 15] >> 3);
            uint32_t s1 = (w[i - 2] >> 17 | w[i - 2] << 15) ^ (w[i - 2] >> 19 | w[i - 2] << 13) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16] + s0 + w[i - 7] + s1;
        }
        uint32_t a = h[0], b = h[1], c = h[2], d = h[3], e = h[4], f = h[5], g = h[6], hh = h[7];
        for (int i = 0; i < 64; i++) {
            uint32_t S1 = (e >> 6 | e << 26) ^ (e >> 11 | e << 21) ^ (e >> 25 | e << 7);
            uint32_t t1 = hh + S1 + ((e & f) ^ (~e & g)) + K[i] + w[i];
            uint32_t S0 = (a >> 2 | a << 30) ^ (a >> 13 | a << 19) ^ (a >> 22 | a << 10);
            uint32_t t2 = S0 + ((a & b) ^ (a & c) ^ (b & c));
            hh = g; g = f; f = e; e = d + t1; d = c; c = b; b = a; a = t1 + t2;
        }
        h[0] += a; h[1] += b; h[2] += c; h[3] += d; h[4] += e; h[5] += f; h[6] += g; h[7] += hh;
    }
    for (int i = 0; i < 8; i++)
        for (int j = 0; j < 4; j++) digest[4 * i + j] = (uint8_t)(h[i] >> (24 - 8 * j));
}

/* ---- 6b. Forms and their cases ----
   A form is what one point's rules fix structurally: the recipe kind, opcode, operation, result
   type and width, the cells it reads (roles k1..k4, each of a fixed kind), the destination's kind,
   and its cases. Holes are named symbolically here and numbered per rule. */

enum {
    HZ,                                   /* the constant word 0 (a source of out only) */
    HP, HPC, HIID, HIMM, HDISP, HA1, HA2, HNEXT, HALT, HFAIL,
    HV1, HV2, HV3, HV4,                   /* the role cells' values */
    HB0, HK0 = HB0 + 8,                   /* byte values, byte keys */
    HW = HK0 + 8,                         /* an intermediate operation output */
    HOUT,                                 /* the value the step writes */
    HDK,                                  /* a store's destination key (matched, then checked) */
    HNH
};

typedef struct { uint8_t slot, nin, in[13]; } TisaCall;
typedef struct {
    uint8_t  nguard, nop, nbytes;         /* nbytes: byte cells the case keeps (a load inside its region) */
    TisaCall guard[3], op[2];             /* op[0] -> HOUT, or op[0] -> HW and op[1] -> HOUT */
    uint8_t  out, next, status;           /* out: HOUT, HZ or a matched hole; next: HNEXT, HALT or HFAIL;
                                             status: TISA_CASE_UPDATE (writes the destination) or _CTRL */
} TisaCase;
typedef struct {
    uint64_t id;                          /* the Instr's form word */
    uint8_t  roles, kind[4], dkind;
    bool     dyn_dst;                     /* the destination is a region byte at a computed address */
    uint8_t  width;                       /* bytes of a region load or store, 0 otherwise */
    int16_t  canon;                       /* the guard checking the destination word's type, or -1 */
    uint8_t  ncase;
    TisaCase cs[5];
} TisaForm;

static TisaCall tisa_call(uint8_t slot, int nin, const uint8_t *in) {
    TisaCall c;
    memset(&c, 0, sizeof c);
    c.slot = slot; c.nin = (uint8_t)nin;
    for (int i = 0; i < nin; i++) c.in[i] = in[i];
    return c;
}
#define CALL(slot, ...) tisa_call((slot), (int)sizeof((uint8_t[]){ __VA_ARGS__ }), (uint8_t[]){ __VA_ARGS__ })
static TisaCase *tisa_case(TisaForm *f, uint8_t out, uint8_t next, uint8_t status) {
    TisaCase *c = &f->cs[f->ncase++];
    memset(c, 0, sizeof *c);
    c->out = out; c->next = next; c->status = status;
    return c;
}
static void tisa_guard(TisaCase *c, TisaCall g) { c->guard[c->nguard++] = g; }
static void tisa_op(TisaCase *c, TisaCall o) { c->op[c->nop++] = o; }
/* A value normalised to a result type: the value itself, or an operation into HOUT. */
static uint8_t tisa_norm(TisaCase *c, TcIsaValType ty, uint8_t v) {
    switch (ty) {
        case TISA_TYPE_U32Z: tisa_op(c, CALL(TFN_ZEXT32, v)); return HOUT;
        case TISA_TYPE_I32S: tisa_op(c, CALL(TFN_SEXT32, v)); return HOUT;
        case TISA_TYPE_BOOL: tisa_op(c, CALL(TFN_LOWBIT, v)); return HOUT;
        default:             return v;
    }
}
static int16_t tisa_canon_slot(TcIsaValType ty) {
    return ty == TISA_TYPE_U32Z ? TFN_G_VALID_U32Z : ty == TISA_TYPE_I32S ? TFN_G_VALID_I32S :
           ty == TISA_TYPE_BOOL ? TFN_G_IS_BOOL : -1;
}

/* The point's form and its Instr words (w[TI_IID] is left for the caller). false: no form, so no
   rule: the host stops at this point (no verdict), as the recipe cannot be executed. */
static bool tisa_point_form(const TcIsaProgram *prog, const TcIsaPointRecipe *rec, uint64_t frame_base,
                            TisaForm *f, uint64_t *w) {
    const TcIsaInstr *ins = &rec->instr;
    const uint8_t R = TISA_KEY_KIND_REG, F = TISA_KEY_KIND_FRAME;
    memset(f, 0, sizeof *f);
    f->canon = -1; f->dkind = TISA_KEY_KIND_NONE;
    w[TI_NEXT] = rec->next_point; w[TI_ALT] = rec->alt_point; w[TI_FAIL] = rec->fail_point;
    uint8_t variant = 0;
    TisaCase *c;
#define ROLE(j, kd, key) do { f->roles |= (uint8_t)(1u << ((j) - 1)); f->kind[(j) - 1] = (kd); w[TI_K1 + (j) - 1] = (key); } while (0)
    switch (rec->kind) {
        case TISA_RECIPE_FUEL:
            ROLE(1, F, offsetof(TcIsaRuntimeFrame, fuel_budget) / 8u);
            ROLE(2, F, offsetof(TcIsaRuntimeFrame, fuel_used) / 8u);
            f->dkind = F; w[TI_DKEY] = offsetof(TcIsaRuntimeFrame, fuel_used) / 8u;
            c = tisa_case(f, HOUT, HNEXT, TISA_CASE_UPDATE);
            tisa_guard(c, CALL(TFN_G_FUEL_AVAILABLE, HV1, HV2)); tisa_op(c, CALL(TFN_INC64, HV2));
            c = tisa_case(f, HZ, HFAIL, TISA_CASE_CTRL);
            tisa_guard(c, CALL(TFN_G_FUEL_EXHAUSTED, HV1, HV2));
            break;
        case TISA_RECIPE_INSTR: {
            TcIsaValType ty = ins->ty;
            f->dkind = R; w[TI_DKEY] = ins->dst;
            w[TI_IMM] = ins->imm64; w[TI_DISP] = (uint64_t)(int64_t)ins->disp32;
            switch (ins->op) {
                case TISA_OP_IMM:
                    f->canon = tisa_canon_slot(ty);
                    if (ty == TISA_TYPE_BOOL) {
                        c = tisa_case(f, HIMM, HNEXT, TISA_CASE_UPDATE); tisa_guard(c, CALL(TFN_G_IS_BOOL, HIMM));
                        c = tisa_case(f, HZ, HFAIL, TISA_CASE_CTRL); tisa_guard(c, CALL(TFN_G_ABOVE_ONE, HIMM));
                    } else {
                        c = tisa_case(f, 0, HNEXT, TISA_CASE_UPDATE); c->out = tisa_norm(c, ty, HIMM);
                    }
                    break;
                case TISA_OP_MOV:
                    ROLE(1, R, ins->src1);
                    f->canon = tisa_canon_slot(ty);
                    if (ty == TISA_TYPE_BOOL) {
                        c = tisa_case(f, HV1, HNEXT, TISA_CASE_UPDATE); tisa_guard(c, CALL(TFN_G_IS_BOOL, HV1));
                        c = tisa_case(f, HZ, HFAIL, TISA_CASE_CTRL); tisa_guard(c, CALL(TFN_G_ABOVE_ONE, HV1));
                    } else {
                        c = tisa_case(f, 0, HNEXT, TISA_CASE_UPDATE); c->out = tisa_norm(c, ty, HV1);
                    }
                    break;
                case TISA_OP_BIN: {
                    static const uint8_t fam[3][6] = {
                        { TFN_ADD64, TFN_SUB64, TFN_AND64, TFN_OR64, TFN_XOR64, TFN_MUL64 },
                        { TFN_ADD32Z, TFN_SUB32Z, TFN_AND32Z, TFN_OR32Z, TFN_XOR32Z, TFN_MUL32Z },
                        { TFN_ADD32S, TFN_SUB32S, TFN_AND32S, TFN_OR32S, TFN_XOR32S, TFN_MUL32S } };
                    if (ins->subop > TISA_BIN_MULLO) return false;
                    ROLE(1, R, ins->src1); ROLE(2, R, ins->src2);
                    f->canon = tisa_canon_slot(ty);
                    if (ty == TISA_TYPE_BOOL) {             /* AND, OR, XOR of booleans; anything else fails */
                        if (ins->subop != TISA_BIN_AND && ins->subop != TISA_BIN_OR && ins->subop != TISA_BIN_XOR) return false;
                        c = tisa_case(f, HOUT, HNEXT, TISA_CASE_UPDATE);
                        tisa_guard(c, CALL(TFN_G_IS_BOOL, HV1)); tisa_guard(c, CALL(TFN_G_IS_BOOL, HV2));
                        tisa_op(c, CALL(fam[0][ins->subop], HV1, HV2));
                        c = tisa_case(f, HZ, HFAIL, TISA_CASE_CTRL); tisa_guard(c, CALL(TFN_G_ABOVE_ONE, HV1));
                        c = tisa_case(f, HZ, HFAIL, TISA_CASE_CTRL);
                        tisa_guard(c, CALL(TFN_G_IS_BOOL, HV1)); tisa_guard(c, CALL(TFN_G_ABOVE_ONE, HV2));
                    } else {
                        int k = ty == TISA_TYPE_U32Z ? 1 : ty == TISA_TYPE_I32S ? 2 : ty == TISA_TYPE_U64 ? 0 : -1;
                        if (k < 0) return false;
                        c = tisa_case(f, HOUT, HNEXT, TISA_CASE_UPDATE); tisa_op(c, CALL(fam[k][ins->subop], HV1, HV2));
                    }
                    break;
                }
                case TISA_OP_SHIFT: {
                    static const uint8_t fam[3][3] = {
                        { TFN_SHL64, TFN_SHRU64, TFN_SHRS64 }, { TFN_SHL32Z, TFN_SHRU32Z, TFN_SHRS32Z },
                        { TFN_SHL32S, TFN_SHRU32S, TFN_SHRS32S } };
                    int k = ty == TISA_TYPE_U32Z ? 1 : ty == TISA_TYPE_I32S ? 2 : 0;
                    if (ins->subop > TISA_SHIFT_SHRS || ty == TISA_TYPE_BOOL || ty == TISA_TYPE_PTR || ty == TISA_TYPE_UNINIT) return false;
                    ROLE(1, R, ins->src1);
                    w[TI_A1] = ins->bit_width;
                    f->canon = tisa_canon_slot(ty);
                    c = tisa_case(f, HOUT, HNEXT, TISA_CASE_UPDATE); tisa_op(c, CALL(fam[k][ins->subop], HV1, HA1));
                    break;
                }
                case TISA_OP_EXTRACT:
                    ROLE(1, R, ins->src1);
                    w[TI_A1] = ins->scale_lg2; w[TI_A2] = ins->bit_width;
                    f->canon = tisa_canon_slot(ty);
                    c = tisa_case(f, HOUT, HNEXT, TISA_CASE_UPDATE);
                    if (ty == TISA_TYPE_U32Z || ty == TISA_TYPE_I32S || ty == TISA_TYPE_BOOL) {
                        tisa_op(c, CALL(TFN_EXTRACT, HV1, HA1, HA2));   /* into HW: the first of two operations */
                        tisa_op(c, CALL(ty == TISA_TYPE_U32Z ? TFN_ZEXT32 : ty == TISA_TYPE_I32S ? TFN_SEXT32 : TFN_LOWBIT, HW));
                    } else {
                        tisa_op(c, CALL(TFN_EXTRACT, HV1, HA1, HA2));
                    }
                    break;
                case TISA_OP_CMP: {
                    static const uint8_t fam[2][6] = {
                        { TFN_EQ64, TFN_NE64, TFN_ULT64, TFN_ULE64, TFN_SLT64, TFN_SLE64 },
                        { TFN_EQ32, TFN_NE32, TFN_ULT32, TFN_ULE32, TFN_SLT32, TFN_SLE32 } };
                    if (ins->subop > TISA_CMP_SLE) return false;
                    int k = (ty == TISA_TYPE_U32Z || ty == TISA_TYPE_I32S) ? 1 : 0;
                    ROLE(1, R, ins->src1);
                    if (ins->bit_width == 0u) ROLE(2, R, ins->src2);
                    variant = ins->bit_width != 0u;
                    f->canon = TFN_G_IS_BOOL;
                    c = tisa_case(f, HOUT, HNEXT, TISA_CASE_UPDATE);
                    tisa_op(c, CALL(fam[k][ins->subop], HV1, variant ? HIMM : HV2));
                    break;
                }
                case TISA_OP_SELECT: {
                    ROLE(1, R, ins->src1); ROLE(2, R, ins->src2); ROLE(3, R, ins->src3);
                    f->canon = tisa_canon_slot(ty);
                    for (int one = 1; one >= 0; one--) {   /* src3 = 1 chooses src1, 0 chooses src2 */
                        uint8_t v = one ? HV1 : HV2;
                        c = tisa_case(f, 0, HNEXT, TISA_CASE_UPDATE);
                        tisa_guard(c, CALL(one ? TFN_G_IS_ONE : TFN_G_IS_ZERO, HV3));
                        if (ty == TISA_TYPE_BOOL) { tisa_guard(c, CALL(TFN_G_IS_BOOL, HV1)); tisa_guard(c, CALL(TFN_G_IS_BOOL, HV2)); c->out = v; }
                        else c->out = tisa_norm(c, ty, v);
                    }
                    c = tisa_case(f, HZ, HFAIL, TISA_CASE_CTRL); tisa_guard(c, CALL(TFN_G_ABOVE_ONE, HV3));
                    if (ty == TISA_TYPE_BOOL) {
                        c = tisa_case(f, HZ, HFAIL, TISA_CASE_CTRL);
                        tisa_guard(c, CALL(TFN_G_IS_BOOL, HV3)); tisa_guard(c, CALL(TFN_G_ABOVE_ONE, HV1));
                        c = tisa_case(f, HZ, HFAIL, TISA_CASE_CTRL);
                        tisa_guard(c, CALL(TFN_G_IS_BOOL, HV3)); tisa_guard(c, CALL(TFN_G_IS_BOOL, HV1));
                        tisa_guard(c, CALL(TFN_G_ABOVE_ONE, HV2));
                    }
                    break;
                }
                case TISA_OP_ADDR: {
                    if (ins->region_id >= prog->nregions) return false;
                    uint64_t rid2 = (uint64_t)ins->region_id * 2u;
                    ROLE(1, R, ins->src1); ROLE(3, F, rid2); ROLE(4, F, rid2 + 1u);
                    w[TI_A1] = ins->scale_lg2;
                    if (ins->src2 != 0xFFu) {
                        ROLE(2, R, ins->src2);
                        c = tisa_case(f, HOUT, HNEXT, TISA_CASE_UPDATE);
                        tisa_guard(c, CALL(TFN_G_ADDR_ADMITTED, HV1, HV2, HV3, HV4, HA1, HDISP));
                        tisa_op(c, CALL(TFN_ADDR_INDEX, HV1, HV2, HA1, HDISP));
                        c = tisa_case(f, HZ, HFAIL, TISA_CASE_CTRL);
                        tisa_guard(c, CALL(TFN_G_ADDR_REFUSED, HV1, HV2, HV3, HV4, HA1, HDISP));
                    } else {
                        variant = 1;
                        c = tisa_case(f, HOUT, HNEXT, TISA_CASE_UPDATE);
                        tisa_guard(c, CALL(TFN_G_ADDR_NOIDX_ADMITTED, HV1, HV3, HV4, HDISP));
                        tisa_op(c, CALL(TFN_ADDR_NOIDX, HV1, HDISP));
                        c = tisa_case(f, HZ, HFAIL, TISA_CASE_CTRL);
                        tisa_guard(c, CALL(TFN_G_ADDR_NOIDX_REFUSED, HV1, HV3, HV4, HDISP));
                    }
                    break;
                }
                case TISA_OP_LOAD:
                    ROLE(1, R, ins->src1);
                    f->canon = tisa_canon_slot(ty);
                    if (ins->region_id == TISA_REGION_FRAME) {
                        if (ins->src1 != TISA_V0 || ins->subop != TISA_MEM_U64 || ins->disp32 < 0 ||
                            (ins->disp32 % 8) != 0 || (size_t)ins->disp32 + 8u > sizeof(TcIsaRuntimeFrame)) {
                            variant = 2;                 /* fails statically */
                            tisa_case(f, HZ, HFAIL, TISA_CASE_CTRL);
                        } else {
                            variant = 1;
                            ROLE(2, F, (uint64_t)ins->disp32 / 8u);
                            w[TI_IMM] = frame_base;      /* the frame's address */
                            c = tisa_case(f, 0, HNEXT, TISA_CASE_UPDATE);
                            tisa_guard(c, CALL(TFN_G_EQ, HV1, HIMM)); c->out = tisa_norm(c, ty, HV2);
                            c = tisa_case(f, HZ, HFAIL, TISA_CASE_CTRL); tisa_guard(c, CALL(TFN_G_NE, HV1, HIMM));
                        }
                    } else if (ins->region_id >= prog->nregions) {
                        variant = 3;                     /* fails statically */
                        tisa_case(f, HZ, HFAIL, TISA_CASE_CTRL);
                    } else {
                        uint8_t wd = ins->subop;
                        int sl = wd == TISA_MEM_U8 ? 0 : wd == TISA_MEM_U32 ? 1 : wd == TISA_MEM_U64 ? 2 : -1;
                        if (sl < 0) return false;
                        static const uint8_t in_g[3] = { TFN_G_ACCESS_IN1, TFN_G_ACCESS_IN4, TFN_G_ACCESS_IN8 };
                        static const uint8_t out_g[3] = { TFN_G_ACCESS_OUT1, TFN_G_ACCESS_OUT4, TFN_G_ACCESS_OUT8 };
                        static const uint8_t key_g[3] = { TFN_G_LOAD_KEYS1, TFN_G_LOAD_KEYS4, TFN_G_LOAD_KEYS8 };
                        static const uint8_t pack[3] = { TFN_PACK1, TFN_PACK4, TFN_PACK8 };
                        uint64_t rid2 = (uint64_t)ins->region_id * 2u;
                        ROLE(3, F, rid2); ROLE(4, F, rid2 + 1u);
                        f->width = wd;
                        c = tisa_case(f, HOUT, HNEXT, TISA_CASE_UPDATE);
                        c->nbytes = wd;
                        tisa_guard(c, CALL(in_g[sl], HV3, HV4, HV1, HDISP));
                        uint8_t kin[10] = { HV1, HDISP }, bin[8];
                        for (int b = 0; b < wd; b++) { kin[2 + b] = (uint8_t)(HK0 + b); bin[b] = (uint8_t)(HB0 + b); }
                        tisa_guard(c, tisa_call(key_g[sl], 2 + wd, kin));
                        TisaCall pk = tisa_call(pack[sl], wd, bin);
                        if (ty == TISA_TYPE_U32Z || ty == TISA_TYPE_I32S || ty == TISA_TYPE_BOOL) {
                            tisa_op(c, pk);                 /* into HW */
                            tisa_op(c, CALL(ty == TISA_TYPE_U32Z ? TFN_ZEXT32 : ty == TISA_TYPE_I32S ? TFN_SEXT32 : TFN_LOWBIT, HW));
                        } else {
                            tisa_op(c, pk);
                        }
                        c = tisa_case(f, HZ, HFAIL, TISA_CASE_CTRL); tisa_guard(c, CALL(out_g[sl], HV3, HV4, HV1, HDISP));
                    }
                    break;
                default:
                    return false;
            }
            break;
        }
        case TISA_RECIPE_STORE_BYTE: {
            uint8_t wd = rec->byte_width;
            int sl = wd == 1u ? 0 : wd == 4u ? 1 : wd == 8u ? 2 : -1;
            if (ins->region_id >= prog->nregions || sl < 0 || rec->byte_phase >= wd) return false;
            static const uint8_t in_g[3] = { TFN_G_ACCESS_IN1, TFN_G_ACCESS_IN4, TFN_G_ACCESS_IN8 };
            static const uint8_t out_g[3] = { TFN_G_ACCESS_OUT1, TFN_G_ACCESS_OUT4, TFN_G_ACCESS_OUT8 };
            uint64_t rid2 = (uint64_t)ins->region_id * 2u;
            ROLE(1, R, ins->src1); ROLE(2, R, ins->src2); ROLE(3, F, rid2); ROLE(4, F, rid2 + 1u);
            f->dkind = TISA_KEY_KIND_BYTE; f->dyn_dst = true; f->width = wd;
            w[TI_DISP] = (uint64_t)(int64_t)ins->disp32; w[TI_A1] = rec->byte_phase;
            variant = rec->byte_phase == 0u ? 0 : 1;
            c = tisa_case(f, HOUT, HNEXT, TISA_CASE_UPDATE);
            tisa_guard(c, CALL(in_g[sl], HV3, HV4, HV1, HDISP)); tisa_op(c, CALL(TFN_BYTE_OF, HV2, HA1));
            if (rec->byte_phase == 0u) {                 /* later phases cannot be outside: no case */
                c = tisa_case(f, HZ, HFAIL, TISA_CASE_CTRL); tisa_guard(c, CALL(out_g[sl], HV3, HV4, HV1, HDISP));
            }
            break;
        }
        case TISA_RECIPE_BRANCH:
            ROLE(1, R, rec->cond_reg);
            c = tisa_case(f, HZ, HNEXT, TISA_CASE_CTRL); tisa_guard(c, CALL(TFN_G_IS_ONE, HV1));
            c = tisa_case(f, HZ, HALT, TISA_CASE_CTRL); tisa_guard(c, CALL(TFN_G_IS_ZERO, HV1));
            c = tisa_case(f, HZ, HFAIL, TISA_CASE_CTRL); tisa_guard(c, CALL(TFN_G_ABOVE_ONE, HV1));
            break;
        case TISA_RECIPE_LOOP_ENTRY:
            ROLE(1, R, rec->bound_reg);
            f->dkind = R; w[TI_DKEY] = rec->idx_reg; w[TI_A1] = rec->max_iters;
            c = tisa_case(f, HZ, HNEXT, TISA_CASE_UPDATE); tisa_guard(c, CALL(TFN_G_ULE, HV1, HA1));
            c = tisa_case(f, HZ, HFAIL, TISA_CASE_CTRL); tisa_guard(c, CALL(TFN_G_ULT, HA1, HV1));
            break;
        case TISA_RECIPE_LOOP_HEADER:
            ROLE(1, R, rec->idx_reg); ROLE(2, R, rec->bound_reg);
            w[TI_A1] = rec->max_iters;
            c = tisa_case(f, HZ, HNEXT, TISA_CASE_CTRL);
            tisa_guard(c, CALL(TFN_G_ULE, HV2, HA1)); tisa_guard(c, CALL(TFN_G_ULT, HV1, HV2));
            c = tisa_case(f, HZ, HALT, TISA_CASE_CTRL);
            tisa_guard(c, CALL(TFN_G_ULE, HV2, HA1)); tisa_guard(c, CALL(TFN_G_EQ, HV1, HV2));
            c = tisa_case(f, HZ, HFAIL, TISA_CASE_CTRL); tisa_guard(c, CALL(TFN_G_ULT, HA1, HV2));
            c = tisa_case(f, HZ, HFAIL, TISA_CASE_CTRL);
            tisa_guard(c, CALL(TFN_G_ULE, HV2, HA1)); tisa_guard(c, CALL(TFN_G_ULT, HV2, HV1));
            break;
        case TISA_RECIPE_LOOP_LATCH:
            ROLE(1, R, rec->idx_reg); ROLE(2, R, rec->bound_reg);
            f->dkind = R; w[TI_DKEY] = rec->idx_reg; w[TI_A1] = rec->max_iters;
            c = tisa_case(f, HOUT, HNEXT, TISA_CASE_UPDATE);
            tisa_guard(c, CALL(TFN_G_ULE, HV2, HA1)); tisa_guard(c, CALL(TFN_G_ULT, HV1, HV2));
            tisa_op(c, CALL(TFN_INC64, HV1));
            c = tisa_case(f, HZ, HFAIL, TISA_CASE_CTRL); tisa_guard(c, CALL(TFN_G_ULT, HA1, HV2));
            c = tisa_case(f, HZ, HFAIL, TISA_CASE_CTRL);
            tisa_guard(c, CALL(TFN_G_ULE, HV2, HA1)); tisa_guard(c, CALL(TFN_G_ULE, HV2, HV1));
            break;
        case TISA_RECIPE_FINALIZE_STATUS:
        case TISA_RECIPE_FINALIZE_RETVAL: {
            bool status = rec->kind == TISA_RECIPE_FINALIZE_STATUS, reg = rec->ret_reg < TISA_NUM_VREGS;
            f->dkind = F;
            w[TI_DKEY] = status ? offsetof(TcIsaRuntimeFrame, status) / 8u : offsetof(TcIsaRuntimeFrame, ret_val) / 8u;
            w[TI_A1] = (uint64_t)rec->outcome;
            if (reg) ROLE(1, R, rec->ret_reg);
            variant = reg;
            tisa_case(f, (!status && reg) ? HV1 : HA1, HNEXT, TISA_CASE_UPDATE);
            break;
        }
        default:
            return false;
    }
#undef ROLE
    /* the form's identity: the recipe kind, the opcode, operation and type of an instruction, the variant */
    f->id = (uint64_t)rec->kind | (uint64_t)variant << 32;
    if (rec->kind == TISA_RECIPE_INSTR || rec->kind == TISA_RECIPE_STORE_BYTE)
        f->id |= (uint64_t)ins->op << 8 | (uint64_t)ins->subop << 16 | (uint64_t)ins->ty << 24;
    w[TI_FORM] = f->id;
    w[TI_DKIND] = f->dkind == TISA_KEY_KIND_NONE ? 0u : f->dkind;
    if (f->dkind == TISA_KEY_KIND_NONE || f->dyn_dst) w[TI_DKEY] = 0;
    return true;
}
#undef CALL

/* ---- 6c. The hosted activation ---- */

/* Test seams for the admission controls (tisa/admission/); production passes none. */
typedef struct {
    int      fault_slot;        /* a TisaFnSlot whose registered callback is replaced, or -1 */
    TcFn     fault_fn;
    bool     dup_instr;         /* post a second Instr at dup_pc before the uniqueness check */
    uint32_t dup_pc;
    bool     dup_ctrl;          /* post a second control cell */
    bool     dup_reg;           /* post a second cell for register dup_reg_idx holding dup_reg_val */
    uint8_t  dup_reg_idx;
    uint64_t dup_reg_val;
    bool     skip_validation;   /* leave such duplicates on the sealed board (matching controls) */
} TcIsaHostedOptions;

typedef struct {
    int      form;              /* index into the activation's forms, or -1: no rule (the host stops) */
    uint8_t  amask;             /* roles whose cell is the destination cell (same kind and key) */
    uint64_t w[TI_N];           /* the Instr words */
    Occ      instr;
} TisaPoint;

#define TISA_MAX_FORMS 96
typedef struct {
    const TcIsaProgram       *prog;
    const TcIsaRecipeTable   *rt;
    const TcIsaHostedOptions *opt;
    uint64_t            frame_base_addr;
    uint16_t            s_word, s_cell, s_instr;
    int                 c_cell, c_instr;
    int                 fn[TFN_COUNT];
    int                 nforms;
    TisaForm            forms[TISA_MAX_FORMS];
    int16_t             r_step[TISA_MAX_FORMS][5][16];  /* STEP rule by form, case and (writing cases) alias mask */
    TisaPoint          *pt;
    Occ                 ctrl_occ;
    Occ                 reg_occ[TISA_NUM_VREGS];
    Occ                 frame_occ[sizeof(TcIsaRuntimeFrame) / 8];
    Occ                *byte_occ[TISA_MAX_REGIONS];
    uint64_t            region_base[TISA_MAX_REGIONS];
    size_t              byte_len[TISA_MAX_REGIONS];
    Occ                 extra_occ[4];                /* duplicates posted by a test seam */
    int                 nextra;
    uint64_t            fires;                       /* STEP firings: one per executed point */
    uint32_t            occ_allocs, max_occs;        /* cell occurrences made, and their budget */
} TcIsaHostedCtx;

static inline Term tisa_w(const TcIsaHostedCtx *h, uint64_t v) { return tc_name(h->s_word, v); }

static Occ tisa_post_cell(TcIsaHostedCtx *h, uint8_t key_kind, uint64_t key, uint64_t val) {
    if (h->occ_allocs >= h->max_occs) return 0;
    Term args[3] = { tisa_w(h, key_kind), tisa_w(h, key), tisa_w(h, val) };
    if (!args[0] || !args[1] || !args[2]) return 0;
    Term app = tc_app(h->c_cell, args);
    Occ o = app ? tc_post(TISA_SPACE_STATE, app) : 0;
    if (o) h->occ_allocs++;
    return o;
}

/* The words of a live fact made with constructor con (each argument a word). */
static bool tisa_fact_words(Occ occ, int con, int arity, uint64_t *out) {
    if (!occ || !tc_alive(occ) || arity > TI_N) return false;
    uint8_t kind = 0; uint32_t head = 0; int ar = 0; const Term *args = NULL;
    tc_node(tc_term(occ), &kind, &head, &ar, &args);
    if (kind != K_APP || (int)head != con || ar != arity) return false;
    for (int i = 0; i < ar; i++) out[i] = tc_name_id(args[i]);
    return true;
}
static bool tisa_tcalc_read_cell_full(const TcIsaHostedCtx *h, Occ occ, uint8_t *out_kind, uint64_t *out_key, uint64_t *out_word) {
    uint64_t w[3];
    if (!tisa_fact_words(occ, h->c_cell, 3, w) || w[0] > TISA_KEY_KIND_FRAME) return false;
    if (out_kind) *out_kind = (uint8_t)w[0];
    if (out_key) *out_key = w[1];
    if (out_word) *out_word = w[2];
    return true;
}
static bool tisa_tcalc_read_cell_word(const TcIsaHostedCtx *h, Occ occ, uint64_t *out_word) {
    return tisa_tcalc_read_cell_full(h, occ, NULL, NULL, out_word);
}

/* The tracked occurrence of the cell (kind, key); bytes of overlapping regions share one cell. */
static Occ *tisa_cell_slot(TcIsaHostedCtx *h, uint8_t kind, uint64_t key) {
    switch (kind) {
        case TISA_KEY_KIND_REG:   return key < TISA_NUM_VREGS ? &h->reg_occ[key] : NULL;
        case TISA_KEY_KIND_FRAME: return key < sizeof(TcIsaRuntimeFrame) / 8u ? &h->frame_occ[key] : NULL;
        case TISA_KEY_KIND_BYTE:
            for (uint8_t rid = 0; rid < h->prog->nregions; rid++)
                if (h->byte_occ[rid] && key >= h->region_base[rid] && key - h->region_base[rid] < h->byte_len[rid])
                    return &h->byte_occ[rid][key - h->region_base[rid]];
            return NULL;
        default: return NULL;
    }
}
static void tisa_cell_moved(TcIsaHostedCtx *h, uint8_t kind, uint64_t key, Occ from, Occ to) {
    if (kind != TISA_KEY_KIND_BYTE) { Occ *s = tisa_cell_slot(h, kind, key); if (s) *s = to; return; }
    for (uint8_t rid = 0; rid < h->prog->nregions; rid++)
        if (h->byte_occ[rid] && key >= h->region_base[rid] && key - h->region_base[rid] < h->byte_len[rid] &&
            h->byte_occ[rid][key - h->region_base[rid]] == from)
            h->byte_occ[rid][key - h->region_base[rid]] = to;
}

/* ---- 6d. The rules: installed for the forms a program uses, before the seal ---- */

typedef struct {
    int n;
    int sym[HNH];               /* the hole of each symbolic name, or -1 */
    int DKEY, OLD, K[4];
} TisaHoles;

static int tisa_hole(TisaHoles *m) { return m->n++; }
static bool tisa_ctx(const TcIsaHostedCtx *h, int n) {
    Binder b[TC_VARS];
    if (n > TC_VARS) return false;
    for (int i = 0; i < n; i++) b[i] = (Binder){ .sort = h->s_word, .bound = 0, .deps = 0 };
    return tc_ctx(n, b);
}
/* The holes of a STEP rule for case cs: Instr's words, the destination's old value (and a store's
   computed key) when the case writes it, the role cells (roles in alias share the destination's key
   and old value), the case's byte cells, HW when two operations chain, and HOUT. */
static void tisa_holes(TisaHoles *m, const TisaForm *f, const TisaCase *cs, bool writes, uint8_t alias) {
    memset(m, -1, sizeof *m);
    m->n = 0;
    static const uint8_t common[] = { HP, HPC, HIID, HIMM, HDISP, HA1, HA2, HNEXT, HALT, HFAIL };
    for (size_t i = 0; i < sizeof common; i++) m->sym[common[i]] = tisa_hole(m);
    if (f->dkind != TISA_KEY_KIND_NONE && !f->dyn_dst) m->DKEY = tisa_hole(m);
    if (writes) { m->OLD = tisa_hole(m); if (f->dyn_dst) m->sym[HDK] = tisa_hole(m); }
    for (int j = 0; j < 4; j++) if (f->roles >> j & 1u) {
        if (alias >> j & 1u) { m->K[j] = m->DKEY; m->sym[HV1 + j] = m->OLD; }
        else { m->K[j] = tisa_hole(m); m->sym[HV1 + j] = tisa_hole(m); }
    }
    for (int b = 0; b < cs->nbytes; b++) { m->sym[HK0 + b] = tisa_hole(m); m->sym[HB0 + b] = tisa_hole(m); }
    if (cs->nop == 2) m->sym[HW] = tisa_hole(m);
    if (cs->nop > 0) m->sym[HOUT] = tisa_hole(m);
}
static Term tisa_cell_pat(const TcIsaHostedCtx *h, Term kind, Term key, Term val) {
    Term a[3] = { kind, key, val };
    return tc_app(h->c_cell, a);
}
static Term tisa_instr_pat(const TcIsaHostedCtx *h, const TisaHoles *m, const TisaForm *f) {
    Term a[TI_N];
    a[TI_PROG] = tc_v(m->sym[HP]); a[TI_PC] = tc_v(m->sym[HPC]); a[TI_IID] = tc_v(m->sym[HIID]);
    a[TI_FORM] = tisa_w(h, f->id);
    a[TI_DKIND] = tisa_w(h, f->dkind == TISA_KEY_KIND_NONE ? 0u : f->dkind);
    a[TI_DKEY] = m->DKEY >= 0 ? tc_v(m->DKEY) : tisa_w(h, 0);
    for (int j = 0; j < 4; j++) a[TI_K1 + j] = (f->roles >> j & 1u) ? tc_v(m->K[j]) : tisa_w(h, 0);
    a[TI_IMM] = tc_v(m->sym[HIMM]); a[TI_DISP] = tc_v(m->sym[HDISP]);
    a[TI_A1] = tc_v(m->sym[HA1]); a[TI_A2] = tc_v(m->sym[HA2]);
    a[TI_NEXT] = tc_v(m->sym[HNEXT]); a[TI_ALT] = tc_v(m->sym[HALT]); a[TI_FAIL] = tc_v(m->sym[HFAIL]);
    return tc_app(h->c_instr, a);
}
static bool tisa_bind_call(const TcIsaHostedCtx *h, const TisaHoles *m, const TisaCall *c, int16_t *fn, uint8_t *in) {
    if (c->nin != TISA_FNS[c->slot].nin) return false;
    *fn = (int16_t)h->fn[c->slot];
    for (int i = 0; i < c->nin; i++) { if (m->sym[c->in[i]] < 0) return false; in[i] = (uint8_t)m->sym[c->in[i]]; }
    return true;
}
static bool tisa_add_guard(const TcIsaHostedCtx *h, Rule *r, const TisaHoles *m, TisaCall c) {
    if (r->nguard >= TC_FN_USES) return false;
    TcGuardUse *g = &r->guard[r->nguard++];
    return tisa_bind_call(h, m, &c, &g->fn, g->in);
}
static void tisa_role_keeps(const TcIsaHostedCtx *h, Rule *r, const TisaHoles *m, const TisaForm *f, uint8_t skip, int nbytes) {
    for (int j = 0; j < 4; j++) if ((f->roles >> j & 1u) && !(skip >> j & 1u))
        r->keep[r->nkeep++] = (Pat){ tisa_cell_pat(h, tisa_w(h, f->kind[j]), tc_v(m->K[j]), tc_v(m->sym[HV1 + j])), TISA_SPACE_STATE };
    for (int b = 0; b < nbytes; b++)
        r->keep[r->nkeep++] = (Pat){ tisa_cell_pat(h, tisa_w(h, TISA_KEY_KIND_BYTE), tc_v(m->sym[HK0 + b]), tc_v(m->sym[HB0 + b])), TISA_SPACE_STATE };
}
static Term tisa_src(const TcIsaHostedCtx *h, const TisaHoles *m, uint8_t sym) { return sym == HZ ? tisa_w(h, 0) : tc_v(m->sym[sym]); }

/* STEP[form, case(, alias)]: one executed point. TAKE the control cell and, when the case writes,
   the destination cell; KEEP Instr, the read cells (a read cell that is the destination is the taken
   one) and the bytes a load reads; GUARD the case's predicates (they select the case); compute the
   case's operations; GUARD the written word's type and, for a store, that it is a byte written at the
   checked address; MAKE the control cell at the case's next and the destination holding the value. */
static int tisa_install_step(TcIsaHostedCtx *h, const TisaForm *f, const TisaCase *cs, uint8_t alias) {
    bool writes = cs->status == TISA_CASE_UPDATE;
    TisaHoles m;
    tisa_holes(&m, f, cs, writes, writes ? alias : 0);
    if (!tisa_ctx(h, m.n)) return -1;
    Term ctrl_kind = tisa_w(h, TISA_KEY_KIND_CTRL), zero = tisa_w(h, 0), dkind = 0, dkey = 0;
    Rule r;
    memset(&r, 0, sizeof r);
    r.fresh = -1;
    r.take[r.ntake++] = (Pat){ tisa_cell_pat(h, ctrl_kind, zero, tc_v(m.sym[HPC])), TISA_SPACE_STATE };
    if (writes) {
        dkind = tisa_w(h, f->dkind);
        dkey = f->dyn_dst ? tc_v(m.sym[HDK]) : tc_v(m.DKEY);
        r.take[r.ntake++] = (Pat){ tisa_cell_pat(h, dkind, dkey, tc_v(m.OLD)), TISA_SPACE_STATE };
    }
    r.keep[r.nkeep++] = (Pat){ tisa_instr_pat(h, &m, f), TISA_SPACE_PROGRAM };
    tisa_role_keeps(h, &r, &m, f, writes ? alias : 0, cs->nbytes);
    for (int i = 0; i < cs->nguard; i++) if (!tisa_add_guard(h, &r, &m, cs->guard[i])) return -1;
    for (int i = 0; i < cs->nop; i++) {
        TcOpUse *u = &r.op[r.nop++];
        if (!tisa_bind_call(h, &m, &cs->op[i], &u->fn, u->in)) return -1;
        u->out[0] = (uint8_t)m.sym[(cs->nop == 2 && i == 0) ? HW : HOUT];
    }
    if (writes) {
        if (f->canon >= 0 && cs->out != HZ && !tisa_add_guard(h, &r, &m, tisa_call((uint8_t)f->canon, 1, (uint8_t[]){ cs->out }))) return -1;
        if (f->dyn_dst && (!tisa_add_guard(h, &r, &m, tisa_call(TFN_G_VALID_BYTE, 1, (uint8_t[]){ cs->out })) ||
                           !tisa_add_guard(h, &r, &m, tisa_call(TFN_G_STORE_KEY, 4, (uint8_t[]){ HV1, HDISP, HA1, HDK })))) return -1;
        r.nmake_extra = 1;
        r.make_extra[0] = (Pat){ tisa_cell_pat(h, dkind, dkey, tisa_src(h, &m, cs->out)), TISA_SPACE_STATE };
    }
    r.make = (Pat){ tisa_cell_pat(h, ctrl_kind, zero, tc_v(m.sym[cs->next])), TISA_SPACE_STATE };
    return tc_rule(&r);
}

/* The theory: sorts, constructors, the sealed functions, and the STEP rules the program's points use,
   with STATE an evidence space of its STEP rules and PROGRAM one with no producer. */
static bool tisa_hosted_theory(TcIsaHostedCtx *h) {
    static uint8_t sha[TFN_COUNT][32];
    static bool sha_ready = false;
    if (!sha_ready) {
        for (int i = 0; i < TFN_COUNT; i++) {
            char text[1024];
            int n = tisa_fn_contract(i, text, sizeof text);
            if (n <= 0 || n >= (int)sizeof text) return false;
            tisa_sha256((const uint8_t *)text, (size_t)n, sha[i]);
        }
        sha_ready = true;
    }
    int s_word = tc_sort(SORT_WORD), s_cell = tc_sort(SORT_PROVABLE), s_instr = tc_sort(SORT_PROVABLE);
    if (s_word < 0 || s_cell < 0 || s_instr < 0) return false;
    h->s_word = (uint16_t)s_word; h->s_cell = (uint16_t)s_cell; h->s_instr = (uint16_t)s_instr;
    Binder wb[TI_N];
    for (int i = 0; i < TI_N; i++) wb[i] = (Binder){ .sort = h->s_word, .bound = 0, .deps = 0 };
    h->c_cell = tc_con(h->s_cell, 0, 3, wb);
    h->c_instr = tc_con(h->s_instr, 0, TI_N, wb);
    if (h->c_cell < 0 || h->c_instr < 0) return false;
    for (int i = 0; i < TFN_COUNT; i++) {
        bool seam = h->opt && h->opt->fault_slot == i && h->opt->fault_fn;   /* a test-only registry */
        TcFn fn = seam ? h->opt->fault_fn : TISA_FNS[i].fn;
        int k = tisa_native_of(i);
        if (!seam && k >= 0 && !tisa_native_bytes_ok(k, fn)) return false;   /* not the proved image: refused */
        h->fn[i] = tc_fn(TISA_FNS[i].name, TISA_FNS[i].kind, TISA_FNS[i].nin, TISA_FNS[i].nout, fn, sha[i]);
        if (h->fn[i] < 0) return false;
    }
    int steps[TISA_MAX_FORMS * 5 * 16];
    int ns = 0;
    memset(h->r_step, 0xFF, sizeof h->r_step);                  /* -1: not installed */
    for (uint32_t pc = 0; pc < h->rt->npoints; pc++) {
        const TisaPoint *p = &h->pt[pc];
        if (p->form < 0) continue;
        const TisaForm *f = &h->forms[p->form];
        for (int ci = 0; ci < f->ncase; ci++) {
            uint8_t a = f->cs[ci].status == TISA_CASE_UPDATE ? p->amask : 0u;
            if (h->r_step[p->form][ci][a] >= 0) continue;
            int rid = tisa_install_step(h, f, &f->cs[ci], a);
            if (rid < 0 || rid > INT16_MAX) return false;
            h->r_step[p->form][ci][a] = (int16_t)rid;
            steps[ns++] = rid;
        }
    }
    return tc_publishers(TISA_SPACE_STATE, steps, ns) && tc_publishers(TISA_SPACE_PROGRAM, NULL, 0);
}

/* The sealed rule set: no rule is barred and none has an input hole; every rule takes the control cell
   first and makes it, keeps Instr first, and takes at most one more cell, which it makes again with
   the same kind and key: a firing moves the activation's one control cell and keeps one cell per key. */
static bool tisa_hosted_audit(const TcIsaHostedCtx *h) {
    Term ctrl = tisa_w(h, TISA_KEY_KIND_CTRL), zero = tisa_w(h, 0);
    for (int rid = 0; rid < tc_rule_count(); rid++) {
        TcInspectRule ir;
        if (!tc_inspect_rule(rid, &ir, NULL) || tc_rule_barred(rid) || ir.decl_rule.inputs) return false;
        const Rule *r = &ir.decl_rule;
        if (r->ntake < 1 || r->ntake > 2 || r->nmake_extra != r->ntake - 1 || r->nkeep < 1 ||
            r->keep[0].space != TISA_SPACE_PROGRAM || r->make.space != TISA_SPACE_STATE) return false;
        uint8_t k; uint32_t head; int ar; const Term *args;
        tc_node(r->keep[0].t, &k, &head, &ar, &args);
        if ((int)head != h->c_instr) return false;
        Term tk[2][2], mk_[2][2];
        for (int i = 0; i < r->ntake; i++) {
            const Pat *t = &r->take[i], *m = i ? &r->make_extra[0] : &r->make;
            if (t->space != TISA_SPACE_STATE || m->space != TISA_SPACE_STATE) return false;
            tc_node(t->t, &k, &head, &ar, &args);
            if ((int)head != h->c_cell || ar != 3) return false;
            tk[i][0] = args[0]; tk[i][1] = args[1];
            tc_node(m->t, &k, &head, &ar, &args);
            if ((int)head != h->c_cell || ar != 3) return false;
            mk_[i][0] = args[0]; mk_[i][1] = args[1];
            if (tk[i][0] != mk_[i][0] || tk[i][1] != mk_[i][1]) return false;
        }
        if (tk[0][0] != ctrl || tk[0][1] != zero) return false;
    }
    return true;
}

/* One Instr per point, one control cell, and one cell per (kind, key): read back from the board. */
static int tisa_cmp_pair(const void *a, const void *b) {
    const uint64_t *x = a, *y = b;
    return x[0] != y[0] ? (x[0] < y[0] ? -1 : 1) : x[1] != y[1] ? (x[1] < y[1] ? -1 : 1) : 0;
}
static bool tisa_hosted_validate(TcIsaHostedCtx *h) {
    uint32_t np = h->rt->npoints;
    size_t ncells = 1u + TISA_NUM_VREGS + sizeof(TcIsaRuntimeFrame) / 8u + (size_t)h->nextra;
    for (uint8_t rid = 0; rid < h->prog->nregions; rid++) ncells += h->byte_occ[rid] ? h->byte_len[rid] : 0u;
    uint64_t *pairs = (uint64_t *)malloc(2u * (np + (size_t)h->nextra + ncells + 1u) * sizeof *pairs);
    Occ *seen = (Occ *)calloc(ncells + 1u, sizeof *seen);
    bool ok = pairs && seen;
    size_t n = 0, ns = 0;
    /* PROGRAM: (prog, pc) of every Instr posted, the seams' included */
    for (uint32_t pc = 0; ok && pc < np; pc++) {
        uint64_t w[TI_N];
        if (!tisa_fact_words(h->pt[pc].instr, h->c_instr, TI_N, w) || w[TI_PC] != pc) { ok = false; break; }
        pairs[2 * n] = w[TI_PROG]; pairs[2 * n + 1] = w[TI_PC]; n++;
    }
    for (int e = 0; ok && e < h->nextra; e++) {
        uint64_t w[TI_N];
        if (tisa_fact_words(h->extra_occ[e], h->c_instr, TI_N, w)) { pairs[2 * n] = w[TI_PROG]; pairs[2 * n + 1] = w[TI_PC]; n++; }
    }
    if (ok) {
        qsort(pairs, n, 2 * sizeof *pairs, tisa_cmp_pair);
        for (size_t i = 1; i < n; i++) if (!tisa_cmp_pair(&pairs[2 * (i - 1)], &pairs[2 * i])) ok = false;
    }
    /* STATE: (kind, key) of every distinct cell occurrence */
    n = 0;
#define TISA_SEE(o) do { Occ o_ = (o); bool dup_ = false; \
        for (size_t s_ = 0; s_ < ns; s_++) if (seen[s_] == o_) { dup_ = true; break; } \
        if (!dup_ && o_) { uint8_t kd_; uint64_t key_; \
            if (!tisa_tcalc_read_cell_full(h, o_, &kd_, &key_, NULL)) ok = false; \
            else { seen[ns++] = o_; pairs[2 * n] = kd_; pairs[2 * n + 1] = kd_ == TISA_KEY_KIND_CTRL ? 0 : key_; n++; } } } while (0)
    if (ok) {
        TISA_SEE(h->ctrl_occ);
        for (int r = 0; r < TISA_NUM_VREGS; r++) TISA_SEE(h->reg_occ[r]);
        for (size_t fw = 0; fw < sizeof(TcIsaRuntimeFrame) / 8u; fw++) TISA_SEE(h->frame_occ[fw]);
        for (int e = 0; e < h->nextra; e++) {
            uint64_t w[TI_N];
            if (!tisa_fact_words(h->extra_occ[e], h->c_instr, TI_N, w)) TISA_SEE(h->extra_occ[e]);   /* a cell, not an Instr */
        }
    }
#undef TISA_SEE
    /* region bytes: distinct physical addresses, so a sort of the keys finds duplicates */
    for (uint8_t rid = 0; ok && rid < h->prog->nregions; rid++)
        for (size_t off = 0; h->byte_occ[rid] && off < h->byte_len[rid]; off++) {
            Occ o = h->byte_occ[rid][off];
            uint8_t kd; uint64_t key;
            if (!tisa_tcalc_read_cell_full(h, o, &kd, &key, NULL) || kd != TISA_KEY_KIND_BYTE ||
                key != h->region_base[rid] + off) { ok = false; break; }
            bool shared = false;                        /* overlapping regions share a cell */
            for (uint8_t r0 = 0; r0 < rid && !shared; r0++)
                shared = h->byte_occ[r0] && key >= h->region_base[r0] && key - h->region_base[r0] < h->byte_len[r0] &&
                         h->byte_occ[r0][key - h->region_base[r0]] == o;
            if (!shared) { pairs[2 * n] = kd; pairs[2 * n + 1] = key; n++; }
        }
    if (ok) {
        qsort(pairs, n, 2 * sizeof *pairs, tisa_cmp_pair);
        for (size_t i = 1; i < n; i++) if (!tisa_cmp_pair(&pairs[2 * (i - 1)], &pairs[2 * i])) ok = false;
    }
    free(pairs); free(seen);
    return ok;
}

/* Builds the theory and posts the program and the cells, validated; the board is not yet sealed.
   false: no verdict. */
static bool tisa_hosted_prepare(TcIsaHostedCtx *h, const TcIsaProgram *prog, const TcIsaRecipeTable *rt,
                                TcIsaRuntimeFrame *frame, const uint64_t regs[TISA_NUM_VREGS],
                                uint32_t max_terms, uint32_t max_occs, const TcIsaHostedOptions *opt) {
    memset(h, 0, sizeof *h);
    h->prog = prog; h->rt = rt; h->opt = opt;
    h->frame_base_addr = (uint64_t)(uintptr_t)frame;
    h->max_occs = max_occs;
    if (!tc_init(max_terms, max_occs)) return false;
    tc_protect(TISA_SPACE_STATE); tc_protect(TISA_SPACE_PROGRAM);
    h->pt = (TisaPoint *)calloc(rt->npoints ? rt->npoints : 1u, sizeof *h->pt);
    if (!h->pt) return false;
    for (uint32_t pc = 0; pc < rt->npoints; pc++) {
        TisaPoint *p = &h->pt[pc];
        TisaForm f;
        p->form = -1;
        p->w[TI_PROG] = prog->prog_id; p->w[TI_PC] = pc;
        if (tisa_point_form(prog, &rt->recipes[pc], h->frame_base_addr, &f, p->w)) {
            int fi = 0;
            while (fi < h->nforms && h->forms[fi].id != f.id) fi++;
            if (fi == h->nforms) { if (h->nforms >= TISA_MAX_FORMS) return false; h->forms[h->nforms++] = f; }
            p->form = fi;
            for (int j = 0; j < 4; j++)
                if ((f.roles >> j & 1u) && f.dkind == f.kind[j] && !f.dyn_dst && p->w[TI_K1 + j] == p->w[TI_DKEY])
                    p->amask |= (uint8_t)(1u << j);
        } else {
            memset(p->w, 0, sizeof p->w);
            p->w[TI_PROG] = prog->prog_id; p->w[TI_PC] = pc;
        }
        uint64_t iid = 0xcbf29ce484222325ull;            /* the recipe's identity: a digest of its words */
        for (int i = 0; i < TI_N; i++) if (i != TI_IID) { iid ^= p->w[i]; iid *= 0x100000001b3ull; iid ^= iid >> 29; }
        p->w[TI_IID] = iid;
    }
    if (!tisa_hosted_theory(h)) return false;

    Term a[TI_N];
    for (uint32_t pc = 0; pc < rt->npoints; pc++) {              /* PROGRAM: one Instr per point */
        for (int i = 0; i < TI_N; i++) if (!(a[i] = tisa_w(h, h->pt[pc].w[i]))) return false;
        Term t = tc_app(h->c_instr, a);
        if (!t || !(h->pt[pc].instr = tc_post(TISA_SPACE_PROGRAM, t))) return false;
    }
    /* STATE: the control cell at the entry point, registers, frame words and region bytes */
    if (!(h->ctrl_occ = tisa_post_cell(h, TISA_KEY_KIND_CTRL, 0ull, rt->entry_point))) return false;
    for (uint8_t r = 0; r < TISA_NUM_VREGS; r++)
        if (!(h->reg_occ[r] = tisa_post_cell(h, TISA_KEY_KIND_REG, (uint64_t)r, regs[r]))) return false;
    const uint64_t *raw = &frame->s0_ptr;
    size_t fu_idx = offsetof(TcIsaRuntimeFrame, fuel_used) / 8u;
    for (size_t fw = 0; fw < sizeof(TcIsaRuntimeFrame) / 8u; fw++)
        if (!(h->frame_occ[fw] = tisa_post_cell(h, TISA_KEY_KIND_FRAME, (uint64_t)fw, fw == fu_idx ? 0ull : raw[fw]))) return false;
    for (uint8_t rid = 0; rid < prog->nregions; rid++) {
        if (prog->regions[rid].mode == TISA_CAP_NONE) continue;
        uint64_t base = raw[rid * 2u], len = raw[rid * 2u + 1u];
        h->region_base[rid] = base;
        h->byte_len[rid] = (size_t)len;
        if (!len) continue;
        if (!(h->byte_occ[rid] = (Occ *)calloc((size_t)len, sizeof(Occ)))) return false;
        const uint8_t *bytes = (const uint8_t *)(uintptr_t)base;
        for (size_t off = 0; off < (size_t)len; off++) {
            uint64_t phys = base + (uint64_t)off;
            Occ shared = 0;
            for (uint8_t r0 = 0; r0 < rid && !shared; r0++)
                if (prog->regions[r0].mode != TISA_CAP_NONE && h->byte_occ[r0] &&
                    phys >= h->region_base[r0] && phys - h->region_base[r0] < h->byte_len[r0])
                    shared = h->byte_occ[r0][phys - h->region_base[r0]];
            if (!(h->byte_occ[rid][off] = shared ? shared : tisa_post_cell(h, TISA_KEY_KIND_BYTE, phys, (uint64_t)bytes[off]))) return false;
        }
    }
    /* test seams: duplicates the validation below must reject */
    if (opt && opt->dup_instr && opt->dup_pc < rt->npoints) {
        uint64_t dw[TI_N];
        memcpy(dw, h->pt[opt->dup_pc].w, sizeof dw);
        dw[TI_IMM] ^= 1u;                                       /* a second recipe at the same point */
        for (int i = 0; i < TI_N; i++) a[i] = tisa_w(h, dw[i]);
        Term t = tc_app(h->c_instr, a);
        if (!t || !(h->extra_occ[h->nextra++] = tc_post(TISA_SPACE_PROGRAM, t))) return false;
    }
    if (opt && opt->dup_ctrl && !(h->extra_occ[h->nextra++] = tisa_post_cell(h, TISA_KEY_KIND_CTRL, 0ull, rt->entry_point))) return false;
    if (opt && opt->dup_reg && !(h->extra_occ[h->nextra++] = tisa_post_cell(h, TISA_KEY_KIND_REG, opt->dup_reg_idx, opt->dup_reg_val))) return false;
    return (opt && opt->skip_validation) || tisa_hosted_validate(h);
}
/* Seals the board and audits the sealed rule set. */
static bool tisa_hosted_seal(const TcIsaHostedCtx *h) {
    tc_seal();
    return tisa_hosted_audit(h);
}
static bool tisa_hosted_open(TcIsaHostedCtx *h, const TcIsaProgram *prog, const TcIsaRecipeTable *rt,
                             TcIsaRuntimeFrame *frame, const uint64_t regs[TISA_NUM_VREGS],
                             uint32_t max_terms, uint32_t max_occs, const TcIsaHostedOptions *opt) {
    return tisa_hosted_prepare(h, prog, rt, frame, regs, max_terms, max_occs, opt) && tisa_hosted_seal(h);
}

static void tisa_hosted_close(TcIsaHostedCtx *h) {
    for (uint8_t rid = 0; h->prog && rid < h->prog->nregions; rid++) { free(h->byte_occ[rid]); h->byte_occ[rid] = NULL; }
    free(h->pt);
    h->pt = NULL;
}

/* The words a point's rules see, read from Instr and the role cells (and, for case ci, its bytes). */
typedef struct { uint64_t v[HNH]; Occ role[4], byte[8]; } TisaEnv;

static bool tisa_point_env(TcIsaHostedCtx *h, const TisaPoint *p, TisaEnv *e) {
    const TisaForm *f = &h->forms[p->form];
    memset(e, 0, sizeof *e);
    e->v[HP] = p->w[TI_PROG]; e->v[HPC] = p->w[TI_PC]; e->v[HIID] = p->w[TI_IID];
    e->v[HIMM] = p->w[TI_IMM]; e->v[HDISP] = p->w[TI_DISP]; e->v[HA1] = p->w[TI_A1]; e->v[HA2] = p->w[TI_A2];
    e->v[HNEXT] = p->w[TI_NEXT]; e->v[HALT] = p->w[TI_ALT]; e->v[HFAIL] = p->w[TI_FAIL];
    for (int j = 0; j < 4; j++) if (f->roles >> j & 1u) {
        Occ *s = tisa_cell_slot(h, f->kind[j], p->w[TI_K1 + j]);
        if (!s || !*s || !tisa_tcalc_read_cell_word(h, *s, &e->v[HV1 + j])) return false;
        e->role[j] = *s;
    }
    return true;
}
/* Whether case cs's guards hold on the words (the host's choice; the kernel decides again). */
static bool tisa_case_holds(TcIsaHostedCtx *h, const TisaCase *cs, TisaEnv *e) {
    if (cs->nbytes) {                                   /* the bytes at the computed address, if they exist */
        uint64_t a = e->v[HV1] + (uint64_t)(int64_t)(int32_t)(int64_t)e->v[HDISP];
        for (int b = 0; b < cs->nbytes; b++) {
            e->v[HK0 + b] = a + (uint64_t)b;
            Occ *s = tisa_cell_slot(h, TISA_KEY_KIND_BYTE, e->v[HK0 + b]);
            if (!s || !*s || !tisa_tcalc_read_cell_word(h, *s, &e->v[HB0 + b])) return false;
            e->byte[b] = *s;
        }
    }
    for (int g = 0; g < cs->nguard; g++) {
        const TisaCall *c = &cs->guard[g];
        uint64_t in[TC_FN_IN] = { 0 }, scratch[TC_FN_OUT];
        for (int i = 0; i < c->nin; i++) in[i] = e->v[c->in[i]];
        if (!TISA_FNS[c->slot].fn(in, scratch)) return false;
    }
    return true;
}

/* The firing that executes point pc for case ci: the STEP rule and its premises, from the tracked
   cells. false: no such rule or cell (the host stops: no verdict). */
typedef struct { int rule; Occ take[2], keep[TC_HYPS]; int nkeep; uint8_t dkind; uint64_t dkey; } TisaFiring;
static bool tisa_step_firing(TcIsaHostedCtx *h, const TisaPoint *p, int ci, const TisaEnv *e, TisaFiring *fr) {
    const TisaForm *f = &h->forms[p->form];
    const TisaCase *cs = &f->cs[ci];
    bool writes = cs->status == TISA_CASE_UPDATE;
    uint8_t alias = writes ? p->amask : 0u;
    memset(fr, 0, sizeof *fr);
    fr->rule = h->r_step[p->form][ci][alias];
    if (fr->rule < 0) return false;
    fr->take[0] = h->ctrl_occ;
    fr->keep[fr->nkeep++] = p->instr;
    if (writes) {
        fr->dkind = f->dkind;
        fr->dkey = f->dyn_dst ? e->v[HV1] + (uint64_t)(int64_t)(int32_t)(int64_t)e->v[HDISP] + e->v[HA1] : p->w[TI_DKEY];
        Occ *slot = tisa_cell_slot(h, f->dkind, fr->dkey);
        if (!slot || !*slot) return false;
        fr->take[1] = *slot;
    }
    for (int j = 0; j < 4; j++) if ((f->roles >> j & 1u) && !(alias >> j & 1u)) fr->keep[fr->nkeep++] = e->role[j];
    for (int b = 0; b < cs->nbytes; b++) fr->keep[fr->nkeep++] = e->byte[b];
    return true;
}

/* One executed point: one STEP firing, for the case whose guards hold. Budget: the cells it makes
   count against max_occs, checked before it fires (as before). */
static bool tisa_hosted_step(TcIsaHostedCtx *h, uint64_t pc) {
    const TisaPoint *p = &h->pt[pc];
    if (p->form < 0) return false;
    const TisaForm *f = &h->forms[p->form];
    TisaEnv e;
    if (!tisa_point_env(h, p, &e)) return false;
    int ci = 0;
    while (ci < f->ncase && !tisa_case_holds(h, &f->cs[ci], &e)) ci++;
    if (ci == f->ncase) return false;
    const TisaCase *cs = &f->cs[ci];
    bool writes = cs->status == TISA_CASE_UPDATE;
    TisaFiring fr;
    if (!tisa_step_firing(h, p, ci, &e, &fr) || h->occ_allocs + (writes ? 2u : 1u) > h->max_occs) return false;
    Occ nc = tc_fire(fr.rule, fr.take, fr.keep, NULL);
    if (!nc) return false;
    if (writes) {
        Occ nd = tc_last_extra(0);
        if (!nd) return false;
        tisa_cell_moved(h, fr.dkind, fr.dkey, fr.take[1], nd);
    }
    h->ctrl_occ = nc;
    h->occ_allocs += writes ? 2u : 1u;
    h->fires++;
    uint64_t chk = 0;
    return tisa_tcalc_read_cell_word(h, h->ctrl_occ, &chk) && chk == e.v[cs->next];
}

/* Runs to a HALT point: 1, with the outcome and the point; 0: no verdict. */
static int tisa_hosted_run(TcIsaHostedCtx *h, TcIsaOutcome *out_outcome, uint64_t *out_halt_pc) {
    for (;;) {
        uint8_t kind = 0xFFu;
        uint64_t key = UINT64_MAX, pc = UINT64_MAX;
        if (!tisa_tcalc_read_cell_full(h, h->ctrl_occ, &kind, &key, &pc) || kind != TISA_KEY_KIND_CTRL || key != 0ull) return 0;
        if (TISA_POINT_IS_HALT(pc)) {
            uint64_t oc = pc & 0xFFull;
            if (oc > (uint64_t)TISA_OUTCOME_EXHAUSTED || pc != TISA_POINT_HALT((TcIsaOutcome)oc)) return 0;
            *out_outcome = (TcIsaOutcome)oc; *out_halt_pc = pc;
            return 1;
        }
        if (pc >= (uint64_t)h->rt->npoints || !tisa_hosted_step(h, pc)) return 0;
    }
}

bool tisa_try_eval_tcalc_with_limits(const TcIsaProgram *prog,
                                     TcIsaRuntimeFrame *frame,
                                     uint64_t regs[TISA_NUM_VREGS],
                                     uint32_t max_terms,
                                     uint32_t max_occs,
                                     TcIsaHostedRunResult *out_res) {
    if (out_res) {
        memset(out_res, 0, sizeof(*out_res));
        out_res->host_status  = TISA_HOST_STATUS_NO_VERDICT;
        out_res->has_verdict  = false;
        out_res->board_halted = false;
        out_res->halt_pc      = UINT64_MAX;
    }
    if (!prog || !frame || !regs || !out_res || max_terms == 0u || max_occs == 0u) {
        return false;
    }

    char err[256] = {0};
    TcIsaRecipeTable rtable;
    if (!tisa_lower_recipes(prog, &rtable, err, sizeof(err))) {
        return false;
    }

    TcIsaOutcome vrc = tisa_validate_frame(prog, frame, regs, err, sizeof(err));
    if (vrc != TISA_OUTCOME_FIRED) {
        frame->status = vrc;
        frame->ret_val = vrc;
        out_res->host_status  = TISA_HOST_STATUS_ABI_REJECTED;
        out_res->has_verdict  = true;
        out_res->board_halted = false;
        out_res->outcome      = vrc;
        return true;
    }

    TcIsaHostedCtx h;
    TcIsaOutcome final_outcome = TISA_OUTCOME_INVALID_INPUT;
    uint64_t final_halt_pc = UINT64_MAX;
    bool ok = tisa_hosted_open(&h, prog, &rtable, frame, regs, max_terms, max_occs, NULL) &&
              tisa_hosted_run(&h, &final_outcome, &final_halt_pc) == 1;

    /* Read back registers, frame status/ret_val/fuel_used and writable region bytes, only once the
       board reached a HALT point */
    uint64_t final_regs[TISA_NUM_VREGS] = {0};
    uint64_t st_w = 0, rv_w = 0, fu_w = 0;
    const uint64_t *raw = &frame->s0_ptr;
    size_t st_idx = offsetof(TcIsaRuntimeFrame, status) / 8u, rv_idx = offsetof(TcIsaRuntimeFrame, ret_val) / 8u;
    size_t fu_idx = offsetof(TcIsaRuntimeFrame, fuel_used) / 8u;
    for (uint8_t r = 0; ok && r < TISA_NUM_VREGS; r++) ok = tisa_tcalc_read_cell_word(&h, h.reg_occ[r], &final_regs[r]);
    ok = ok && tisa_tcalc_read_cell_word(&h, h.frame_occ[st_idx], &st_w) && tisa_tcalc_read_cell_word(&h, h.frame_occ[rv_idx], &rv_w) &&
         tisa_tcalc_read_cell_word(&h, h.frame_occ[fu_idx], &fu_w) && st_w == (uint64_t)final_outcome;
    for (uint8_t rid = 0; ok && rid < prog->nregions; rid++)
        if (prog->regions[rid].mode == TISA_CAP_RW && h.byte_occ[rid])
            for (size_t off = 0; ok && off < h.byte_len[rid]; off++) {
                uint64_t bval = 0;
                ok = tisa_tcalc_read_cell_word(&h, h.byte_occ[rid][off], &bval);
            }
    if (ok) {
        for (uint8_t r = 0; r < TISA_NUM_VREGS; r++) regs[r] = final_regs[r];
        frame->status    = st_w;
        frame->ret_val   = rv_w;
        frame->fuel_used = fu_w;
        for (uint8_t rid = 0; rid < prog->nregions; rid++) {
            if (prog->regions[rid].mode == TISA_CAP_RW && h.byte_occ[rid]) {
                uint8_t *bytes = (uint8_t *)(uintptr_t)raw[rid * 2u];
                for (size_t off = 0; off < h.byte_len[rid]; off++) {
                    uint64_t bval = 0;
                    (void)tisa_tcalc_read_cell_word(&h, h.byte_occ[rid][off], &bval);
                    bytes[off] = (uint8_t)(bval & 0xFFu);
                }
            }
        }
    }
    out_res->tcalc_fires = h.fires;
    tisa_hosted_close(&h);
    if (!ok) {
        return false;
    }
    out_res->host_status  = TISA_HOST_STATUS_BOARD_HALTED;
    out_res->has_verdict  = true;
    out_res->board_halted = true;
    out_res->outcome      = final_outcome;
    out_res->halt_pc      = final_halt_pc;
    return true;
}

bool tisa_try_eval_tcalc(const TcIsaProgram *prog,
                         TcIsaRuntimeFrame *frame,
                         uint64_t regs[TISA_NUM_VREGS],
                         TcIsaHostedRunResult *out_res) {
    return tisa_try_eval_tcalc_with_limits(prog, frame, regs, 1u << 18, 1u << 17, out_res);
}

TcIsaOutcome tisa_eval_tcalc(const TcIsaProgram *prog,
                             TcIsaRuntimeFrame *frame,
                             uint64_t regs[TISA_NUM_VREGS],
                             uint64_t *out_tcalc_fires) {
    TcIsaHostedRunResult res;
    bool ok = tisa_try_eval_tcalc(prog, frame, regs, &res);
    if (out_tcalc_fires) *out_tcalc_fires = res.tcalc_fires;
    if (!ok || !res.has_verdict) {
        return TISA_OUTCOME_INVALID_INPUT;
    }
    return res.outcome;
}

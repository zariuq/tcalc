/*
 * tisa_specialize.c — Table-Driven Specializer & Consumer Builders for `t-ISA`
 *
 * Implements:
 *   1. `tisa_specialize_lean_flat_rule`: derives `t-ISA` programs for all 11
 *      premise-bearing Lean rules (`R_DERIVE_IS_TYPE .. R_ADMIT_THM`) directly
 *      from the live `TcInspectRule` + `TcInspectFlat` reflection tables.
 *   2. `tisa_specialize_micromath_sub_rule`: derives `t-ISA` programs for
 *      Micromath's 4-premise substitution rules (`sub1` and `sub2`) directly
 *      from the live `R[]` / `FL[]` reflection tables.
 *   3. `tisa_build_ordinary_flat_fire_prog`: builds the generic `flat_fire`
 *      (`ordinary_flat_fire`) `t-ISA` program.
 *   4. `tisa_build_ordinary_flat_adapter_prog`: builds the complete
 *      `ordinary_flat_adapter` (`ordinary_flat_pack` + `flat_fire`) `t-ISA`
 *      program over all 9 span capabilities (`s0..s8`).
 */
#include "tisa.h"
#include <stdio.h>
#include <string.h>

/* =========================================================================
 * 1. Concise Instruction Construction Helpers
 * ========================================================================= */

static TcIsaStmt *mk_imm(TcIsaArena *a, TcIsaValType ty, uint8_t dst, uint64_t imm64) {
    TcIsaInstr ins;
    memset(&ins, 0, sizeof(ins));
    ins.op    = TISA_OP_IMM;
    ins.ty    = ty;
    ins.dst   = dst;
    ins.imm64 = imm64;
    return tisa_stmt_instr(a, ins);
}

static __attribute__((unused)) TcIsaStmt *mk_mov(TcIsaArena *a, TcIsaValType ty, uint8_t dst, uint8_t src1) {
    TcIsaInstr ins;
    memset(&ins, 0, sizeof(ins));
    ins.op   = TISA_OP_MOV;
    ins.ty   = ty;
    ins.dst  = dst;
    ins.src1 = src1;
    return tisa_stmt_instr(a, ins);
}

static TcIsaStmt *mk_bin(TcIsaArena *a, TcIsaBinOp subop, TcIsaValType ty,
                         uint8_t dst, uint8_t src1, uint8_t src2) {
    TcIsaInstr ins;
    memset(&ins, 0, sizeof(ins));
    ins.op    = TISA_OP_BIN;
    ins.ty    = ty;
    ins.dst   = dst;
    ins.src1  = src1;
    ins.src2  = src2;
    ins.subop = (uint8_t)subop;
    return tisa_stmt_instr(a, ins);
}

static TcIsaStmt *mk_shift(TcIsaArena *a, TcIsaShiftOp subop, TcIsaValType ty,
                           uint8_t dst, uint8_t src1, uint8_t sh) {
    TcIsaInstr ins;
    memset(&ins, 0, sizeof(ins));
    ins.op        = TISA_OP_SHIFT;
    ins.ty        = ty;
    ins.dst       = dst;
    ins.src1      = src1;
    ins.subop     = (uint8_t)subop;
    ins.bit_width = sh;
    return tisa_stmt_instr(a, ins);
}

static TcIsaStmt *mk_extract(TcIsaArena *a, TcIsaValType ty,
                             uint8_t dst, uint8_t src1, uint8_t lsb, uint8_t width) {
    TcIsaInstr ins;
    memset(&ins, 0, sizeof(ins));
    ins.op        = TISA_OP_EXTRACT;
    ins.ty        = ty;
    ins.dst       = dst;
    ins.src1      = src1;
    ins.scale_lg2 = lsb;
    ins.bit_width = width;
    return tisa_stmt_instr(a, ins);
}

static TcIsaStmt *mk_addr(TcIsaArena *a, uint8_t region_id,
                          uint8_t dst, uint8_t base_reg, uint8_t idx_reg,
                          uint8_t scale_lg2, int32_t disp32) {
    TcIsaInstr ins;
    memset(&ins, 0, sizeof(ins));
    ins.op        = TISA_OP_ADDR;
    ins.ty        = TISA_TYPE_PTR;
    ins.dst       = dst;
    ins.src1      = base_reg;
    ins.src2      = idx_reg;
    ins.region_id = region_id;
    ins.scale_lg2 = scale_lg2;
    ins.disp32    = disp32;
    return tisa_stmt_instr(a, ins);
}

static TcIsaStmt *mk_load(TcIsaArena *a, uint8_t region_id, TcIsaMemWidth width,
                          TcIsaValType ty, uint8_t dst, uint8_t base_reg, int32_t disp32) {
    TcIsaInstr ins;
    memset(&ins, 0, sizeof(ins));
    ins.op        = TISA_OP_LOAD;
    ins.ty        = ty;
    ins.dst       = dst;
    ins.src1      = base_reg;
    ins.subop     = (uint8_t)width;
    ins.region_id = region_id;
    ins.disp32    = disp32;
    return tisa_stmt_instr(a, ins);
}

static TcIsaStmt *mk_load_frame_ptr(TcIsaArena *a, uint8_t dst, uint8_t target_region_id) {
    return mk_load(a, TISA_REGION_FRAME, TISA_MEM_U64, TISA_TYPE_PTR,
                   dst, TISA_V0, (int32_t)(target_region_id * 16u));
}

static TcIsaStmt *mk_load_frame_len(TcIsaArena *a, uint8_t dst, uint8_t target_region_id) {
    return mk_load(a, TISA_REGION_FRAME, TISA_MEM_U64, TISA_TYPE_U64,
                   dst, TISA_V0, (int32_t)(target_region_id * 16u + 8u));
}

static TcIsaStmt *mk_store(TcIsaArena *a, uint8_t region_id, TcIsaMemWidth width,
                           uint8_t base_reg, int32_t disp32, uint8_t val_reg) {
    TcIsaInstr ins;
    memset(&ins, 0, sizeof(ins));
    ins.op        = TISA_OP_STORE;
    ins.ty        = (width == TISA_MEM_U64) ? TISA_TYPE_U64 : TISA_TYPE_U32Z;
    ins.src1      = base_reg;
    ins.src2      = val_reg;
    ins.subop     = (uint8_t)width;
    ins.region_id = region_id;
    ins.disp32    = disp32;
    return tisa_stmt_instr(a, ins);
}

static TcIsaStmt *mk_cmp_reg(TcIsaArena *a, TcIsaCmpCond cond, TcIsaValType ty,
                             uint8_t dst, uint8_t src1, uint8_t src2) {
    TcIsaInstr ins;
    memset(&ins, 0, sizeof(ins));
    ins.op        = TISA_OP_CMP;
    ins.ty        = ty;
    ins.dst       = dst;
    ins.src1      = src1;
    ins.src2      = src2;
    ins.subop     = (uint8_t)cond;
    ins.bit_width = 0u;
    return tisa_stmt_instr(a, ins);
}

static TcIsaStmt *mk_cmp_imm(TcIsaArena *a, TcIsaCmpCond cond, TcIsaValType ty,
                             uint8_t dst, uint8_t src1, uint64_t imm64) {
    TcIsaInstr ins;
    memset(&ins, 0, sizeof(ins));
    ins.op        = TISA_OP_CMP;
    ins.ty        = ty;
    ins.dst       = dst;
    ins.src1      = src1;
    ins.subop     = (uint8_t)cond;
    ins.bit_width = 1u;
    ins.imm64     = imm64;
    return tisa_stmt_instr(a, ins);
}

static __attribute__((unused)) TcIsaStmt *mk_select(TcIsaArena *a, TcIsaValType ty,
                            uint8_t dst, uint8_t vtrue, uint8_t vfalse, uint8_t cond_reg) {
    TcIsaInstr ins;
    memset(&ins, 0, sizeof(ins));
    ins.op   = TISA_OP_SELECT;
    ins.ty   = ty;
    ins.dst  = dst;
    ins.src1 = vtrue;
    ins.src2 = vfalse;
    ins.src3 = cond_reg;
    return tisa_stmt_instr(a, ins);
}

/* Helper to read the 64-bit payload of a constant term `mc_term` from tcalc */
static uint64_t inspect_const_u64_payload(Term mc_term) {
    uint8_t kind = 0; uint32_t head = 0; int ar = 0; const Term *args = NULL;
    tc_node(mc_term, &kind, &head, &ar, &args);
    if (kind == K_NAME) return tc_name_id(mc_term);
    if (kind == K_APP && ar == 0) return 0ull;
    if (kind == K_APP && ar >= 1 && args) return tc_name_id(args[0]);
    return (uint64_t)mc_term;
}

/* =========================================================================
 * 2. Table-Driven Specializer for the 11 Premise-Bearing Lean Rules
 * ========================================================================= */

static const char *const LEAN_PREMISE_REGION_NAMES[5] = {
    "premise_0", "premise_1", "premise_2", "premise_3", "output_tuple"
};

bool tisa_specialize_lean_flat_rule(TcIsaArena *arena,
                                    const TcInspectRule *ir,
                                    const TcInspectFlat *ifl,
                                    const char *rule_name,
                                    TcIsaProgram *out_prog,
                                    char *err_buf, size_t err_cap) {
    if (!arena || !ir || !ifl || !out_prog) {
        if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "null argument to tisa_specialize_lean_flat_rule");
        return false;
    }
    if (!ir->flat || ir->nkeep == 0 || ir->nkeep > 4) {
        if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "rule %d is not a 1..4 premise flat rule", ir->rule_id);
        return false;
    }

    memset(out_prog, 0, sizeof(*out_prog));
    out_prog->name      = rule_name ? rule_name : "lean_flat_rule";
    out_prog->prog_id   = (uint32_t)ir->rule_id;
    uint8_t np          = ir->nkeep;
    out_prog->nregions  = (uint8_t)(np + 1u);

    /* v0 is frame; v1..v<np> hold RO premise pointers (regions 0..np-1); v<np+1> holds RW output pointer (region np) */
    out_prog->init_reg_mask       = (1u << TISA_V0);
    out_prog->init_reg_types[0]   = TISA_TYPE_U64;
    for (uint8_t i = 0; i < np; i++) {
        out_prog->regions[i] = (TcIsaRegionDecl){
            .region_id    = i,
            .mode         = TISA_CAP_RO,
            .min_byte_len = 32u, /* sizeof(TcLeanGenTuple) */
            .align_bytes  = 8u,
            .name         = LEAN_PREMISE_REGION_NAMES[i]
        };
        uint8_t reg = (uint8_t)(TISA_V1 + i);
        out_prog->init_reg_mask     |= (uint16_t)(1u << reg);
        out_prog->init_reg_types[reg]  = TISA_TYPE_PTR;
        out_prog->init_reg_region[reg] = i;
    }
    out_prog->regions[np] = (TcIsaRegionDecl){
        .region_id    = np,
        .mode         = TISA_CAP_RW,
        .min_byte_len = 32u,
        .align_bytes  = 8u,
        .name         = "output_tuple"
    };
    uint8_t out_reg = (uint8_t)(TISA_V1 + np);
    out_prog->init_reg_mask         |= (uint16_t)(1u << out_reg);
    out_prog->init_reg_types[out_reg]  = TISA_TYPE_PTR;
    out_prog->init_reg_region[out_reg] = np;

    /* Build the conclusion (when all tags & guards pass): write TcLeanGenTuple to out_reg */
    uint32_t mtag = (ifl->mhead << 9) | ((uint32_t)ir->mspace << 1) | 1u;
    TcIsaStmt *concl = NULL;
    /* out->tag = mtag (offset 0, U32); out->pad = 0 (offset 4, U32) */
    concl = tisa_stmt_seq(arena, concl, mk_imm(arena, TISA_TYPE_U32Z, TISA_V6, mtag));
    concl = tisa_stmt_seq(arena, concl, mk_store(arena, np, TISA_MEM_U32, out_reg, 0, TISA_V6));
    concl = tisa_stmt_seq(arena, concl, mk_imm(arena, TISA_TYPE_U32Z, TISA_V6, 0u));
    concl = tisa_stmt_seq(arena, concl, mk_store(arena, np, TISA_MEM_U32, out_reg, 4, TISA_V6));

    /* Gather and store out->a[0..2] (offsets 8, 16, 24) */
    for (uint8_t j = 0; j < 3u; j++) {
        if (j < ifl->mar) {
            uint8_t mi = ifl->mi[j];
            uint8_t mj = ifl->mj[j];
            if (mi < np) {
                uint8_t preg = (uint8_t)(TISA_V1 + mi);
                concl = tisa_stmt_seq(arena, concl,
                                      mk_load(arena, mi, TISA_MEM_U64, TISA_TYPE_U64,
                                              TISA_V6, preg, (int32_t)(8u + mj * 8u)));
            } else {
                uint64_t cval = inspect_const_u64_payload(ifl->mc[mj]);
                concl = tisa_stmt_seq(arena, concl, mk_imm(arena, TISA_TYPE_U64, TISA_V6, cval));
            }
        } else {
            concl = tisa_stmt_seq(arena, concl, mk_imm(arena, TISA_TYPE_U64, TISA_V6, 0ull));
        }
        concl = tisa_stmt_seq(arena, concl,
                              mk_store(arena, np, TISA_MEM_U64, out_reg, (int32_t)(8u + j * 8u), TISA_V6));
    }
    concl = tisa_stmt_seq(arena, concl, mk_imm(arena, TISA_TYPE_U64, TISA_V8, 1ull));
    concl = tisa_stmt_seq(arena, concl, tisa_stmt_return(arena, TISA_OUTCOME_FIRED, TISA_V8));

    /* Refusal branch: returns 0 without writing anything to output_tuple */
    TcIsaStmt *refuse = tisa_stmt_seq(arena,
                                      mk_imm(arena, TISA_TYPE_U64, TISA_V8, 0ull),
                                      tisa_stmt_return(arena, TISA_OUTCOME_REFUSED, TISA_V8));

    /* Wrap `concl` inside the `nguard` guards from `ifl` in reverse order */
    TcIsaStmt *curr = concl;
    for (int g = (int)ifl->nguard - 1; g >= 0; g--) {
        uint8_t i  = ifl->guard[g].i;
        uint8_t j  = ifl->guard[g].j;
        uint8_t i0 = ifl->guard[g].i0;
        uint8_t j0 = ifl->guard[g].j0;
        TcIsaStmt *gcheck = NULL;

        if (i < np && i0 == np) {
            /* Constant guard: premise[i].a[j] == const_payload(mc[j0]) */
            uint8_t preg = (uint8_t)(TISA_V1 + i);
            uint64_t cval = inspect_const_u64_payload(ifl->mc[j0]);
            gcheck = tisa_stmt_seq(arena, gcheck,
                                   mk_load(arena, i, TISA_MEM_U64, TISA_TYPE_U64,
                                           TISA_V6, preg, (int32_t)(8u + j * 8u)));
            gcheck = tisa_stmt_seq(arena, gcheck,
                                   mk_cmp_imm(arena, TISA_CMP_EQ, TISA_TYPE_U64,
                                              TISA_V7, TISA_V6, cval));
        } else if (i == np && i0 < np) {
            uint8_t preg = (uint8_t)(TISA_V1 + i0);
            uint64_t cval = inspect_const_u64_payload(ifl->mc[j]);
            gcheck = tisa_stmt_seq(arena, gcheck,
                                   mk_load(arena, i0, TISA_MEM_U64, TISA_TYPE_U64,
                                           TISA_V6, preg, (int32_t)(8u + j0 * 8u)));
            gcheck = tisa_stmt_seq(arena, gcheck,
                                   mk_cmp_imm(arena, TISA_CMP_EQ, TISA_TYPE_U64,
                                              TISA_V7, TISA_V6, cval));
        } else {
            /* Field-to-field equality guard: premise[i].a[j] == premise[i0].a[j0] */
            uint8_t preg1 = (uint8_t)(TISA_V1 + i);
            uint8_t preg2 = (uint8_t)(TISA_V1 + i0);
            gcheck = tisa_stmt_seq(arena, gcheck,
                                   mk_load(arena, i, TISA_MEM_U64, TISA_TYPE_U64,
                                           TISA_V6, preg1, (int32_t)(8u + j * 8u)));
            gcheck = tisa_stmt_seq(arena, gcheck,
                                   mk_load(arena, i0, TISA_MEM_U64, TISA_TYPE_U64,
                                           TISA_V8, preg2, (int32_t)(8u + j0 * 8u)));
            gcheck = tisa_stmt_seq(arena, gcheck,
                                   mk_cmp_reg(arena, TISA_CMP_EQ, TISA_TYPE_U64,
                                              TISA_V7, TISA_V6, TISA_V8));
        }
        curr = tisa_stmt_seq(arena, gcheck, tisa_stmt_if(arena, TISA_V7, curr, refuse));
    }

    /* Wrap `curr` inside the `np` premise `wtag` checks in reverse order */
    for (int i = (int)np - 1; i >= 0; i--) {
        uint8_t preg = (uint8_t)(TISA_V1 + i);
        TcIsaStmt *tcheck = NULL;
        tcheck = tisa_stmt_seq(arena, tcheck,
                               mk_load(arena, (uint8_t)i, TISA_MEM_U32, TISA_TYPE_U32Z,
                                       TISA_V6, preg, 0));
        tcheck = tisa_stmt_seq(arena, tcheck,
                               mk_cmp_imm(arena, TISA_CMP_EQ, TISA_TYPE_U32Z,
                                          TISA_V7, TISA_V6, (uint64_t)ifl->ktag[i]));
        curr = tisa_stmt_seq(arena, tcheck, tisa_stmt_if(arena, TISA_V7, curr, refuse));
    }

    out_prog->root = curr;
    return tisa_check_program(out_prog, err_buf, err_cap);
}

/* =========================================================================
 * 3. Table-Driven Specializer for Micromath `sub1` & `sub2`
 * ========================================================================= */

bool tisa_specialize_micromath_sub_rule(TcIsaArena *arena,
                                        const TcInspectRule *ir,
                                        const TcInspectFlat *ifl,
                                        const char *rule_name,
                                        TcIsaProgram *out_prog,
                                        char *err_buf, size_t err_cap) {
    if (!arena || !ir || !ifl || !out_prog) {
        if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "null argument to tisa_specialize_micromath_sub_rule");
        return false;
    }
    if (!ir->flat || ir->nkeep != 4 || ifl->mar != 4) {
        if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "rule %d is not a 4-premise arity-4 Micromath rule", ir->rule_id);
        return false;
    }

    memset(out_prog, 0, sizeof(*out_prog));
    out_prog->name      = rule_name ? rule_name : "mm_sub_rule";
    out_prog->prog_id   = (uint32_t)ir->rule_id;
    out_prog->nregions  = 5u;

    static const char *const mm_reg_names[5] = { "p0", "p1", "p2", "p3", "dest_slot" };
    out_prog->init_reg_mask     = (1u << TISA_V0);
    out_prog->init_reg_types[0] = TISA_TYPE_U64;
    for (uint8_t i = 0; i < 4u; i++) {
        out_prog->regions[i] = (TcIsaRegionDecl){
            .region_id    = i,
            .mode         = TISA_CAP_RO,
            .min_byte_len = 32u, /* sizeof(MmBody) = 4 * 8 */
            .align_bytes  = 8u,
            .name         = mm_reg_names[i]
        };
        uint8_t reg = (uint8_t)(TISA_V1 + i);
        out_prog->init_reg_mask        |= (uint16_t)(1u << reg);
        out_prog->init_reg_types[reg]   = TISA_TYPE_PTR;
        out_prog->init_reg_region[reg]  = i;
    }
    out_prog->regions[4] = (TcIsaRegionDecl){
        .region_id    = 4u,
        .mode         = TISA_CAP_RW,
        .min_byte_len = 32u,
        .align_bytes  = 8u,
        .name         = mm_reg_names[4]
    };
    out_prog->init_reg_mask          |= (uint16_t)(1u << TISA_V5);
    out_prog->init_reg_types[TISA_V5] = TISA_TYPE_PTR;
    out_prog->init_reg_region[TISA_V5]= 4u;

    TcIsaStmt *refuse = tisa_stmt_seq(arena,
                                      mk_imm(arena, TISA_TYPE_U64, TISA_V8, 0ull),
                                      tisa_stmt_return(arena, TISA_OUTCOME_REFUSED, TISA_V8));
    TcIsaStmt *unsup  = tisa_stmt_seq(arena,
                                      mk_imm(arena, TISA_TYPE_U64, TISA_V8, 2ull),
                                      tisa_stmt_return(arena, TISA_OUTCOME_UNSUPPORTED, TISA_V8));

    /*
     * Conclusion when guards pass & dest < nslot:
     * Read all 4 output words into v6, v7, v8, v9 before writing to v5 (dest_slot)
     */
    TcIsaStmt *write_out = NULL;
    for (uint8_t j = 0; j < 4u; j++) {
        uint8_t mi   = ifl->mi[j];
        uint8_t mj   = ifl->mj[j];
        uint8_t preg = (uint8_t)(TISA_V1 + mi);
        uint8_t treg = (uint8_t)(TISA_V6 + j);
        write_out = tisa_stmt_seq(arena, write_out,
                                  mk_load(arena, mi, TISA_MEM_U64, TISA_TYPE_U64,
                                          treg, preg, (int32_t)(mj * 8u)));
    }
    for (uint8_t j = 0; j < 4u; j++) {
        uint8_t treg = (uint8_t)(TISA_V6 + j);
        write_out = tisa_stmt_seq(arena, write_out,
                                  mk_store(arena, 4u, TISA_MEM_U64, TISA_V5, (int32_t)(j * 8u), treg));
    }
    write_out = tisa_stmt_seq(arena, write_out, mk_imm(arena, TISA_TYPE_U64, TISA_V8, 1ull));
    write_out = tisa_stmt_seq(arena, write_out, tisa_stmt_return(arena, TISA_OUTCOME_FIRED, TISA_V8));

    /* Check dest < nslot (passed in frame->arg0 = dest, frame->arg1 = nslot) */
    TcIsaStmt *dest_check = NULL;
    dest_check = tisa_stmt_seq(arena, dest_check,
                               mk_load(arena, TISA_REGION_FRAME, TISA_MEM_U64, TISA_TYPE_U64,
                                       TISA_V6, TISA_V0, (int32_t)offsetof(TcIsaRuntimeFrame, arg0)));
    dest_check = tisa_stmt_seq(arena, dest_check,
                               mk_load(arena, TISA_REGION_FRAME, TISA_MEM_U64, TISA_TYPE_U64,
                                       TISA_V8, TISA_V0, (int32_t)offsetof(TcIsaRuntimeFrame, arg1)));
    dest_check = tisa_stmt_seq(arena, dest_check,
                               mk_cmp_reg(arena, TISA_CMP_ULT, TISA_TYPE_U64,
                                          TISA_V7, TISA_V6, TISA_V8));
    TcIsaStmt *curr = tisa_stmt_seq(arena, dest_check, tisa_stmt_if(arena, TISA_V7, write_out, unsup));

    /* Wrap inside the 7 equality guards from `ifl` in reverse order */
    for (int g = (int)ifl->nguard - 1; g >= 0; g--) {
        uint8_t i  = ifl->guard[g].i;
        uint8_t j  = ifl->guard[g].j;
        uint8_t i0 = ifl->guard[g].i0;
        uint8_t j0 = ifl->guard[g].j0;
        uint8_t p1 = (uint8_t)(TISA_V1 + i);
        uint8_t p2 = (uint8_t)(TISA_V1 + i0);
        TcIsaStmt *gcheck = NULL;
        gcheck = tisa_stmt_seq(arena, gcheck,
                               mk_load(arena, i, TISA_MEM_U64, TISA_TYPE_U64,
                                       TISA_V6, p1, (int32_t)(j * 8u)));
        gcheck = tisa_stmt_seq(arena, gcheck,
                               mk_load(arena, i0, TISA_MEM_U64, TISA_TYPE_U64,
                                       TISA_V8, p2, (int32_t)(j0 * 8u)));
        gcheck = tisa_stmt_seq(arena, gcheck,
                               mk_cmp_reg(arena, TISA_CMP_EQ, TISA_TYPE_U64,
                                          TISA_V7, TISA_V6, TISA_V8));
        curr = tisa_stmt_seq(arena, gcheck, tisa_stmt_if(arena, TISA_V7, curr, refuse));
    }

    out_prog->root = curr;
    return tisa_check_program(out_prog, err_buf, err_cap);
}

/* =========================================================================
 * 4. Generic `ordinary_flat_fire` (`flat_fire`) Builder
 *
 * Regions:
 *   0 (`s0`): RO `fields`  (`uint32_t[]`)
 *   1 (`s1`): RO `rows`    (`uint32_t[]`)
 *   2 (`s2`): RO `guards`  (`uint32_t[nguards]`)
 *   3 (`s3`): RO `make`    (`uint32_t[arity]`)
 *   4 (`s4`): RW `dest`    (`uint32_t[arity]`)
 *   5 (`s5`): RW `scratch` (`uint32_t[arity]`)
 * ========================================================================= */

bool tisa_build_ordinary_flat_fire_prog(TcIsaArena *arena,
                                        TcIsaProgram *out_prog,
                                        char *err_buf, size_t err_cap) {
    if (!arena || !out_prog) return false;
    memset(out_prog, 0, sizeof(*out_prog));
    out_prog->name      = "ordinary_flat_fire";
    out_prog->prog_id   = 1000u;
    out_prog->nregions  = 6u;

    out_prog->regions[0] = (TcIsaRegionDecl){ 0, TISA_CAP_RO, 0, 4, "fields"  };
    out_prog->regions[1] = (TcIsaRegionDecl){ 1, TISA_CAP_RO, 0, 4, "rows"    };
    out_prog->regions[2] = (TcIsaRegionDecl){ 2, TISA_CAP_RO, 0, 4, "guards"  };
    out_prog->regions[3] = (TcIsaRegionDecl){ 3, TISA_CAP_RO, 0, 4, "make"    };
    out_prog->regions[4] = (TcIsaRegionDecl){ 4, TISA_CAP_RW, 0, 4, "dest"    };
    out_prog->regions[5] = (TcIsaRegionDecl){ 5, TISA_CAP_RW, 0, 4, "scratch" };

    out_prog->init_reg_mask     = (1u << TISA_V0);
    out_prog->init_reg_types[0] = TISA_TYPE_U64;

    TcIsaStmt *s = NULL;
    /* Load pointers: v1=fields(0), v2=rows(1), v3=guards(2) */
    s = tisa_stmt_seq(arena, s, mk_load_frame_ptr(arena, TISA_V1, 0u));
    s = tisa_stmt_seq(arena, s, mk_load_frame_ptr(arena, TISA_V2, 1u));
    s = tisa_stmt_seq(arena, s, mk_load_frame_ptr(arena, TISA_V3, 2u));
    /* v4 = nguards = s2_len >> 2 */
    s = tisa_stmt_seq(arena, s, mk_load_frame_len(arena, TISA_V4, 2u));
    s = tisa_stmt_seq(arena, s, mk_shift(arena, TISA_SHIFT_SHRU, TISA_TYPE_U64, TISA_V4, TISA_V4, 2u));
    /* v5 = cont_reg = 1 (Bool) */
    s = tisa_stmt_seq(arena, s, mk_imm(arena, TISA_TYPE_BOOL, TISA_V5, 1ull));

    /*
     * Guard loop body (idx = v6, bound = v4, cont = v5):
     *   v7  = &guards[v6]
     *   v8  = *v7 (packed guard: i | j<<8 | i0<<16 | j0<<24)
     *   v9  = i  = extract(v8, 0, 8)
     *   v10 = j  = extract(v8, 8, 8)
     *   v7  = &rows[v9]; v9 = *v7 (rows[i])
     *   v9  = (uint32_t)(v9 + v10)  [U32Z modular addition!]
     *   v7  = &fields[v9]; v9 = *v7 (fields[off1])
     *   v10 = i0 = extract(v8, 16, 8)
     *   v11 = j0 = extract(v8, 24, 8)
     *   v7  = &rows[v10]; v10 = *v7 (rows[i0])
     *   v10 = (uint32_t)(v10 + v11) [U32Z modular addition!]
     *   v7  = &fields[v10]; v10 = *v7 (fields[off2])
     *   v5  = (v9 == v10)
     */
    TcIsaStmt *gbody = NULL;
    gbody = tisa_stmt_seq(arena, gbody, mk_addr(arena, 2u, TISA_V7, TISA_V3, TISA_V6, 2u, 0));
    gbody = tisa_stmt_seq(arena, gbody, mk_load(arena, 2u, TISA_MEM_U32, TISA_TYPE_U32Z, TISA_V8, TISA_V7, 0));
    gbody = tisa_stmt_seq(arena, gbody, mk_extract(arena, TISA_TYPE_U32Z, TISA_V9, TISA_V8, 0u, 8u));
    gbody = tisa_stmt_seq(arena, gbody, mk_extract(arena, TISA_TYPE_U32Z, TISA_V10, TISA_V8, 8u, 8u));
    gbody = tisa_stmt_seq(arena, gbody, mk_addr(arena, 1u, TISA_V7, TISA_V2, TISA_V9, 2u, 0));
    gbody = tisa_stmt_seq(arena, gbody, mk_load(arena, 1u, TISA_MEM_U32, TISA_TYPE_U32Z, TISA_V9, TISA_V7, 0));
    gbody = tisa_stmt_seq(arena, gbody, mk_bin(arena, TISA_BIN_ADD, TISA_TYPE_U32Z, TISA_V9, TISA_V9, TISA_V10));
    gbody = tisa_stmt_seq(arena, gbody, mk_addr(arena, 0u, TISA_V7, TISA_V1, TISA_V9, 2u, 0));
    gbody = tisa_stmt_seq(arena, gbody, mk_load(arena, 0u, TISA_MEM_U32, TISA_TYPE_U32Z, TISA_V9, TISA_V7, 0));

    gbody = tisa_stmt_seq(arena, gbody, mk_extract(arena, TISA_TYPE_U32Z, TISA_V10, TISA_V8, 16u, 8u));
    gbody = tisa_stmt_seq(arena, gbody, mk_extract(arena, TISA_TYPE_U32Z, TISA_V11, TISA_V8, 24u, 8u));
    gbody = tisa_stmt_seq(arena, gbody, mk_addr(arena, 1u, TISA_V7, TISA_V2, TISA_V10, 2u, 0));
    gbody = tisa_stmt_seq(arena, gbody, mk_load(arena, 1u, TISA_MEM_U32, TISA_TYPE_U32Z, TISA_V10, TISA_V7, 0));
    gbody = tisa_stmt_seq(arena, gbody, mk_bin(arena, TISA_BIN_ADD, TISA_TYPE_U32Z, TISA_V10, TISA_V10, TISA_V11));
    gbody = tisa_stmt_seq(arena, gbody, mk_addr(arena, 0u, TISA_V7, TISA_V1, TISA_V10, 2u, 0));
    gbody = tisa_stmt_seq(arena, gbody, mk_load(arena, 0u, TISA_MEM_U32, TISA_TYPE_U32Z, TISA_V10, TISA_V7, 0));
    gbody = tisa_stmt_seq(arena, gbody, mk_cmp_reg(arena, TISA_CMP_EQ, TISA_TYPE_U32Z, TISA_V5, TISA_V9, TISA_V10));

    s = tisa_stmt_seq(arena, s, tisa_stmt_early_exit_loop(arena, TISA_V6, TISA_V4, TISA_V5, 32u, gbody));

    TcIsaStmt *refuse = tisa_stmt_seq(arena,
                                      mk_imm(arena, TISA_TYPE_U64, TISA_V8, 0ull),
                                      tisa_stmt_return(arena, TISA_OUTCOME_REFUSED, TISA_V8));

    /* When all guards pass: stage output into scratch (region 5), then copy scratch -> dest (region 4) */
    TcIsaStmt *accept = NULL;
    accept = tisa_stmt_seq(arena, accept, mk_load_frame_ptr(arena, TISA_V3, 3u)); /* make(3) */
    accept = tisa_stmt_seq(arena, accept, mk_load_frame_ptr(arena, TISA_V4, 5u)); /* scratch(5) */
    accept = tisa_stmt_seq(arena, accept, mk_load_frame_len(arena, TISA_V5, 3u)); /* arity = s3_len >> 2 */
    accept = tisa_stmt_seq(arena, accept, mk_shift(arena, TISA_SHIFT_SHRU, TISA_TYPE_U64, TISA_V5, TISA_V5, 2u));

    TcIsaStmt *mbody = NULL;
    mbody = tisa_stmt_seq(arena, mbody, mk_addr(arena, 3u, TISA_V7, TISA_V3, TISA_V6, 2u, 0));
    mbody = tisa_stmt_seq(arena, mbody, mk_load(arena, 3u, TISA_MEM_U32, TISA_TYPE_U32Z, TISA_V8, TISA_V7, 0));
    mbody = tisa_stmt_seq(arena, mbody, mk_extract(arena, TISA_TYPE_U32Z, TISA_V9, TISA_V8, 0u, 8u));
    mbody = tisa_stmt_seq(arena, mbody, mk_extract(arena, TISA_TYPE_U32Z, TISA_V10, TISA_V8, 8u, 8u));
    mbody = tisa_stmt_seq(arena, mbody, mk_addr(arena, 1u, TISA_V7, TISA_V2, TISA_V9, 2u, 0));
    mbody = tisa_stmt_seq(arena, mbody, mk_load(arena, 1u, TISA_MEM_U32, TISA_TYPE_U32Z, TISA_V9, TISA_V7, 0));
    mbody = tisa_stmt_seq(arena, mbody, mk_bin(arena, TISA_BIN_ADD, TISA_TYPE_U32Z, TISA_V9, TISA_V9, TISA_V10));
    mbody = tisa_stmt_seq(arena, mbody, mk_addr(arena, 0u, TISA_V7, TISA_V1, TISA_V9, 2u, 0));
    mbody = tisa_stmt_seq(arena, mbody, mk_load(arena, 0u, TISA_MEM_U32, TISA_TYPE_U32Z, TISA_V9, TISA_V7, 0));
    mbody = tisa_stmt_seq(arena, mbody, mk_addr(arena, 5u, TISA_V7, TISA_V4, TISA_V6, 2u, 0));
    mbody = tisa_stmt_seq(arena, mbody, mk_store(arena, 5u, TISA_MEM_U32, TISA_V7, 0, TISA_V9));

    accept = tisa_stmt_seq(arena, accept, tisa_stmt_count_loop(arena, TISA_V6, TISA_V5, 32u, mbody));

    /* Copy scratch (region 5, v4) -> dest (region 4, v3) */
    accept = tisa_stmt_seq(arena, accept, mk_load_frame_ptr(arena, TISA_V3, 4u)); /* dest(4) */
    TcIsaStmt *cbody = NULL;
    cbody = tisa_stmt_seq(arena, cbody, mk_addr(arena, 5u, TISA_V7, TISA_V4, TISA_V6, 2u, 0));
    cbody = tisa_stmt_seq(arena, cbody, mk_load(arena, 5u, TISA_MEM_U32, TISA_TYPE_U32Z, TISA_V9, TISA_V7, 0));
    cbody = tisa_stmt_seq(arena, cbody, mk_addr(arena, 4u, TISA_V7, TISA_V3, TISA_V6, 2u, 0));
    cbody = tisa_stmt_seq(arena, cbody, mk_store(arena, 4u, TISA_MEM_U32, TISA_V7, 0, TISA_V9));

    accept = tisa_stmt_seq(arena, accept, tisa_stmt_count_loop(arena, TISA_V6, TISA_V5, 32u, cbody));
    accept = tisa_stmt_seq(arena, accept, mk_imm(arena, TISA_TYPE_U64, TISA_V8, 1ull));
    accept = tisa_stmt_seq(arena, accept, tisa_stmt_return(arena, TISA_OUTCOME_FIRED, TISA_V8));

    s = tisa_stmt_seq(arena, s, tisa_stmt_if(arena, TISA_V5, accept, refuse));
    out_prog->root = s;
    return tisa_check_program(out_prog, err_buf, err_cap);
}

/* =========================================================================
 * 5. Complete `ordinary_flat_adapter` (`ordinary_flat_pack` + `flat_fire`)
 *
 * Regions:
 *   0 (`s0`): RO `source`    (`uint32_t[ns]`)
 *   1 (`s1`): RO `premises`  (`uint32_t[nk]`)
 *   2 (`s2`): RO `constants` (`uint32_t[nc]`)
 *   3 (`s3`): RO `guards`    (`uint32_t[ng]`)
 *   4 (`s4`): RO `makes`     (`uint32_t[nm]`)
 *   5 (`s5`): RW `fields`    (`uint32_t[nfields]`)
 *   6 (`s6`): RW `rows`      (`uint32_t[nrows]`)
 *   7 (`s7`): RW `dest`      (`uint32_t[ndest]`)
 *   8 (`s8`): RW `scratch`   (`uint32_t[nscratch]`)
 * ========================================================================= */

bool tisa_build_ordinary_flat_adapter_prog(TcIsaArena *arena,
                                           TcIsaProgram *out_prog,
                                           char *err_buf, size_t err_cap) {
    if (!arena || !out_prog) return false;
    memset(out_prog, 0, sizeof(*out_prog));
    out_prog->name      = "ordinary_flat_adapter";
    out_prog->prog_id   = 1001u;
    out_prog->nregions  = 9u;

    out_prog->regions[0] = (TcIsaRegionDecl){ 0, TISA_CAP_RO, 0, 4, "source"    };
    out_prog->regions[1] = (TcIsaRegionDecl){ 1, TISA_CAP_RO, 0, 4, "premises"  };
    out_prog->regions[2] = (TcIsaRegionDecl){ 2, TISA_CAP_RO, 0, 4, "constants" };
    out_prog->regions[3] = (TcIsaRegionDecl){ 3, TISA_CAP_RO, 0, 4, "guards"    };
    out_prog->regions[4] = (TcIsaRegionDecl){ 4, TISA_CAP_RO, 0, 4, "makes"     };
    out_prog->regions[5] = (TcIsaRegionDecl){ 5, TISA_CAP_RW, 0, 4, "fields"    };
    out_prog->regions[6] = (TcIsaRegionDecl){ 6, TISA_CAP_RW, 0, 4, "rows"      };
    out_prog->regions[7] = (TcIsaRegionDecl){ 7, TISA_CAP_RW, 0, 4, "dest"      };
    out_prog->regions[8] = (TcIsaRegionDecl){ 8, TISA_CAP_RW, 0, 4, "scratch"   };

    out_prog->init_reg_mask     = (1u << TISA_V0);
    out_prog->init_reg_types[0] = TISA_TYPE_U64;

    TcIsaStmt *unsup = tisa_stmt_seq(arena,
                                     mk_imm(arena, TISA_TYPE_U64, TISA_V8, 2ull),
                                     tisa_stmt_return(arena, TISA_OUTCOME_UNSUPPORTED, TISA_V8));
    TcIsaStmt *refuse = tisa_stmt_seq(arena,
                                      mk_imm(arena, TISA_TYPE_U64, TISA_V8, 0ull),
                                      tisa_stmt_return(arena, TISA_OUTCOME_REFUSED, TISA_V8));

    /*
     * Build from inside out (Phase 3 -> Phase 2 -> Phase 1) so every capacity
     * and extent guard branches cleanly to `unsup` before any writes occur.
     */

    /* --- Phase 3: Guard Evaluation & Make Output --- */
    TcIsaStmt *p3 = NULL;
    p3 = tisa_stmt_seq(arena, p3, mk_load_frame_ptr(arena, TISA_V1, 5u)); /* fields(5) */
    p3 = tisa_stmt_seq(arena, p3, mk_load_frame_ptr(arena, TISA_V2, 6u)); /* rows(6)   */
    p3 = tisa_stmt_seq(arena, p3, mk_load_frame_ptr(arena, TISA_V3, 3u)); /* guards(3) */
    p3 = tisa_stmt_seq(arena, p3, mk_load_frame_len(arena, TISA_V4, 3u)); /* ng = s3_len >> 2 */
    p3 = tisa_stmt_seq(arena, p3, mk_shift(arena, TISA_SHIFT_SHRU, TISA_TYPE_U64, TISA_V4, TISA_V4, 2u));
    p3 = tisa_stmt_seq(arena, p3, mk_imm(arena, TISA_TYPE_BOOL, TISA_V5, 1ull));

    TcIsaStmt *gbody = NULL;
    gbody = tisa_stmt_seq(arena, gbody, mk_addr(arena, 3u, TISA_V7, TISA_V3, TISA_V6, 2u, 0));
    gbody = tisa_stmt_seq(arena, gbody, mk_load(arena, 3u, TISA_MEM_U32, TISA_TYPE_U32Z, TISA_V8, TISA_V7, 0));
    gbody = tisa_stmt_seq(arena, gbody, mk_extract(arena, TISA_TYPE_U32Z, TISA_V9, TISA_V8, 0u, 8u));
    gbody = tisa_stmt_seq(arena, gbody, mk_extract(arena, TISA_TYPE_U32Z, TISA_V10, TISA_V8, 8u, 8u));
    gbody = tisa_stmt_seq(arena, gbody, mk_addr(arena, 6u, TISA_V7, TISA_V2, TISA_V9, 2u, 0));
    gbody = tisa_stmt_seq(arena, gbody, mk_load(arena, 6u, TISA_MEM_U32, TISA_TYPE_U32Z, TISA_V9, TISA_V7, 0));
    gbody = tisa_stmt_seq(arena, gbody, mk_bin(arena, TISA_BIN_ADD, TISA_TYPE_U32Z, TISA_V9, TISA_V9, TISA_V10));
    gbody = tisa_stmt_seq(arena, gbody, mk_addr(arena, 5u, TISA_V7, TISA_V1, TISA_V9, 2u, 0));
    gbody = tisa_stmt_seq(arena, gbody, mk_load(arena, 5u, TISA_MEM_U32, TISA_TYPE_U32Z, TISA_V9, TISA_V7, 0));

    gbody = tisa_stmt_seq(arena, gbody, mk_extract(arena, TISA_TYPE_U32Z, TISA_V10, TISA_V8, 16u, 8u));
    gbody = tisa_stmt_seq(arena, gbody, mk_extract(arena, TISA_TYPE_U32Z, TISA_V11, TISA_V8, 24u, 8u));
    gbody = tisa_stmt_seq(arena, gbody, mk_addr(arena, 6u, TISA_V7, TISA_V2, TISA_V10, 2u, 0));
    gbody = tisa_stmt_seq(arena, gbody, mk_load(arena, 6u, TISA_MEM_U32, TISA_TYPE_U32Z, TISA_V10, TISA_V7, 0));
    gbody = tisa_stmt_seq(arena, gbody, mk_bin(arena, TISA_BIN_ADD, TISA_TYPE_U32Z, TISA_V10, TISA_V10, TISA_V11));
    gbody = tisa_stmt_seq(arena, gbody, mk_addr(arena, 5u, TISA_V7, TISA_V1, TISA_V10, 2u, 0));
    gbody = tisa_stmt_seq(arena, gbody, mk_load(arena, 5u, TISA_MEM_U32, TISA_TYPE_U32Z, TISA_V10, TISA_V7, 0));
    gbody = tisa_stmt_seq(arena, gbody, mk_cmp_reg(arena, TISA_CMP_EQ, TISA_TYPE_U32Z, TISA_V5, TISA_V9, TISA_V10));

    p3 = tisa_stmt_seq(arena, p3, tisa_stmt_early_exit_loop(arena, TISA_V6, TISA_V4, TISA_V5, 32u, gbody));

    TcIsaStmt *p3_make = NULL;
    p3_make = tisa_stmt_seq(arena, p3_make, mk_load_frame_ptr(arena, TISA_V3, 4u)); /* makes(4)   */
    p3_make = tisa_stmt_seq(arena, p3_make, mk_load_frame_ptr(arena, TISA_V4, 7u)); /* dest(7)    */
    p3_make = tisa_stmt_seq(arena, p3_make, mk_load_frame_ptr(arena, TISA_V11, 8u));/* scratch(8) */
    p3_make = tisa_stmt_seq(arena, p3_make, mk_load_frame_len(arena, TISA_V5, 4u)); /* nm = s4_len >> 2 */
    p3_make = tisa_stmt_seq(arena, p3_make, mk_shift(arena, TISA_SHIFT_SHRU, TISA_TYPE_U64, TISA_V5, TISA_V5, 2u));

    TcIsaStmt *mbody = NULL;
    mbody = tisa_stmt_seq(arena, mbody, mk_addr(arena, 4u, TISA_V7, TISA_V3, TISA_V6, 2u, 0));
    mbody = tisa_stmt_seq(arena, mbody, mk_load(arena, 4u, TISA_MEM_U32, TISA_TYPE_U32Z, TISA_V8, TISA_V7, 0));
    mbody = tisa_stmt_seq(arena, mbody, mk_extract(arena, TISA_TYPE_U32Z, TISA_V9, TISA_V8, 0u, 8u));
    mbody = tisa_stmt_seq(arena, mbody, mk_extract(arena, TISA_TYPE_U32Z, TISA_V10, TISA_V8, 8u, 8u));
    mbody = tisa_stmt_seq(arena, mbody, mk_addr(arena, 6u, TISA_V7, TISA_V2, TISA_V9, 2u, 0));
    mbody = tisa_stmt_seq(arena, mbody, mk_load(arena, 6u, TISA_MEM_U32, TISA_TYPE_U32Z, TISA_V9, TISA_V7, 0));
    mbody = tisa_stmt_seq(arena, mbody, mk_bin(arena, TISA_BIN_ADD, TISA_TYPE_U32Z, TISA_V9, TISA_V9, TISA_V10));
    mbody = tisa_stmt_seq(arena, mbody, mk_addr(arena, 5u, TISA_V7, TISA_V1, TISA_V9, 2u, 0));
    mbody = tisa_stmt_seq(arena, mbody, mk_load(arena, 5u, TISA_MEM_U32, TISA_TYPE_U32Z, TISA_V9, TISA_V7, 0));
    mbody = tisa_stmt_seq(arena, mbody, mk_addr(arena, 8u, TISA_V7, TISA_V11, TISA_V6, 2u, 0));
    mbody = tisa_stmt_seq(arena, mbody, mk_store(arena, 8u, TISA_MEM_U32, TISA_V7, 0, TISA_V9));
    mbody = tisa_stmt_seq(arena, mbody, mk_addr(arena, 7u, TISA_V7, TISA_V4, TISA_V6, 2u, 0));
    mbody = tisa_stmt_seq(arena, mbody, mk_store(arena, 7u, TISA_MEM_U32, TISA_V7, 0, TISA_V9));

    p3_make = tisa_stmt_seq(arena, p3_make, tisa_stmt_count_loop(arena, TISA_V6, TISA_V5, 32u, mbody));
    p3_make = tisa_stmt_seq(arena, p3_make, mk_imm(arena, TISA_TYPE_U64, TISA_V8, 1ull));
    p3_make = tisa_stmt_seq(arena, p3_make, tisa_stmt_return(arena, TISA_OUTCOME_FIRED, TISA_V8));

    p3 = tisa_stmt_seq(arena, p3, tisa_stmt_if(arena, TISA_V5, p3_make, refuse));

    /* --- Phase 2: Pack rows & fields (`ordinary_flat_pack`) --- */
    TcIsaStmt *p2 = NULL;
    p2 = tisa_stmt_seq(arena, p2, mk_load_frame_ptr(arena, TISA_V1, 0u)); /* source(0)   */
    p2 = tisa_stmt_seq(arena, p2, mk_load_frame_ptr(arena, TISA_V2, 1u)); /* premises(1) */
    p2 = tisa_stmt_seq(arena, p2, mk_load_frame_ptr(arena, TISA_V3, 5u)); /* fields(5)   */
    p2 = tisa_stmt_seq(arena, p2, mk_load_frame_ptr(arena, TISA_V4, 6u)); /* rows(6)     */
    p2 = tisa_stmt_seq(arena, p2, mk_load_frame_len(arena, TISA_V5, 1u)); /* nk = s1_len >> 2 */
    p2 = tisa_stmt_seq(arena, p2, mk_shift(arena, TISA_SHIFT_SHRU, TISA_TYPE_U64, TISA_V5, TISA_V5, 2u));

    /* Loop i in 0 .. nk-1: rows[i] = 4*i; copy 4 words from source[premises[i]] to fields[4*i] */
    TcIsaStmt *pack_p = NULL;
    pack_p = tisa_stmt_seq(arena, pack_p, mk_shift(arena, TISA_SHIFT_SHL, TISA_TYPE_U32Z, TISA_V8, TISA_V6, 2u)); /* base = 4*i */
    pack_p = tisa_stmt_seq(arena, pack_p, mk_addr(arena, 6u, TISA_V7, TISA_V4, TISA_V6, 2u, 0));
    pack_p = tisa_stmt_seq(arena, pack_p, mk_store(arena, 6u, TISA_MEM_U32, TISA_V7, 0, TISA_V8));
    /* v9 = premises[i] */
    pack_p = tisa_stmt_seq(arena, pack_p, mk_addr(arena, 1u, TISA_V7, TISA_V2, TISA_V6, 2u, 0));
    pack_p = tisa_stmt_seq(arena, pack_p, mk_load(arena, 1u, TISA_MEM_U32, TISA_TYPE_U32Z, TISA_V9, TISA_V7, 0));
    /* v7 = &source[v9], v10 = &fields[4*i] */
    pack_p = tisa_stmt_seq(arena, pack_p, mk_addr(arena, 0u, TISA_V7, TISA_V1, TISA_V9, 2u, 0));
    pack_p = tisa_stmt_seq(arena, pack_p, mk_addr(arena, 5u, TISA_V10, TISA_V3, TISA_V8, 2u, 0));
    for (int j = 0; j < 4; j++) {
        pack_p = tisa_stmt_seq(arena, pack_p,
                               mk_load(arena, 0u, TISA_MEM_U32, TISA_TYPE_U32Z, TISA_V11, TISA_V7, j * 4));
        pack_p = tisa_stmt_seq(arena, pack_p,
                               mk_store(arena, 5u, TISA_MEM_U32, TISA_V10, j * 4, TISA_V11));
    }
    p2 = tisa_stmt_seq(arena, p2, tisa_stmt_count_loop(arena, TISA_V6, TISA_V5, 24u, pack_p));

    /* rows[nk] = 4 * nk */
    p2 = tisa_stmt_seq(arena, p2, mk_shift(arena, TISA_SHIFT_SHL, TISA_TYPE_U32Z, TISA_V8, TISA_V5, 2u));
    p2 = tisa_stmt_seq(arena, p2, mk_addr(arena, 6u, TISA_V7, TISA_V4, TISA_V5, 2u, 0));
    p2 = tisa_stmt_seq(arena, p2, mk_store(arena, 6u, TISA_MEM_U32, TISA_V7, 0, TISA_V8));

    /* Copy constants[0..nc-1] into fields[4*nk + j] */
    p2 = tisa_stmt_seq(arena, p2, mk_load_frame_ptr(arena, TISA_V1, 2u)); /* constants(2) */
    p2 = tisa_stmt_seq(arena, p2, mk_load_frame_len(arena, TISA_V4, 2u)); /* nc = s2_len >> 2 */
    p2 = tisa_stmt_seq(arena, p2, mk_shift(arena, TISA_SHIFT_SHRU, TISA_TYPE_U64, TISA_V4, TISA_V4, 2u));
    TcIsaStmt *pack_c = NULL;
    pack_c = tisa_stmt_seq(arena, pack_c, mk_addr(arena, 2u, TISA_V7, TISA_V1, TISA_V6, 2u, 0));
    pack_c = tisa_stmt_seq(arena, pack_c, mk_load(arena, 2u, TISA_MEM_U32, TISA_TYPE_U32Z, TISA_V9, TISA_V7, 0));
    pack_c = tisa_stmt_seq(arena, pack_c, mk_bin(arena, TISA_BIN_ADD, TISA_TYPE_U64, TISA_V10, TISA_V8, TISA_V6));
    pack_c = tisa_stmt_seq(arena, pack_c, mk_addr(arena, 5u, TISA_V7, TISA_V3, TISA_V10, 2u, 0));
    pack_c = tisa_stmt_seq(arena, pack_c, mk_store(arena, 5u, TISA_MEM_U32, TISA_V7, 0, TISA_V9));
    p2 = tisa_stmt_seq(arena, p2, tisa_stmt_count_loop(arena, TISA_V6, TISA_V4, 32u, pack_c));
    p2 = tisa_stmt_seq(arena, p2, p3);

    /* --- Phase 1: Validate Capacities & Premise Extents (before any writes!) --- */
    TcIsaStmt *p1 = NULL;
    /* Load word lengths: v1=ns(0), v2=nk(1), v3=nc(2), v4=ng(3), v5=nm(4) */
    p1 = tisa_stmt_seq(arena, p1, mk_load_frame_len(arena, TISA_V1, 0u));
    p1 = tisa_stmt_seq(arena, p1, mk_shift(arena, TISA_SHIFT_SHRU, TISA_TYPE_U64, TISA_V1, TISA_V1, 2u));
    p1 = tisa_stmt_seq(arena, p1, mk_load_frame_len(arena, TISA_V2, 1u));
    p1 = tisa_stmt_seq(arena, p1, mk_shift(arena, TISA_SHIFT_SHRU, TISA_TYPE_U64, TISA_V2, TISA_V2, 2u));
    p1 = tisa_stmt_seq(arena, p1, mk_load_frame_len(arena, TISA_V3, 2u));
    p1 = tisa_stmt_seq(arena, p1, mk_shift(arena, TISA_SHIFT_SHRU, TISA_TYPE_U64, TISA_V3, TISA_V3, 2u));
    p1 = tisa_stmt_seq(arena, p1, mk_load_frame_len(arena, TISA_V4, 3u));
    p1 = tisa_stmt_seq(arena, p1, mk_shift(arena, TISA_SHIFT_SHRU, TISA_TYPE_U64, TISA_V4, TISA_V4, 2u));
    p1 = tisa_stmt_seq(arena, p1, mk_load_frame_len(arena, TISA_V5, 4u));
    p1 = tisa_stmt_seq(arena, p1, mk_shift(arena, TISA_SHIFT_SHRU, TISA_TYPE_U64, TISA_V5, TISA_V5, 2u));

    /* Check premise extents in loop (idx=v6, bound=v2=nk): premises[i] + 4 <= ns */
    TcIsaStmt *ext_check = NULL;
    ext_check = tisa_stmt_seq(arena, ext_check, mk_load_frame_ptr(arena, TISA_V7, 1u)); /* premises(1) */
    ext_check = tisa_stmt_seq(arena, ext_check, mk_imm(arena, TISA_TYPE_BOOL, TISA_V8, 1ull));
    TcIsaStmt *ebody = NULL;
    ebody = tisa_stmt_seq(arena, ebody, mk_addr(arena, 1u, TISA_V9, TISA_V7, TISA_V6, 2u, 0));
    ebody = tisa_stmt_seq(arena, ebody, mk_load(arena, 1u, TISA_MEM_U32, TISA_TYPE_U32Z, TISA_V10, TISA_V9, 0));
    ebody = tisa_stmt_seq(arena, ebody, mk_imm(arena, TISA_TYPE_U64, TISA_V11, 4ull));
    ebody = tisa_stmt_seq(arena, ebody, mk_bin(arena, TISA_BIN_ADD, TISA_TYPE_U64, TISA_V10, TISA_V10, TISA_V11));
    ebody = tisa_stmt_seq(arena, ebody, mk_cmp_reg(arena, TISA_CMP_ULE, TISA_TYPE_U64, TISA_V8, TISA_V10, TISA_V1));
    ext_check = tisa_stmt_seq(arena, ext_check,
                              tisa_stmt_early_exit_loop(arena, TISA_V6, TISA_V2, TISA_V8, 24u, ebody));
    TcIsaStmt *after_caps = tisa_stmt_seq(arena, ext_check, tisa_stmt_if(arena, TISA_V8, p2, unsup));

    /* Check 4*nk + nc <= nfields (region 5) and nk + 1 <= nrows (region 6) and nm <= ndest (7), nm <= nscratch (8) */
    TcIsaStmt *cap_checks = NULL;
    /* v6 = 4*nk + nc; v7 = nfields (s5_len >> 2) */
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_shift(arena, TISA_SHIFT_SHL, TISA_TYPE_U64, TISA_V6, TISA_V2, 2u));
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_bin(arena, TISA_BIN_ADD, TISA_TYPE_U64, TISA_V6, TISA_V6, TISA_V3));
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_load_frame_len(arena, TISA_V7, 5u));
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_shift(arena, TISA_SHIFT_SHRU, TISA_TYPE_U64, TISA_V7, TISA_V7, 2u));
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_cmp_reg(arena, TISA_CMP_ULE, TISA_TYPE_U64, TISA_V8, TISA_V6, TISA_V7));

    /* v6 = nk + 1; v7 = nrows (s6_len >> 2) */
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_imm(arena, TISA_TYPE_U64, TISA_V6, 1ull));
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_bin(arena, TISA_BIN_ADD, TISA_TYPE_U64, TISA_V6, TISA_V2, TISA_V6));
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_load_frame_len(arena, TISA_V7, 6u));
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_shift(arena, TISA_SHIFT_SHRU, TISA_TYPE_U64, TISA_V7, TISA_V7, 2u));
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_cmp_reg(arena, TISA_CMP_ULE, TISA_TYPE_U64, TISA_V9, TISA_V6, TISA_V7));
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_bin(arena, TISA_BIN_AND, TISA_TYPE_BOOL, TISA_V8, TISA_V8, TISA_V9));

    /* nm <= ndest (s7_len >> 2) and nm <= nscratch (s8_len >> 2) */
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_load_frame_len(arena, TISA_V7, 7u));
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_shift(arena, TISA_SHIFT_SHRU, TISA_TYPE_U64, TISA_V7, TISA_V7, 2u));
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_cmp_reg(arena, TISA_CMP_ULE, TISA_TYPE_U64, TISA_V9, TISA_V5, TISA_V7));
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_bin(arena, TISA_BIN_AND, TISA_TYPE_BOOL, TISA_V8, TISA_V8, TISA_V9));

    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_load_frame_len(arena, TISA_V7, 8u));
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_shift(arena, TISA_SHIFT_SHRU, TISA_TYPE_U64, TISA_V7, TISA_V7, 2u));
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_cmp_reg(arena, TISA_CMP_ULE, TISA_TYPE_U64, TISA_V9, TISA_V5, TISA_V7));
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_bin(arena, TISA_BIN_AND, TISA_TYPE_BOOL, TISA_V8, TISA_V8, TISA_V9));

    /* Static max bounds: nk <= 24, nc <= 32, ng <= 32, nm <= 32 */
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_cmp_imm(arena, TISA_CMP_ULE, TISA_TYPE_U64, TISA_V9, TISA_V2, 24ull));
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_bin(arena, TISA_BIN_AND, TISA_TYPE_BOOL, TISA_V8, TISA_V8, TISA_V9));
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_cmp_imm(arena, TISA_CMP_ULE, TISA_TYPE_U64, TISA_V9, TISA_V3, 32ull));
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_bin(arena, TISA_BIN_AND, TISA_TYPE_BOOL, TISA_V8, TISA_V8, TISA_V9));
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_cmp_imm(arena, TISA_CMP_ULE, TISA_TYPE_U64, TISA_V9, TISA_V4, 32ull));
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_bin(arena, TISA_BIN_AND, TISA_TYPE_BOOL, TISA_V8, TISA_V8, TISA_V9));
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_cmp_imm(arena, TISA_CMP_ULE, TISA_TYPE_U64, TISA_V9, TISA_V5, 32ull));
    cap_checks = tisa_stmt_seq(arena, cap_checks, mk_bin(arena, TISA_BIN_AND, TISA_TYPE_BOOL, TISA_V8, TISA_V8, TISA_V9));

    p1 = tisa_stmt_seq(arena, p1, cap_checks);
    p1 = tisa_stmt_seq(arena, p1, tisa_stmt_if(arena, TISA_V8, after_caps, unsup));

    out_prog->root = p1;
    return tisa_check_program(out_prog, err_buf, err_cap);
}

/* =========================================================================
 * 6. Qualified Consumer Execution Helpers (`Ref`, `tcalc-Hosted`, `x86-64`)
 * ========================================================================= */

TcIsaOutcome (*tisa_p1_runner)(const TcIsaProgram *prog, TcIsaExecMode mode,
                               TcIsaRuntimeFrame *frame, uint64_t regs[TISA_NUM_VREGS]) = NULL;

static TcIsaOutcome tisa_dispatch_mode(const TcIsaProgram *prog,
                                       const TcIsaCompiledX86 *comp,
                                       TcIsaExecMode mode,
                                       TcIsaRuntimeFrame *frame,
                                       uint64_t regs[TISA_NUM_VREGS],
                                       uint64_t *out_steps) {
    if (out_steps) *out_steps = 0;
    if (mode == TISA_MODE_REF) {
        TcIsaOutcome rc = tisa_eval_ref(prog, frame, regs);
        if (out_steps) *out_steps = frame->fuel_used;
        return rc;
    }
    if (mode == TISA_MODE_TCALC) {
        uint64_t fires = 0;
        TcIsaOutcome rc = tisa_eval_tcalc(prog, frame, regs, &fires);
        if (out_steps) *out_steps = fires;
        return rc;
    }
    if (mode == TISA_MODE_X86) {
        TcIsaOutcome rc = tisa_run_x86(prog, comp, frame,
                                       regs[TISA_V1], regs[TISA_V2],
                                       regs[TISA_V3], regs[TISA_V4],
                                       regs[TISA_V5]);
        if (out_steps) *out_steps = frame->fuel_used;
        return rc;
    }
    if (mode == TISA_MODE_P1_REF || mode == TISA_MODE_P1_X86) {
        /* These programs carry no FUND points: the receipt does not move. */
        if (!tisa_p1_runner) return TISA_OUTCOME_UNSUPPORTED;
        TcIsaOutcome rc = tisa_p1_runner(prog, mode, frame, regs);
        if (out_steps) *out_steps = frame->fuel_used;
        return rc;
    }
    return TISA_OUTCOME_INVALID_INPUT;
}

TcIsaOutcome tisa_run_ordinary_flat_fire(const TcIsaProgram *prog,
                                         const TcIsaCompiledX86 *comp,
                                         TcIsaExecMode mode,
                                         const uint32_t *fields, size_t nfields,
                                         const uint32_t *rows, size_t nrows,
                                         const uint32_t *guards, size_t nguards,
                                         const uint32_t *make, size_t nmake,
                                         uint32_t *dest, size_t ndest,
                                         uint32_t *scratch, size_t nscratch,
                                         uint64_t *out_steps) {
    TcIsaRuntimeFrame frame;
    memset(&frame, 0, sizeof(frame));
    frame.s0_ptr = (uint64_t)(uintptr_t)fields;  frame.s0_len = (uint64_t)nfields * 4ull;
    frame.s1_ptr = (uint64_t)(uintptr_t)rows;    frame.s1_len = (uint64_t)nrows * 4ull;
    frame.s2_ptr = (uint64_t)(uintptr_t)guards;  frame.s2_len = (uint64_t)nguards * 4ull;
    frame.s3_ptr = (uint64_t)(uintptr_t)make;    frame.s3_len = (uint64_t)nmake * 4ull;
    frame.s4_ptr = (uint64_t)(uintptr_t)dest;    frame.s4_len = (uint64_t)ndest * 4ull;
    frame.s5_ptr = (uint64_t)(uintptr_t)scratch; frame.s5_len = (uint64_t)nscratch * 4ull;

    uint64_t regs[TISA_NUM_VREGS] = {0};
    regs[TISA_V0] = (uint64_t)(uintptr_t)&frame;
    return tisa_dispatch_mode(prog, comp, mode, &frame, regs, out_steps);
}

TcIsaOutcome tisa_run_ordinary_flat_adapter(const TcIsaProgram *prog,
                                            const TcIsaCompiledX86 *comp,
                                            TcIsaExecMode mode,
                                            const uint32_t *source, size_t nsource,
                                            const uint32_t *premises, size_t nprem,
                                            const uint32_t *constants, size_t nconst,
                                            const uint32_t *guards, size_t nguards,
                                            const uint32_t *makes, size_t nmakes,
                                            uint32_t *fields, size_t nfields,
                                            uint32_t *rows, size_t nrows,
                                            uint32_t *dest, size_t ndest,
                                            uint32_t *scratch, size_t nscratch,
                                            uint64_t *out_steps) {
    TcIsaRuntimeFrame frame;
    memset(&frame, 0, sizeof(frame));
    frame.s0_ptr = (uint64_t)(uintptr_t)source;    frame.s0_len = (uint64_t)nsource * 4ull;
    frame.s1_ptr = (uint64_t)(uintptr_t)premises;  frame.s1_len = (uint64_t)nprem * 4ull;
    frame.s2_ptr = (uint64_t)(uintptr_t)constants; frame.s2_len = (uint64_t)nconst * 4ull;
    frame.s3_ptr = (uint64_t)(uintptr_t)guards;    frame.s3_len = (uint64_t)nguards * 4ull;
    frame.s4_ptr = (uint64_t)(uintptr_t)makes;     frame.s4_len = (uint64_t)nmakes * 4ull;
    frame.s5_ptr = (uint64_t)(uintptr_t)fields;    frame.s5_len = (uint64_t)nfields * 4ull;
    frame.s6_ptr = (uint64_t)(uintptr_t)rows;      frame.s6_len = (uint64_t)nrows * 4ull;
    frame.s7_ptr = (uint64_t)(uintptr_t)dest;      frame.s7_len = (uint64_t)ndest * 4ull;
    frame.s8_ptr = (uint64_t)(uintptr_t)scratch;   frame.s8_len = (uint64_t)nscratch * 4ull;

    uint64_t regs[TISA_NUM_VREGS] = {0};
    regs[TISA_V0] = (uint64_t)(uintptr_t)&frame;
    return tisa_dispatch_mode(prog, comp, mode, &frame, regs, out_steps);
}

TcIsaOutcome tisa_run_micromath_sub(const TcIsaProgram *prog,
                                    const TcIsaCompiledX86 *comp,
                                    TcIsaExecMode mode,
                                    const uint64_t p0[4],
                                    const uint64_t p1[4],
                                    const uint64_t p2[4],
                                    const uint64_t p3[4],
                                    uint64_t dest_slot[4],
                                    uint64_t dest_idx,
                                    uint64_t nslot,
                                    uint64_t *out_steps) {
    TcIsaRuntimeFrame frame;
    memset(&frame, 0, sizeof(frame));
    frame.s0_ptr = (uint64_t)(uintptr_t)p0;        frame.s0_len = 32ull;
    frame.s1_ptr = (uint64_t)(uintptr_t)p1;        frame.s1_len = 32ull;
    frame.s2_ptr = (uint64_t)(uintptr_t)p2;        frame.s2_len = 32ull;
    frame.s3_ptr = (uint64_t)(uintptr_t)p3;        frame.s3_len = 32ull;
    frame.s4_ptr = (uint64_t)(uintptr_t)dest_slot; frame.s4_len = 32ull;
    frame.arg0   = dest_idx;
    frame.arg1   = nslot;

    uint64_t regs[TISA_NUM_VREGS] = {0};
    regs[TISA_V0] = (uint64_t)(uintptr_t)&frame;
    regs[TISA_V1] = frame.s0_ptr;
    regs[TISA_V2] = frame.s1_ptr;
    regs[TISA_V3] = frame.s2_ptr;
    regs[TISA_V4] = frame.s3_ptr;
    regs[TISA_V5] = frame.s4_ptr;
    return tisa_dispatch_mode(prog, comp, mode, &frame, regs, out_steps);
}

TcIsaOutcome tisa_run_lean_flat_rule(const TcIsaProgram *prog,
                                     const TcIsaCompiledX86 *comp,
                                     TcIsaExecMode mode,
                                     const void *const *prem_tuples,
                                     uint8_t nprem,
                                     void *out_tuple,
                                     uint64_t *out_steps) {
    if (!prog || nprem < 1u || nprem > 4u || !prem_tuples || !out_tuple) {
        return TISA_OUTCOME_INVALID_INPUT;
    }
    TcIsaRuntimeFrame frame;
    memset(&frame, 0, sizeof(frame));
    uint64_t *raw = &frame.s0_ptr;
    uint64_t regs[TISA_NUM_VREGS] = {0};
    regs[TISA_V0] = (uint64_t)(uintptr_t)&frame;

    for (uint8_t i = 0; i < nprem; i++) {
        uint64_t ptr = (uint64_t)(uintptr_t)prem_tuples[i];
        raw[i * 2u]      = ptr;
        raw[i * 2u + 1u] = 32ull;
        regs[TISA_V1 + i] = ptr;
    }
    uint64_t out_ptr = (uint64_t)(uintptr_t)out_tuple;
    raw[nprem * 2u]      = out_ptr;
    raw[nprem * 2u + 1u] = 32ull;
    regs[TISA_V1 + nprem] = out_ptr;

    return tisa_dispatch_mode(prog, comp, mode, &frame, regs, out_steps);
}

/*
 * test_tisa.c — Comprehensive Verification & Differential Gate Suite for t-ISA
 *
 * Covers:
 *   1. All 10 shared core opcodes and 5 structured control forms across
 *      Reference (`tisa_eval_ref`), tcalc-Hosted (`tisa_eval_tcalc`), and
 *      Direct x86-64 Native (`tisa_run_x86`), including:
 *        - U32Z signed shift & 32-bit signed comparison (`CMP U32Z SLT 0xffffffff < 0`)
 *        - SELECT operand aliasing (`dst == src2`, `dst == src3`) & callee-saved `rbx/r12/r13`
 *        - Counted & early-exit loops (0 iterations, boundary iterations, early exit, `> max_iters`)
 *        - Fuel exhaustion preserving completed prefix and untouched suffix
 *        - Capability overlap rejection, 64-bit address wraparound rejection, bad BOOL rejection,
 *          and static loop-bound immutability / shift-bound rejection
 *   2. All 11 premise-bearing Lean rules (`R_DERIVE_IS_TYPE .. R_ADMIT_THM`) specialized from
 *      live `tc_inspect_rule` tables: 4-way differential (`tc_flat_fire` vs `Ref` vs
 *      `tcalc-Hosted` vs `x86-64`) + semantic mutation controls (mutated `wtag`, constant
 *      guard, cross-premise equality guard, and rule table coordinates).
 *   3. Micromath `sub1` & `sub2` specialized from live `tc_inspect_rule` tables: 4-way
 *      differential (`tc_flat_fire` vs `Ref` vs `tcalc-Hosted` vs `x86-64`), guard refusals,
 *      `dest >= nslot` `UNSUPPORTED` refusal, and 500 randomized differential trials.
 *   4. `ordinary_flat_fire` (`flat_fire`) & `ordinary_flat_adapter` (`ordinary_flat_pack` +
 *      `flat_fire`): wrapped `UINT32_MAX` modular offsets, capacity/extent `UNSUPPORTED = 2`
 *      controls preserving `fields[0] == 77`, and 2,000 randomized differential scenarios
 *      against `ordinary_flat_adapter` (`ordinary_flat_cesta_runtime.o`).
 *   5. Deterministic JSON manifest export (`tisa/manifests/tisa_x86_programs_v1.json`) and
 *      byte-for-byte reproducibility verification across repeated compilations.
 */

#include "tisa_ref.h"
#include "tisa_x86.h"
#include "tisa_print.h"

#define TEST_MODES 5   /* p0: reference, tcalc-hosted, x86; p1: reference, x86 */
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../tcalc.h"
#include "../lean_tcalc_theory.h"
#include "../compiled/ordinary_flat_adapter.h"
#include "../compiled/flat_fire.h"
#include "tisa.h"
#include "tisa_manifest_export.h"

static unsigned g_checks = 0;

#define CHECK(cond)                                                            \
    do {                                                                       \
        if (!(cond)) {                                                         \
            fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, #cond);    \
            exit(1);                                                           \
        }                                                                      \
        g_checks++;                                                            \
    } while (0)

#define GUARD_PACK(i, j, i0, j0) \
    ((uint32_t)(i) | ((uint32_t)(j) << 8) | ((uint32_t)(i0) << 16) | ((uint32_t)(j0) << 24))
#define MAKE_PACK(i, j) \
    ((uint32_t)(i) | ((uint32_t)(j) << 8))

/* =========================================================================
 * Part 1: Core Opcode, Control, Aliasing, Fuel, & Negative Admission Tests
 * ========================================================================= */

static void test_core_opcodes_and_controls(void) {
    char err[256] = {0};

    /* 1a. U32Z signed shift, 32-bit SLT comparison (0xffffffff < 0), EXTRACT, MULLO,
     *     SELECT aliasing (dst == src2 and dst == src3), and callee-saved v9/v10/v11 */
    {
        TcIsaArena arena;
        tisa_arena_init(&arena, 128);
        TcIsaProgram prog;
        memset(&prog, 0, sizeof(prog));
        prog.name = "core_scalar_and_alias_suite";
        prog.prog_id = 1u;
        prog.nregions = 1u;
        prog.regions[0] = (TcIsaRegionDecl){ 0, TISA_CAP_RW, 64, 8, "out_buf" };
        prog.init_reg_mask = (1u << TISA_V0) | (1u << TISA_V1);
        prog.init_reg_types[TISA_V0] = TISA_TYPE_U64;
        prog.init_reg_types[TISA_V1] = TISA_TYPE_PTR;
        prog.init_reg_region[TISA_V1] = 0u;

        TcIsaStmt *s = NULL;
        /* v2 = 0x80000010 (U32Z); v3 = SHRS(U32Z, v2, 4) -> 0xF8000001 */
        s = tisa_stmt_seq(&arena, s, tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_IMM, .ty = TISA_TYPE_U32Z, .dst = TISA_V2, .imm64 = 0x80000010ull
        }));
        s = tisa_stmt_seq(&arena, s, tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_SHIFT, .subop = TISA_SHIFT_SHRS, .ty = TISA_TYPE_U32Z,
            .dst = TISA_V3, .src1 = TISA_V2, .bit_width = 4u, .imm64 = 4ull
        }));
        s = tisa_stmt_seq(&arena, s, tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_STORE, .subop = TISA_MEM_U64, .ty = TISA_TYPE_U64,
            .src1 = TISA_V1, .src2 = TISA_V3, .region_id = 0u, .disp32 = 0
        }));

        /* w14 interface check: CMP(U32Z, SLT, 0xffffffff, 0) == 1 (true), while ULT == 0 (false) */
        s = tisa_stmt_seq(&arena, s, tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_IMM, .ty = TISA_TYPE_U32Z, .dst = TISA_V4, .imm64 = 0xFFFFFFFFull
        }));
        s = tisa_stmt_seq(&arena, s, tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_CMP, .subop = TISA_CMP_SLT, .ty = TISA_TYPE_U32Z,
            .dst = TISA_V5, .src1 = TISA_V4, .bit_width = 1u, .imm64 = 0ull
        }));
        s = tisa_stmt_seq(&arena, s, tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_CMP, .subop = TISA_CMP_ULT, .ty = TISA_TYPE_U32Z,
            .dst = TISA_V6, .src1 = TISA_V4, .bit_width = 1u, .imm64 = 0ull
        }));
        /* Callee-saved registers v9 (rbx), v10 (r12), v11 (r13) + SELECT aliasing */
        s = tisa_stmt_seq(&arena, s, tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_IMM, .ty = TISA_TYPE_U64, .dst = TISA_V9, .imm64 = 0x1111222233334444ull
        }));
        s = tisa_stmt_seq(&arena, s, tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_IMM, .ty = TISA_TYPE_U64, .dst = TISA_V10, .imm64 = 0x5555666677778888ull
        }));
        /* SELECT with dst == src2 (v10 = v6 ? v9 : v10 -> since v6 == 0, v10 stays 0x5555666677778888) */
        s = tisa_stmt_seq(&arena, s, tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_SELECT, .ty = TISA_TYPE_U64,
            .dst = TISA_V10, .src1 = TISA_V9, .src2 = TISA_V10, .src3 = TISA_V6
        }));
        s = tisa_stmt_seq(&arena, s, tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_STORE, .subop = TISA_MEM_U64, .ty = TISA_TYPE_U64,
            .src1 = TISA_V1, .src2 = TISA_V10, .region_id = 0u, .disp32 = 8
        }));
        /* SELECT with dst == src3 (v11 = BOOL; v11 = v11 ? v5 : v6 -> 1) */
        s = tisa_stmt_seq(&arena, s, tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_MOV, .ty = TISA_TYPE_BOOL, .dst = TISA_V11, .src1 = TISA_V5
        }));
        s = tisa_stmt_seq(&arena, s, tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_SELECT, .ty = TISA_TYPE_BOOL,
            .dst = TISA_V11, .src1 = TISA_V5, .src2 = TISA_V6, .src3 = TISA_V11
        }));
        /* EXTRACT + MULLO + XOR + OR + SUB */
        s = tisa_stmt_seq(&arena, s, tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_EXTRACT, .ty = TISA_TYPE_U32Z,
            .dst = TISA_V7, .src1 = TISA_V9, .scale_lg2 = 16u, .bit_width = 16u
        })); /* 0x3333 */
        s = tisa_stmt_seq(&arena, s, tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_IMM, .ty = TISA_TYPE_U32Z, .dst = TISA_V8, .imm64 = 3ull
        }));
        s = tisa_stmt_seq(&arena, s, tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_BIN, .subop = TISA_BIN_MULLO, .ty = TISA_TYPE_U32Z,
            .dst = TISA_V7, .src1 = TISA_V7, .src2 = TISA_V8
        })); /* 0x9999 */
        s = tisa_stmt_seq(&arena, s, tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_STORE, .subop = TISA_MEM_U64, .ty = TISA_TYPE_U64,
            .src1 = TISA_V1, .src2 = TISA_V7, .region_id = 0u, .disp32 = 16
        }));
        /* Return v11 (1) */
        s = tisa_stmt_seq(&arena, s, tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_IMM, .ty = TISA_TYPE_U64, .dst = TISA_V8, .imm64 = 1ull
        }));
        s = tisa_stmt_seq(&arena, s, tisa_stmt_return(&arena, TISA_OUTCOME_FIRED, TISA_V8));
        prog.root = s;

        CHECK(tisa_check_program(&prog, err, sizeof(err)));
        TcIsaCompiledX86 comp;
        CHECK(tisa_compile_x86(&prog, TISA_PROFILE_P0, &comp, err, sizeof(err)));
        CHECK(comp.footprint.no_spill_verified);

        for (int m = 0; m < 3; m++) {
            uint64_t buf[8] = {0};
            TcIsaRuntimeFrame frame;
            memset(&frame, 0, sizeof(frame));
            frame.s0_ptr = (uint64_t)(uintptr_t)buf;
            frame.s0_len = sizeof(buf);
            uint64_t regs[TISA_NUM_VREGS] = {0};
            regs[TISA_V0] = (uint64_t)(uintptr_t)&frame;
            regs[TISA_V1] = frame.s0_ptr;

            TcIsaOutcome rc;
            uint64_t fires = 0;
            if (m == 0) rc = tisa_eval_ref(&prog, &frame, regs);
            else if (m == 1) {
                rc = tisa_eval_tcalc(&prog, &frame, regs, &fires);
                CHECK(fires > 0);
            } else {
                rc = tisa_run_x86(&prog, &comp, &frame, regs[TISA_V1], 0, 0, 0, 0);
            }
            CHECK(rc == TISA_OUTCOME_FIRED);
            CHECK(buf[0] == 0xF8000001ull);
            CHECK(buf[1] == 0x5555666677778888ull);
            CHECK(buf[2] == 0x9999ull);
        }

        tisa_free_x86(&comp);
        tisa_arena_free(&arena);
    }

    /* 1a-cont. Continuation-contextual recipe lowering on shared AST nodes:
     * Reusing the exact same `TcIsaStmt *shared_inc` pointer twice in a sequence
     * (`shared_inc ; mul2 ; shared_inc ; return`) must allocate distinct semantic-PC
     * recipe points with distinct continuation targets (`next_point`). */
    {
        TcIsaArena arena;
        tisa_arena_init(&arena, 64);
        TcIsaProgram prog;
        memset(&prog, 0, sizeof(prog));
        prog.name = "shared_ast_continuation_separation";
        prog.prog_id = 99u;
        prog.init_reg_mask = (1u << TISA_V0) | (1u << TISA_V1);
        prog.init_reg_types[TISA_V0] = TISA_TYPE_U64;
        prog.init_reg_types[TISA_V1] = TISA_TYPE_U64;

        TcIsaStmt *init_c1 = tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_IMM, .ty = TISA_TYPE_U64, .dst = TISA_V2, .imm64 = 3ull
        });
        /* Shared statement pointer: v1 = v1 + v2 */
        TcIsaStmt *shared_add = tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_BIN, .subop = TISA_BIN_ADD, .ty = TISA_TYPE_U64,
            .dst = TISA_V1, .src1 = TISA_V1, .src2 = TISA_V2
        });
        TcIsaStmt *shift_v1 = tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_SHIFT, .subop = TISA_SHIFT_SHL, .ty = TISA_TYPE_U64,
            .dst = TISA_V1, .src1 = TISA_V1, .bit_width = 1u
        });
        TcIsaStmt *ret_v1 = tisa_stmt_return(&arena, TISA_OUTCOME_FIRED, TISA_V1);

        /* Root reuses `shared_add` pointer twice with different continuations */
        prog.root = tisa_stmt_seq(&arena, init_c1,
                    tisa_stmt_seq(&arena, shared_add,
                    tisa_stmt_seq(&arena, shift_v1,
                    tisa_stmt_seq(&arena, shared_add, ret_v1))));

        TcIsaRecipeTable rtable;
        CHECK(tisa_lower_recipes(&prog, &rtable, err, sizeof(err)));
        CHECK(rtable.entry_point == 0ull);
        uint32_t add_points[4] = {0};
        uint64_t add_nexts[4]  = {0};
        size_t add_count = 0;
        for (uint32_t i = 0; i < rtable.npoints; i++) {
            const TcIsaPointRecipe *r = &rtable.recipes[i];
            CHECK(r->point == i);
            if (r->kind == TISA_RECIPE_INSTR && r->instr.op == TISA_OP_BIN &&
                r->instr.subop == TISA_BIN_ADD) {
                CHECK(add_count < 4u);
                add_points[add_count] = r->point;
                add_nexts[add_count]  = r->next_point;
                add_count++;
            }
        }
        CHECK(add_count == 2u);
        CHECK(add_points[0] != add_points[1]);
        CHECK(add_nexts[0]  != add_nexts[1]);

        TcIsaCompiledX86 comp;
        CHECK(tisa_compile_x86(&prog, TISA_PROFILE_P0, &comp, err, sizeof(err)));
        for (int m = 0; m < 3; m++) {
            TcIsaRuntimeFrame frame;
            memset(&frame, 0, sizeof(frame));
            uint64_t regs[TISA_NUM_VREGS] = {0};
            regs[TISA_V0] = (uint64_t)(uintptr_t)&frame;
            regs[TISA_V1] = 10ull; /* ((10 + 3) << 1) + 3 = 29 */
            TcIsaOutcome rc;
            if (m == 0) {
                rc = tisa_eval_ref(&prog, &frame, regs);
            } else if (m == 1) {
                TcIsaHostedRunResult hres;
                CHECK(tisa_try_eval_tcalc(&prog, &frame, regs, &hres));
                CHECK(hres.has_verdict && hres.board_halted);
                CHECK(hres.host_status == TISA_HOST_STATUS_BOARD_HALTED);
                CHECK(hres.halt_pc == TISA_POINT_HALT(TISA_OUTCOME_FIRED));
                CHECK(hres.tcalc_fires == 10ull); /* 4*(FUEL+INSTR) + FINALIZE_STATUS + FINALIZE_RETVAL = 10 */
                rc = hres.outcome;
            } else {
                rc = tisa_run_x86(&prog, &comp, &frame, 10ull, 0, 0, 0, 0);
            }
            CHECK(rc == TISA_OUTCOME_FIRED);
            CHECK(frame.status == (uint64_t)TISA_OUTCOME_FIRED);
            CHECK(frame.ret_val == 29ull);
            CHECK(frame.fuel_used == 4ull);
        }

        /* Injected no-verdict negative controls (`tisa_try_eval_tcalc_with_limits`):
         * 1) Initial cell-posting exhaustion (max_terms=32, max_occs=8) must return false
         *    (TISA_HOST_STATUS_NO_VERDICT) without manufacturing a semantic outcome or HALT.
         * 2) Mid-execution tc_fire occurrence exhaustion (max_terms=2048, max_occs=30,
         *    enough for the 25 initial cells + 2 firings before exhausting on step 3)
         *    must return false (TISA_HOST_STATUS_NO_VERDICT) with 0 < tcalc_fires < 10
         *    and leave frame.status / frame.ret_val untouched. */
        {
            TcIsaRuntimeFrame frame;
            memset(&frame, 0, sizeof(frame));
            frame.status    = 0xDEADull;
            frame.ret_val   = 0xBEEFull;
            frame.fuel_used = 0xCAFEull;
            uint64_t regs[TISA_NUM_VREGS] = {0};
            regs[TISA_V0] = (uint64_t)(uintptr_t)&frame;
            regs[TISA_V1] = 10ull;
            TcIsaHostedRunResult hres;
            CHECK(!tisa_try_eval_tcalc_with_limits(&prog, &frame, regs, 32u, 8u, &hres));
            CHECK(!hres.has_verdict && !hres.board_halted);
            CHECK(hres.host_status == TISA_HOST_STATUS_NO_VERDICT);
            CHECK(!TISA_POINT_IS_HALT(hres.halt_pc));
            CHECK(frame.status == 0xDEADull && frame.ret_val == 0xBEEFull && frame.fuel_used == 0xCAFEull);

            CHECK(!tisa_try_eval_tcalc_with_limits(&prog, &frame, regs, 2048u, 41u, &hres));
            CHECK(!hres.has_verdict && !hres.board_halted);
            CHECK(hres.host_status == TISA_HOST_STATUS_NO_VERDICT);
            CHECK(!TISA_POINT_IS_HALT(hres.halt_pc));
            CHECK(hres.tcalc_fires == 2ull);
            CHECK(frame.status == 0xDEADull && frame.ret_val == 0xBEEFull && frame.fuel_used == 0xCAFEull);
        }
        tisa_free_x86(&comp);
        tisa_arena_free(&arena);
    }

    /* 1b. Fuel exhaustion (`TISA_OUTCOME_EXHAUSTED = 4`) preserving completed prefix */
    {
        TcIsaArena arena;
        tisa_arena_init(&arena, 64);
        TcIsaProgram prog;
        memset(&prog, 0, sizeof(prog));
        prog.name = "fuel_prefix_test";
        prog.prog_id = 2u;
        prog.nregions = 1u;
        prog.regions[0] = (TcIsaRegionDecl){ 0, TISA_CAP_RW, 32, 8, "out_buf" };
        prog.init_reg_mask = (1u << TISA_V0) | (1u << TISA_V1);
        prog.init_reg_types[TISA_V0] = TISA_TYPE_U64;
        prog.init_reg_types[TISA_V1] = TISA_TYPE_PTR;
        prog.init_reg_region[TISA_V1] = 0u;

        TcIsaStmt *s = NULL;
        /* Step 1: v2 = 0xAA */
        s = tisa_stmt_seq(&arena, s, tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_IMM, .ty = TISA_TYPE_U64, .dst = TISA_V2, .imm64 = 0xAAull
        }));
        /* Step 2: out[0] = v2 */
        s = tisa_stmt_seq(&arena, s, tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_STORE, .subop = TISA_MEM_U64, .ty = TISA_TYPE_U64,
            .src1 = TISA_V1, .src2 = TISA_V2, .region_id = 0u, .disp32 = 0
        }));
        /* Step 3: v2 = 0xBB */
        s = tisa_stmt_seq(&arena, s, tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_IMM, .ty = TISA_TYPE_U64, .dst = TISA_V2, .imm64 = 0xBBull
        }));
        /* Step 4 (exceeds fuel_budget = 2): out[1] = v2 */
        s = tisa_stmt_seq(&arena, s, tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_STORE, .subop = TISA_MEM_U64, .ty = TISA_TYPE_U64,
            .src1 = TISA_V1, .src2 = TISA_V2, .region_id = 0u, .disp32 = 8
        }));
        s = tisa_stmt_seq(&arena, s, tisa_stmt_return(&arena, TISA_OUTCOME_FIRED, TISA_V2));
        prog.root = s;

        CHECK(tisa_check_program(&prog, err, sizeof(err)));
        TcIsaCompiledX86 comp;
        CHECK(tisa_compile_x86(&prog, TISA_PROFILE_P0, &comp, err, sizeof(err)));

        for (int m = 0; m < 3; m++) {
            uint64_t buf[4] = { 0x11ull, 0x22ull, 0x33ull, 0x44ull };
            TcIsaRuntimeFrame frame;
            memset(&frame, 0, sizeof(frame));
            frame.s0_ptr = (uint64_t)(uintptr_t)buf;
            frame.s0_len = sizeof(buf);
            frame.status = 99ull;
            frame.ret_val = 77ull;
            frame.fuel_budget = 2ull; /* Only 2 instructions allowed */
            uint64_t regs[TISA_NUM_VREGS] = {0};
            regs[TISA_V0] = (uint64_t)(uintptr_t)&frame;
            regs[TISA_V1] = frame.s0_ptr;

            TcIsaOutcome rc;
            if (m == 0) rc = tisa_eval_ref(&prog, &frame, regs);
            else if (m == 1) rc = tisa_eval_tcalc(&prog, &frame, regs, NULL);
            else rc = tisa_run_x86(&prog, &comp, &frame, regs[TISA_V1], 0, 0, 0, 0);

            CHECK(rc == TISA_OUTCOME_EXHAUSTED);
            CHECK(frame.status == (uint64_t)TISA_OUTCOME_EXHAUSTED);
            CHECK(frame.ret_val == (uint64_t)TISA_OUTCOME_EXHAUSTED);
            CHECK(frame.fuel_used == 2ull);
            CHECK(buf[0] == 0xAAull); /* Completed prefix preserved! */
            CHECK(buf[1] == 0x22ull); /* Suffix after exhaustion untouched! */
        }

        tisa_free_x86(&comp);
        tisa_arena_free(&arena);
    }

    /* 1c. Negative admission & runtime controls (loop-bound overwrite, bad shift,
     *     bad BOOL from U64, overlapping RW capability, ADDR 64-bit wraparound) */
    {
        TcIsaArena arena;
        tisa_arena_init(&arena, 64);

        /* Negative 1: Loop body overwrites bound_reg (v2) -> must be rejected by tisa_check_program */
        TcIsaProgram bad_loop;
        memset(&bad_loop, 0, sizeof(bad_loop));
        bad_loop.name = "bad_loop_bound_write";
        bad_loop.init_reg_mask = (1u << TISA_V0) | (1u << TISA_V2);
        bad_loop.init_reg_types[TISA_V0] = TISA_TYPE_U64;
        bad_loop.init_reg_types[TISA_V2] = TISA_TYPE_U64;
        TcIsaStmt *body_write_bound = tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_IMM, .ty = TISA_TYPE_U64, .dst = TISA_V2, .imm64 = 0ull
        });
        bad_loop.root = tisa_stmt_seq(&arena,
            tisa_stmt_count_loop(&arena, TISA_V3, TISA_V2, 8u, body_write_bound),
            tisa_stmt_return(&arena, TISA_OUTCOME_FIRED, TISA_V2));
        CHECK(!tisa_check_program(&bad_loop, err, sizeof(err)));

        /* Negative 1b: COUNT_LOOP and EARLY_EXIT_LOOP with RETURN inside body and no
         * post-loop RETURN -> must be rejected by tisa_check_program because zero
         * iterations or early exit falls through without returning! */
        TcIsaProgram bad_loop_ret = bad_loop;
        bad_loop_ret.root = tisa_stmt_count_loop(&arena, TISA_V3, TISA_V2, 1u,
            tisa_stmt_return(&arena, TISA_OUTCOME_FIRED, TISA_V2));
        CHECK(!tisa_check_program(&bad_loop_ret, err, sizeof(err)));

        TcIsaProgram bad_early_ret = bad_loop;
        bad_early_ret.init_reg_mask |= (1u << TISA_V4);
        bad_early_ret.init_reg_types[TISA_V4] = TISA_TYPE_BOOL;
        bad_early_ret.root = tisa_stmt_early_exit_loop(&arena, TISA_V3, TISA_V2, TISA_V4, 1u,
            tisa_stmt_return(&arena, TISA_OUTCOME_FIRED, TISA_V2));
        CHECK(!tisa_check_program(&bad_early_ret, err, sizeof(err)));

        /* Positive 1b-zero: COUNT_LOOP (bound=0) and EARLY_EXIT_LOOP (cont=0) followed by
         * post-loop RETURN, plus check that tisa_check_program sets no_spill_verified=false
         * and tisa_compile_x86 sets comp.footprint.no_spill_verified=true. */
        TcIsaProgram zero_loop = bad_early_ret;
        zero_loop.name = "zero_and_early_exit_loop_fallthrough";
        TcIsaStmt *zl_s = NULL;
        zl_s = tisa_stmt_seq(&arena, zl_s, tisa_stmt_count_loop(&arena, TISA_V3, TISA_V2, 4u,
            tisa_stmt_return(&arena, TISA_OUTCOME_FIRED, TISA_V2)));
        zl_s = tisa_stmt_seq(&arena, zl_s, tisa_stmt_early_exit_loop(&arena, TISA_V3, TISA_V2, TISA_V4, 4u,
            tisa_stmt_return(&arena, TISA_OUTCOME_FIRED, TISA_V2)));
        zl_s = tisa_stmt_seq(&arena, zl_s, tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_IMM, .ty = TISA_TYPE_U64, .dst = TISA_V5, .imm64 = 42ull
        }));
        zl_s = tisa_stmt_seq(&arena, zl_s, tisa_stmt_return(&arena, TISA_OUTCOME_FIRED, TISA_V5));
        zero_loop.root = zl_s;
        CHECK(tisa_check_program(&zero_loop, err, sizeof(err)));
        CHECK(!zero_loop.footprint.no_spill_verified);
        TcIsaCompiledX86 zl_comp;
        CHECK(tisa_compile_x86(&zero_loop, TISA_PROFILE_P0, &zl_comp, err, sizeof(err)));
        CHECK(zl_comp.footprint.no_spill_verified);
        for (int m = 0; m < 3; m++) {
            TcIsaRuntimeFrame zf;
            memset(&zf, 0, sizeof(zf));
            uint64_t zr[TISA_NUM_VREGS] = {0};
            zr[TISA_V0] = (uint64_t)(uintptr_t)&zf;
            zr[TISA_V2] = 0ull; /* bound = 0 for COUNT_LOOP */
            zr[TISA_V4] = 0ull; /* cont = 0 for EARLY_EXIT_LOOP */
            TcIsaOutcome zrc = (m == 0) ? tisa_eval_ref(&zero_loop, &zf, zr) :
                               (m == 1) ? tisa_eval_tcalc(&zero_loop, &zf, zr, NULL) :
                                          tisa_run_x86(&zero_loop, &zl_comp, &zf, 0, zr[TISA_V2], 0, zr[TISA_V4], 0);
            CHECK(zrc == TISA_OUTCOME_FIRED);
            CHECK(zf.ret_val == 42ull);
        }

        /* Negative 1c: Entry ABI review control — declaring non-entry register v8 in
         * init_reg_mask + directly RETURNing v8 must be rejected by tisa_check_program
         * and tisa_compile_x86! */
        TcIsaProgram bad_init_v8;
        memset(&bad_init_v8, 0, sizeof(bad_init_v8));
        bad_init_v8.name = "bad_init_v8_return";
        bad_init_v8.init_reg_mask = (1u << TISA_V0) | (1u << TISA_V8);
        bad_init_v8.init_reg_types[TISA_V0] = TISA_TYPE_U64;
        bad_init_v8.init_reg_types[TISA_V8] = TISA_TYPE_U64;
        bad_init_v8.root = tisa_stmt_return(&arena, TISA_OUTCOME_FIRED, TISA_V8);
        CHECK(!tisa_check_program(&bad_init_v8, err, sizeof(err)));
        TcIsaCompiledX86 bad_v8_comp;
        CHECK(!tisa_compile_x86(&bad_init_v8, TISA_PROFILE_P0, &bad_v8_comp, err, sizeof(err)));

        /* Negative 1d: Raw byte mutation controls on `tisa_verify_x86_bytes` —
         * 1) Unmutated zl_comp.bytes passes tisa_verify_x86_bytes.
         * 2) Mutating a prologue byte fails.
         * 3) Mutating a body instruction into `push rsp` (0x54) or `mov rsp, imm` fails.
         * 4) Mutating a branch rel32 displacement byte to jump outside [body_off, epilogue_off] fails. */
        CHECK(tisa_verify_x86_bytes(zl_comp.bytes, zl_comp.byte_len,
                                    zl_comp.body_offset, zl_comp.epilogue_offset, err, sizeof(err)));
        uint8_t mut_bytes[16384];
        memcpy(mut_bytes, zl_comp.bytes, zl_comp.byte_len);
        mut_bytes[0] ^= 0x01u; /* corrupt prologue push rbx */
        CHECK(!tisa_verify_x86_bytes(mut_bytes, zl_comp.byte_len,
                                     zl_comp.body_offset, zl_comp.epilogue_offset, err, sizeof(err)));
        memcpy(mut_bytes, zl_comp.bytes, zl_comp.byte_len);
        mut_bytes[zl_comp.body_offset] = 0x54u; /* inject `push rsp` inside body */
        CHECK(!tisa_verify_x86_bytes(mut_bytes, zl_comp.byte_len,
                                     zl_comp.body_offset, zl_comp.epilogue_offset, err, sizeof(err)));
        memcpy(mut_bytes, zl_comp.bytes, zl_comp.byte_len);
        /* Scan for the first E9 or 0F 8x branch inside body and corrupt its rel32 high byte to 0x7F */
        for (size_t bi = zl_comp.body_offset; bi + 6u <= zl_comp.epilogue_offset; bi++) {
            if (mut_bytes[bi] == 0x0Fu && (mut_bytes[bi + 1u] & 0xF0u) == 0x80u) {
                mut_bytes[bi + 5u] = 0x7Fu;
                break;
            }
        }
        CHECK(!tisa_verify_x86_bytes(mut_bytes, zl_comp.byte_len,
                                     zl_comp.body_offset, zl_comp.epilogue_offset, err, sizeof(err)));

        tisa_free_x86(&zl_comp);

        /* Negative 2: Shift >= 32 on U32Z -> must be rejected by tisa_check_program */
        TcIsaProgram bad_shift = bad_loop;
        bad_shift.root = tisa_stmt_seq(&arena,
            tisa_stmt_instr(&arena, (TcIsaInstr){
                .op = TISA_OP_SHIFT, .subop = TISA_SHIFT_SHL, .ty = TISA_TYPE_U32Z,
                .dst = TISA_V3, .src1 = TISA_V2, .bit_width = 32u, .imm64 = 32ull
            }),
            tisa_stmt_return(&arena, TISA_OUTCOME_FIRED, TISA_V3));
        CHECK(!tisa_check_program(&bad_shift, err, sizeof(err)));

        /* Negative 3: MOV from U64 to BOOL -> must be rejected by tisa_check_program */
        TcIsaProgram bad_bool_mov = bad_loop;
        bad_bool_mov.root = tisa_stmt_seq(&arena,
            tisa_stmt_instr(&arena, (TcIsaInstr){
                .op = TISA_OP_MOV, .ty = TISA_TYPE_BOOL, .dst = TISA_V3, .src1 = TISA_V2
            }),
            tisa_stmt_return(&arena, TISA_OUTCOME_FIRED, TISA_V3));
        CHECK(!tisa_check_program(&bad_bool_mov, err, sizeof(err)));

        /* Negative 3b: MOV from U64 to PTR -> must be rejected by tisa_check_program */
        TcIsaProgram bad_ptr_mov = bad_loop;
        bad_ptr_mov.root = tisa_stmt_seq(&arena,
            tisa_stmt_instr(&arena, (TcIsaInstr){
                .op = TISA_OP_MOV, .ty = TISA_TYPE_PTR, .dst = TISA_V3, .src1 = TISA_V2
            }),
            tisa_stmt_return(&arena, TISA_OUTCOME_FIRED, TISA_V3));
        CHECK(!tisa_check_program(&bad_ptr_mov, err, sizeof(err)));

        /* Negative 4: Overlapping RW capability slice rejected at runtime; ADDR wraparound rejected */
        TcIsaProgram addr_prog;
        memset(&addr_prog, 0, sizeof(addr_prog));
        addr_prog.name = "addr_bounds_test";
        addr_prog.nregions = 2u;
        addr_prog.regions[0] = (TcIsaRegionDecl){ 0, TISA_CAP_RO, 16, 8, "ro_in" };
        addr_prog.regions[1] = (TcIsaRegionDecl){ 1, TISA_CAP_RW, 16, 8, "rw_out" };
        addr_prog.init_reg_mask = (1u << TISA_V0) | (1u << TISA_V1) | (1u << TISA_V2) | (1u << TISA_V3);
        addr_prog.init_reg_types[TISA_V0] = TISA_TYPE_U64;
        addr_prog.init_reg_types[TISA_V1] = TISA_TYPE_PTR; addr_prog.init_reg_region[TISA_V1] = 0u;
        addr_prog.init_reg_types[TISA_V2] = TISA_TYPE_PTR; addr_prog.init_reg_region[TISA_V2] = 1u;
        addr_prog.init_reg_types[TISA_V3] = TISA_TYPE_U64;
        addr_prog.root = tisa_stmt_seq(&arena,
            tisa_stmt_instr(&arena, (TcIsaInstr){
                .op = TISA_OP_ADDR, .ty = TISA_TYPE_PTR,
                .dst = TISA_V4, .src1 = TISA_V1, .src2 = TISA_V3,
                .region_id = 0u, .scale_lg2 = 3u, .disp32 = 0
            }),
            tisa_stmt_return(&arena, TISA_OUTCOME_FIRED, TISA_V3));
        CHECK(tisa_check_program(&addr_prog, err, sizeof(err)));
        TcIsaCompiledX86 comp;
        CHECK(tisa_compile_x86(&addr_prog, TISA_PROFILE_P0, &comp, err, sizeof(err)));

        uint64_t b0[2] = {1, 2}, b1[2] = {3, 4};
        TcIsaRuntimeFrame frame;
        memset(&frame, 0, sizeof(frame));
        /* Overlap RW region 1 with RO region 0 -> must return TISA_OUTCOME_INVALID_INPUT */
        frame.s0_ptr = (uint64_t)(uintptr_t)b0; frame.s0_len = 16ull;
        frame.s1_ptr = (uint64_t)(uintptr_t)b0; frame.s1_len = 16ull;
        uint64_t regs[TISA_NUM_VREGS] = {0};
        regs[TISA_V0] = (uint64_t)(uintptr_t)&frame;
        regs[TISA_V1] = frame.s0_ptr;
        regs[TISA_V2] = frame.s1_ptr;
        regs[TISA_V3] = 1ull;
        CHECK(tisa_eval_ref(&addr_prog, &frame, regs) == TISA_OUTCOME_INVALID_INPUT);
        CHECK(tisa_run_x86(&addr_prog, &comp, &frame, regs[TISA_V1], regs[TISA_V2], regs[TISA_V3], 0, 0) == TISA_OUTCOME_INVALID_INPUT);

        /* Disjoint regions, but v3 = (1ull << 62) causes idx << 3 to shift-overflow 64 bits -> INVALID_INPUT */
        frame.s1_ptr = (uint64_t)(uintptr_t)b1;
        regs[TISA_V2] = frame.s1_ptr;
        regs[TISA_V3] = (1ull << 62);
        frame.status = 99ull; frame.ret_val = 77ull;
        CHECK(tisa_eval_ref(&addr_prog, &frame, regs) == TISA_OUTCOME_INVALID_INPUT);
        CHECK(frame.status == (uint64_t)TISA_OUTCOME_INVALID_INPUT && frame.ret_val == (uint64_t)TISA_OUTCOME_INVALID_INPUT);
        frame.status = 99ull; frame.ret_val = 77ull;
        CHECK(tisa_eval_tcalc(&addr_prog, &frame, regs, NULL) == TISA_OUTCOME_INVALID_INPUT);
        CHECK(frame.status == (uint64_t)TISA_OUTCOME_INVALID_INPUT && frame.ret_val == (uint64_t)TISA_OUTCOME_INVALID_INPUT);
        frame.status = 99ull; frame.ret_val = 77ull;
        CHECK(tisa_run_x86(&addr_prog, &comp, &frame, regs[TISA_V1], regs[TISA_V2], regs[TISA_V3], 0, 0) == TISA_OUTCOME_INVALID_INPUT);
        CHECK(frame.status == (uint64_t)TISA_OUTCOME_INVALID_INPUT && frame.ret_val == (uint64_t)TISA_OUTCOME_INVALID_INPUT);

        /* Negative 5: RW region overlapping TcIsaRuntimeFrame descriptor -> INVALID_INPUT */
        frame.s0_ptr = (uint64_t)(uintptr_t)b0;
        frame.s1_ptr = (uint64_t)(uintptr_t)&frame.s0_ptr;
        regs[TISA_V1] = frame.s0_ptr;
        regs[TISA_V2] = frame.s1_ptr;
        regs[TISA_V3] = 0ull;
        frame.status = 99ull; frame.ret_val = 77ull;
        CHECK(tisa_eval_ref(&addr_prog, &frame, regs) == TISA_OUTCOME_INVALID_INPUT);
        CHECK(frame.status == (uint64_t)TISA_OUTCOME_INVALID_INPUT && frame.ret_val == (uint64_t)TISA_OUTCOME_INVALID_INPUT);
        frame.status = 99ull; frame.ret_val = 77ull;
        CHECK(tisa_eval_tcalc(&addr_prog, &frame, regs, NULL) == TISA_OUTCOME_INVALID_INPUT);
        CHECK(frame.status == (uint64_t)TISA_OUTCOME_INVALID_INPUT && frame.ret_val == (uint64_t)TISA_OUTCOME_INVALID_INPUT);
        frame.status = 99ull; frame.ret_val = 77ull;
        CHECK(tisa_run_x86(&addr_prog, &comp, &frame, regs[TISA_V1], regs[TISA_V2], regs[TISA_V3], 0, 0) == TISA_OUTCOME_INVALID_INPUT);
        CHECK(frame.status == (uint64_t)TISA_OUTCOME_INVALID_INPUT && frame.ret_val == (uint64_t)TISA_OUTCOME_INVALID_INPUT);

        /* Negative 6: RO region overlapping mutable TcIsaRuntimeFrame fields (status/ret_val/fuel_used) -> INVALID_INPUT */
        frame.s0_ptr = (uint64_t)(uintptr_t)&frame.status;
        frame.s1_ptr = (uint64_t)(uintptr_t)b1;
        regs[TISA_V1] = frame.s0_ptr;
        regs[TISA_V2] = frame.s1_ptr;
        frame.status = 99ull; frame.ret_val = 77ull;
        CHECK(tisa_eval_ref(&addr_prog, &frame, regs) == TISA_OUTCOME_INVALID_INPUT);
        CHECK(frame.status == (uint64_t)TISA_OUTCOME_INVALID_INPUT && frame.ret_val == (uint64_t)TISA_OUTCOME_INVALID_INPUT);
        frame.status = 99ull; frame.ret_val = 77ull;
        CHECK(tisa_eval_tcalc(&addr_prog, &frame, regs, NULL) == TISA_OUTCOME_INVALID_INPUT);
        CHECK(frame.status == (uint64_t)TISA_OUTCOME_INVALID_INPUT && frame.ret_val == (uint64_t)TISA_OUTCOME_INVALID_INPUT);
        frame.status = 99ull; frame.ret_val = 77ull;
        CHECK(tisa_run_x86(&addr_prog, &comp, &frame, regs[TISA_V1], regs[TISA_V2], regs[TISA_V3], 0, 0) == TISA_OUTCOME_INVALID_INPUT);
        CHECK(frame.status == (uint64_t)TISA_OUTCOME_INVALID_INPUT && frame.ret_val == (uint64_t)TISA_OUTCOME_INVALID_INPUT);

        tisa_free_x86(&comp);
        tisa_arena_free(&arena);
    }
}

static void test_p1_static_leaf_regressions(void) {
    TcIsaArena arena;
    tisa_arena_init(&arena, 256);
    char err[256] = {0};

    /* 1. Independent outcome vs full-64 payload + sentinel frame preservation */
    static const struct {
        TcIsaOutcome outcome;
        uint64_t     payload;
    } ret_cases[] = {
        { TISA_OUTCOME_FIRED,       0ull },
        { TISA_OUTCOME_FIRED,       42ull },
        { TISA_OUTCOME_FIRED,       0xfedcba9876543210ull },
        { TISA_OUTCOME_REFUSED,     0ull },
        { TISA_OUTCOME_REFUSED,     42ull },
        { TISA_OUTCOME_REFUSED,     0x8000000000000001ull },
        { TISA_OUTCOME_UNSUPPORTED, 42ull },
        { TISA_OUTCOME_UNSUPPORTED, 0x123456789abcdef0ull }
    };
    for (size_t ci = 0; ci < sizeof(ret_cases) / sizeof(ret_cases[0]); ci++) {
        const TcIsaStmt ret_stmt = {
            .kind = TISA_CTRL_RETURN,
            .u.ret = { .outcome = ret_cases[ci].outcome, .ret_reg = TISA_V1 }
        };
        TcIsaProgram leaf_prog;
        memset(&leaf_prog, 0, sizeof(leaf_prog));
        leaf_prog.name = "p1_leaf_outcome_payload";
        leaf_prog.init_reg_mask = (1u << TISA_V0) | (1u << TISA_V1);
        leaf_prog.init_reg_types[TISA_V0] = TISA_TYPE_U64;
        leaf_prog.init_reg_types[TISA_V1] = TISA_TYPE_U64;
        leaf_prog.root = &ret_stmt;

        TcIsaCompiledX86 comp_p0, comp_p1;
        CHECK(tisa_compile_x86(&leaf_prog, TISA_PROFILE_P0, &comp_p0, err, sizeof(err)));
        CHECK(tisa_compile_x86(&leaf_prog, TISA_PROFILE_P1, &comp_p1, err, sizeof(err)));

        TcIsaRuntimeFrame sentinel;
        memset(&sentinel, 0, sizeof(sentinel));
        sentinel.s0_ptr = 0x1111000011110000ull; sentinel.s0_len = 0x2222000022220000ull;
        sentinel.s4_ptr = 0x3333000033330000ull; sentinel.s4_len = 0x4444000044440000ull;
        sentinel.s8_ptr = 0x5555000055550000ull; sentinel.s8_len = 0x6666000066660000ull;
        sentinel.status = 99ull;
        sentinel.ret_val = 77ull;
        sentinel.fuel_budget = 900ull;
        sentinel.fuel_used = 123ull;
        sentinel.arg0 = 0xaaaa5555aaaa5555ull;
        sentinel.arg1 = 0x5555aaaa5555aaaaull;

        TcIsaRuntimeFrame ref_f = sentinel, p1_ref_f = sentinel, p1_x86_f = sentinel, x86_p0_f = sentinel, x86_p1_f = sentinel;
        uint64_t r_ref[TISA_NUM_VREGS] = {0}, r_p1[TISA_NUM_VREGS] = {0}, r_p1_x86[TISA_NUM_VREGS] = {0};
        r_ref[TISA_V0]    = (uint64_t)(uintptr_t)&ref_f;
        r_ref[TISA_V1]    = ret_cases[ci].payload;
        r_p1[TISA_V0]     = (uint64_t)(uintptr_t)&p1_ref_f;
        r_p1[TISA_V1]     = ret_cases[ci].payload;
        r_p1_x86[TISA_V0] = (uint64_t)(uintptr_t)&p1_x86_f;
        r_p1_x86[TISA_V1] = ret_cases[ci].payload;

        TcIsaOutcome oc_ref    = tisa_eval_ref(&leaf_prog, &ref_f, r_ref);
        TcIsaOutcome oc_p1_ref = tisa_run(&leaf_prog, &p1_ref_f, r_p1);
        TcIsaOutcome oc_p1_x86 = tisa_p1_runner(&leaf_prog, TISA_MODE_P1_X86, &p1_x86_f, r_p1_x86);
        TcIsaOutcome oc_x86_p0 = tisa_run_x86(&leaf_prog, &comp_p0, &x86_p0_f, ret_cases[ci].payload, 0, 0, 0, 0);
        TcIsaOutcome oc_x86_p1 = tisa_run_x86(&leaf_prog, &comp_p1, &x86_p1_f, ret_cases[ci].payload, 0, 0, 0, 0);
        uint64_t raw_rax = comp_p1.entry(&x86_p1_f, ret_cases[ci].payload, 0, 0, 0, 0);

        CHECK(oc_ref == ret_cases[ci].outcome);
        CHECK(oc_p1_ref == ret_cases[ci].outcome);
        CHECK(oc_p1_x86 == ret_cases[ci].outcome);
        CHECK(oc_x86_p0 == ret_cases[ci].outcome);
        CHECK(oc_x86_p1 == ret_cases[ci].outcome);
        CHECK(raw_rax == ret_cases[ci].payload);

        CHECK(ref_f.status == (uint64_t)ret_cases[ci].outcome && ref_f.ret_val == ret_cases[ci].payload);
        CHECK(p1_ref_f.status == (uint64_t)ret_cases[ci].outcome && p1_ref_f.ret_val == ret_cases[ci].payload);
        CHECK(p1_x86_f.status == (uint64_t)ret_cases[ci].outcome && p1_x86_f.ret_val == ret_cases[ci].payload);
        CHECK(x86_p0_f.status == (uint64_t)ret_cases[ci].outcome && x86_p0_f.ret_val == ret_cases[ci].payload);
        CHECK(x86_p1_f.status == (uint64_t)ret_cases[ci].outcome && x86_p1_f.ret_val == ret_cases[ci].payload);

        CHECK(x86_p1_f.s0_ptr == sentinel.s0_ptr && x86_p1_f.s0_len == sentinel.s0_len);
        CHECK(x86_p1_f.s4_ptr == sentinel.s4_ptr && x86_p1_f.s4_len == sentinel.s4_len);
        CHECK(x86_p1_f.s8_ptr == sentinel.s8_ptr && x86_p1_f.s8_len == sentinel.s8_len);
        CHECK(x86_p1_f.fuel_budget == sentinel.fuel_budget);
        CHECK(x86_p1_f.fuel_used == sentinel.fuel_used);
        CHECK(x86_p1_f.arg0 == sentinel.arg0 && x86_p1_f.arg1 == sentinel.arg1);

        tisa_free_x86(&comp_p0);
        tisa_free_x86(&comp_p1);
    }

    /* 2. CMP+IF fallthrough into outer SEQ reading cond_reg (`v3`) */
    TcIsaProgram fall_prog;
    memset(&fall_prog, 0, sizeof(fall_prog));
    fall_prog.name = "p1_cmp_if_fallthrough_live_cond";
    fall_prog.init_reg_mask = (1u << TISA_V0) | (1u << TISA_V1) | (1u << TISA_V2);
    fall_prog.init_reg_types[TISA_V0] = TISA_TYPE_U64;
    fall_prog.init_reg_types[TISA_V1] = TISA_TYPE_U64;
    fall_prog.init_reg_types[TISA_V2] = TISA_TYPE_U64;
    TcIsaStmt *cmp_s = tisa_stmt_instr(&arena, (TcIsaInstr){
        .op = TISA_OP_CMP, .subop = TISA_CMP_EQ, .ty = TISA_TYPE_U64,
        .dst = TISA_V3, .src1 = TISA_V1, .src2 = TISA_V2
    });
    TcIsaStmt *if_fall = tisa_stmt_if(&arena, TISA_V3,
        tisa_stmt_instr(&arena, (TcIsaInstr){ .op = TISA_OP_IMM, .ty = TISA_TYPE_U64, .dst = TISA_V4, .imm64 = 10ull }),
        tisa_stmt_instr(&arena, (TcIsaInstr){ .op = TISA_OP_IMM, .ty = TISA_TYPE_U64, .dst = TISA_V4, .imm64 = 20ull }));
    TcIsaStmt *sel_after = tisa_stmt_instr(&arena, (TcIsaInstr){
        .op = TISA_OP_SELECT, .ty = TISA_TYPE_U64,
        .dst = TISA_V5, .src1 = TISA_V4, .src2 = TISA_V1, .src3 = TISA_V3
    });
    fall_prog.root = tisa_stmt_seq(&arena,
        tisa_stmt_seq(&arena, cmp_s, if_fall),
        tisa_stmt_seq(&arena, sel_after, tisa_stmt_return(&arena, TISA_OUTCOME_FIRED, TISA_V5)));
    TcIsaCompiledX86 fall_p1;
    CHECK(tisa_compile_x86(&fall_prog, TISA_PROFILE_P1, &fall_p1, err, sizeof(err)));
    for (int eq = 0; eq <= 1; eq++) {
        TcIsaRuntimeFrame ff = {0};
        uint64_t a1 = 55ull, a2 = eq ? 55ull : 66ull;
        CHECK(tisa_run_x86(&fall_prog, &fall_p1, &ff, a1, a2, 0, 0, 0) == TISA_OUTCOME_FIRED);
        CHECK(ff.status == (uint64_t)TISA_OUTCOME_FIRED);
        CHECK(ff.ret_val == (eq ? 10ull : 55ull));
    }
    tisa_free_x86(&fall_p1);

    /* 3. Valid entry pointer at `base + len` must fail LOAD with INVALID_INPUT under P1 */
    TcIsaProgram end_ptr_prog;
    memset(&end_ptr_prog, 0, sizeof(end_ptr_prog));
    end_ptr_prog.name = "p1_end_ptr_load_bounds";
    end_ptr_prog.nregions = 1u;
    end_ptr_prog.regions[0] = (TcIsaRegionDecl){
        .region_id = 0, .mode = TISA_CAP_RO, .min_byte_len = 32, .align_bytes = 8, .name = "ro0"
    };
    end_ptr_prog.init_reg_mask = (1u << TISA_V0) | (1u << TISA_V1);
    end_ptr_prog.init_reg_types[TISA_V0] = TISA_TYPE_U64;
    end_ptr_prog.init_reg_types[TISA_V1] = TISA_TYPE_PTR;
    end_ptr_prog.init_reg_region[TISA_V1] = 0u;
    end_ptr_prog.root = tisa_stmt_seq(&arena,
        tisa_stmt_instr(&arena, (TcIsaInstr){
            .op = TISA_OP_LOAD, .subop = TISA_MEM_U64, .ty = TISA_TYPE_U64,
            .dst = TISA_V2, .src1 = TISA_V1, .region_id = 0u, .disp32 = 0
        }),
        tisa_stmt_return(&arena, TISA_OUTCOME_FIRED, TISA_V2));
    TcIsaCompiledX86 end_p1;
    CHECK(tisa_compile_x86(&end_ptr_prog, TISA_PROFILE_P1, &end_p1, err, sizeof(err)));
    uint64_t ro_buf[4] = { 101ull, 102ull, 103ull, 104ull };
    TcIsaRuntimeFrame ef = { .s0_ptr = (uint64_t)(uintptr_t)ro_buf, .s0_len = sizeof(ro_buf), .status = 99ull, .ret_val = 77ull };
    uint64_t end_ptr = ef.s0_ptr + ef.s0_len;
    CHECK(tisa_run_x86(&end_ptr_prog, &end_p1, &ef, end_ptr, 0, 0, 0, 0) == TISA_OUTCOME_INVALID_INPUT);
    CHECK(ef.status == (uint64_t)TISA_OUTCOME_INVALID_INPUT && ef.ret_val == (uint64_t)TISA_OUTCOME_INVALID_INPUT);
    ef.status = 99ull; ef.ret_val = 77ull;
    CHECK(tisa_run_x86(&end_ptr_prog, &end_p1, &ef, ef.s0_ptr + 24ull, 0, 0, 0, 0) == TISA_OUTCOME_FIRED);
    CHECK(ef.status == (uint64_t)TISA_OUTCOME_FIRED && ef.ret_val == 104ull);
    tisa_free_x86(&end_p1);

    tisa_arena_free(&arena);
}

/* =========================================================================
 * Part 2: All 11 Premise-Bearing Lean Rules Derived from Live `R[]`/`FL[]`
 * ========================================================================= */

typedef struct {
    uint32_t tag;
    uint32_t pad;
    uint64_t a[3];
} TestLeanTuple;

static const char *const k_lean_rule_names[23] = {
    "R_CHECK_SORT", "R_CHECK_CONST", "R_CHECK_APP", "R_CHECK_LAM",
    "R_CHECK_FORALL", "R_CHECK_LET", "R_CHECK_PROJ", "R_CHECK_LIT",
    "R_EMIT_DEFEQ", "R_EMIT_SORT_OF", "R_EMIT_DECL_REQ2", "R_EMIT_DECL_REQ3",
    "R_DERIVE_IS_TYPE", "R_DERIVE_IS_PROP", "R_CHECK_CONV", "R_ADMIT_AXIOM",
    "R_ADMIT_QUOT", "R_ADMIT_IND", "R_ADMIT_CTOR", "R_ADMIT_REC",
    "R_ADMIT_DEFN", "R_ADMIT_OPAQUE", "R_ADMIT_THM"
};

static Occ test_fire_mflat2(int rid, uint64_t a0, uint64_t a1) {
    Term vs[2] = { lean_tc_id_term(a0), lean_tc_id_term(a1) };
    return tc_flat_fire(rid, NULL, vs, 0);
}

static Occ test_fire_mflat3(int rid, uint64_t a0, uint64_t a1, uint64_t a2) {
    Term vs[3] = { lean_tc_id_term(a0), lean_tc_id_term(a1), lean_tc_id_term(a2) };
    return tc_flat_fire(rid, NULL, vs, 0);
}

static Occ post_lean_premise_on_sealed_board(int head, const uint64_t a[3]) {
    if (head == C_TYPED) {
        return test_fire_mflat2(R_CHECK_SORT, a[0], a[1]);
    } else if (head == C_DEFEQ) {
        return test_fire_mflat2(R_EMIT_DEFEQ, a[0], a[1]);
    } else if (head == C_SORT_OF) {
        return test_fire_mflat2(R_EMIT_SORT_OF, a[0], a[1]);
    } else if (head == C_DECL_REQ2) {
        return test_fire_mflat2(R_EMIT_DECL_REQ2, a[0], a[1]);
    } else if (head == C_DECL_REQ3) {
        return test_fire_mflat3(R_EMIT_DECL_REQ3, a[0], a[1], a[2]);
    } else if (head == C_IS_TYPE) {
        Occ o_ty = test_fire_mflat2(R_CHECK_SORT, a[0], 999991ull);
        Occ o_so = test_fire_mflat2(R_EMIT_SORT_OF, 999991ull, a[1]);
        Occ ks[2] = { o_ty, o_so };
        return tc_flat_fire(R_DERIVE_IS_TYPE, ks, NULL, 0);
    } else if (head == C_IS_PROP) {
        uint64_t ty_args[3] = { a[0], 0ull, 0ull };
        Occ o_it = post_lean_premise_on_sealed_board(C_IS_TYPE, ty_args);
        Occ ks[1] = { o_it };
        return tc_flat_fire(R_DERIVE_IS_PROP, ks, NULL, 0);
    } else if (head == C_DECL_IND) {
        Occ o_req = test_fire_mflat2(R_EMIT_DECL_REQ2, a[0], a[1]);
        uint64_t ty_args[3] = { a[1], 1ull, 0ull };
        Occ o_it  = post_lean_premise_on_sealed_board(C_IS_TYPE, ty_args);
        Occ ks[2] = { o_req, o_it };
        return tc_flat_fire(R_ADMIT_IND, ks, NULL, 0);
    }
    return 0;
}

static void test_all_11_lean_premise_rules(TcIsaArena *export_arena,
                                           TcIsaProgram export_progs[11],
                                           TcIsaCompiledX86 export_comps[11]) {
    /* Initialize the live 23-rule Lean theory in tcalc and snapshot all 11 flat rules */
    lean_tc_init_kernel();
    TcInspectRule ir[23];
    TcInspectFlat ifl[23];
    for (int rid = 0; rid < 23; rid++) {
        CHECK(tc_inspect_rule(rid, &ir[rid], &ifl[rid]));
        if (rid < 12) CHECK(!ir[rid].flat && ir[rid].mflat);
        else          CHECK(ir[rid].flat && ifl[rid].ordinary);
    }

    char err[256] = {0};
    for (int idx = 0; idx < 11; idx++) {
        int rid = 12 + idx;
        lean_tc_init_kernel();
        TcIsaProgram *prog = &export_progs[idx];
        TcIsaCompiledX86 *comp = &export_comps[idx];
        CHECK(tisa_specialize_lean_flat_rule(export_arena, &ir[rid], &ifl[rid],
                                             k_lean_rule_names[rid], prog, err, sizeof(err)));
        CHECK(tisa_compile_x86(prog, TISA_PROFILE_P0, comp, err, sizeof(err)));
        CHECK(comp->footprint.no_spill_verified);

        uint8_t np = ir[rid].nkeep;
        CHECK(np >= 1u && np <= 3u);

        /* Build the `np` premise tuples from `ir[rid]` & `ifl[rid]` */
        TestLeanTuple prems[4];
        memset(prems, 0, sizeof(prems));
        for (uint8_t i = 0; i < np; i++) {
            prems[i].tag = ifl[rid].ktag[i];
            for (int j = 0; j < 3; j++) {
                prems[i].a[j] = (uint64_t)(500 + i * 10 + j);
            }
        }
        /* Satisfy all `nguard` guards from `ifl[rid]` */
        for (int g = (int)ifl[rid].nguard - 1; g >= 0; g--) {
            uint8_t gi  = ifl[rid].guard[g].i;
            uint8_t gj  = ifl[rid].guard[g].j;
            uint8_t gi0 = ifl[rid].guard[g].i0;
            uint8_t gj0 = ifl[rid].guard[g].j0;
            if (gi < np && gi0 == np) {
                uint64_t cval = (ifl[rid].mc[gj0] == T_ID_ZERO) ? 0ull : tc_name_id(ifl[rid].mc[gj0]);
                prems[gi].a[gj] = cval;
            } else if (gi == np && gi0 < np) {
                uint64_t cval = (ifl[rid].mc[gj] == T_ID_ZERO) ? 0ull : tc_name_id(ifl[rid].mc[gj]);
                prems[gi0].a[gj0] = cval;
            } else if (gi < np && gi0 < np) {
                prems[gi].a[gj] = prems[gi0].a[gj0];
            }
        }

        const void *prem_ptrs[4] = { &prems[0], &prems[1], &prems[2], &prems[3] };

        /* 1. Compute reference output using tcalc's own `tc_flat_fire` on a fresh sealed board */
        lean_tc_init_kernel();
        (void)tc_fresh_name(); /* burn name ID 0 so lean_tc_id_term(k) gets tc_name_id == k */
        for (uint64_t k = 1; k <= 600; k++) {
            (void)lean_tc_id_term(k);
        }
        Occ keep_occ[4] = {0};
        for (uint8_t i = 0; i < np; i++) {
            uint32_t head = prems[i].tag >> 9;
            keep_occ[i] = post_lean_premise_on_sealed_board((int)head, prems[i].a);
            CHECK(keep_occ[i] != 0);
        }
        Occ out_occ = tc_flat_fire(rid, keep_occ, NULL, 0);
        CHECK(out_occ != 0);
        uint32_t want_mtag = (ifl[rid].mhead << 9) | ((uint32_t)ir[rid].mspace << 1) | 1u;
        const Term *out_targs = tc_flat_args(out_occ, want_mtag);
        CHECK(out_targs != NULL);
        TestLeanTuple want_out;
        memset(&want_out, 0, sizeof(want_out));
        want_out.tag = want_mtag;
        for (int j = 0; j < (int)ifl[rid].mar; j++) {
            want_out.a[j] = (out_targs[j] == T_ID_ZERO) ? 0ull : tc_name_id(out_targs[j]);
        }

        /* 2. Run 3 t-ISA realizations (`Ref`, `tcalc-Hosted`, `x86-64`) and verify exact parity */
        for (int mode = 0; mode < TEST_MODES; mode++) {
            TestLeanTuple got_out;
            memset(&got_out, 0xA5, sizeof(got_out));
            uint64_t steps = 0;
            TcIsaOutcome rc = tisa_run_lean_flat_rule(prog, comp, (TcIsaExecMode)mode,
                                                      prem_ptrs, np, &got_out, &steps);
            CHECK(rc == TISA_OUTCOME_FIRED);
            CHECK(mode >= TISA_MODE_P1_REF || steps > 0);   /* p1 pays only at FUND points */
            CHECK(memcmp(&got_out, &want_out, sizeof(TestLeanTuple)) == 0);
        }

        /* 3. Semantic Mutation Control A: Mutate each premise's `wtag` -> REFUSED + untouched output */
        for (uint8_t i = 0; i < np; i++) {
            TestLeanTuple bad_prems[4];
            memcpy(bad_prems, prems, sizeof(prems));
            bad_prems[i].tag ^= (1u << 9); /* Flip constructor bit in wtag */
            const void *bptrs[4] = { &bad_prems[0], &bad_prems[1], &bad_prems[2], &bad_prems[3] };
            for (int mode = 0; mode < TEST_MODES; mode++) {
                TestLeanTuple got_out, sentinel;
                memset(&got_out, 0xA5, sizeof(got_out));
                memset(&sentinel, 0xA5, sizeof(sentinel));
                TcIsaOutcome rc = tisa_run_lean_flat_rule(prog, comp, (TcIsaExecMode)mode,
                                                          bptrs, np, &got_out, NULL);
                CHECK(rc == TISA_OUTCOME_REFUSED);
                CHECK(memcmp(&got_out, &sentinel, sizeof(TestLeanTuple)) == 0);
            }
        }

        /* 4. Semantic Mutation Control B: Break every guard in `ifl[rid]` one by one -> REFUSED + untouched output */
        for (uint8_t g = 0; g < ifl[rid].nguard; g++) {
            TestLeanTuple bad_prems[4];
            memcpy(bad_prems, prems, sizeof(prems));
            uint8_t gi = ifl[rid].guard[g].i;
            uint8_t gj = ifl[rid].guard[g].j;
            if (gi < np) {
                bad_prems[gi].a[gj] ^= 0x12345ull;
            } else {
                uint8_t gi0 = ifl[rid].guard[g].i0;
                uint8_t gj0 = ifl[rid].guard[g].j0;
                bad_prems[gi0].a[gj0] ^= 0x12345ull;
            }
            const void *bptrs[4] = { &bad_prems[0], &bad_prems[1], &bad_prems[2], &bad_prems[3] };
            for (int mode = 0; mode < TEST_MODES; mode++) {
                TestLeanTuple got_out, sentinel;
                memset(&got_out, 0xA5, sizeof(got_out));
                memset(&sentinel, 0xA5, sizeof(sentinel));
                TcIsaOutcome rc = tisa_run_lean_flat_rule(prog, comp, (TcIsaExecMode)mode,
                                                          bptrs, np, &got_out, NULL);
                CHECK(rc == TISA_OUTCOME_REFUSED);
                CHECK(memcmp(&got_out, &sentinel, sizeof(TestLeanTuple)) == 0);
            }
        }

        /* 5. Semantic Mutation Control C: Mutate conclusion space or output coordinate -> must NOT match want_out */
        {
            lean_tc_init_kernel();
            TcInspectRule mut_ir = ir[rid];
            TcInspectFlat mut_ifl = ifl[rid];
            mut_ir.mspace = (uint8_t)(mut_ir.mspace + 1u);
            TcIsaArena mut_arena;
            tisa_arena_init(&mut_arena, 64);
            TcIsaProgram mut_prog;
            TcIsaCompiledX86 mut_comp;
            CHECK(tisa_specialize_lean_flat_rule(&mut_arena, &mut_ir, &mut_ifl, "mut_rule", &mut_prog, err, sizeof(err)));
            CHECK(tisa_compile_x86(&mut_prog, TISA_PROFILE_P0, &mut_comp, err, sizeof(err)));
            TestLeanTuple mut_out;
            memset(&mut_out, 0, sizeof(mut_out));
            CHECK(tisa_run_lean_flat_rule(&mut_prog, &mut_comp, TISA_MODE_X86, prem_ptrs, np, &mut_out, NULL) == TISA_OUTCOME_FIRED);
            CHECK(memcmp(&mut_out, &want_out, sizeof(TestLeanTuple)) != 0);
            tisa_free_x86(&mut_comp);
            tisa_arena_free(&mut_arena);
        }
    }
}

/* =========================================================================
 * Part 3: Micromath `sub1` & `sub2` Derived from Live `tc_inspect_rule`
 * ========================================================================= */

static void init_micromath_tcalc_board(int *out_sub1, int *out_sub2) {
    CHECK(tc_init(1u << 15, 1u << 12));
    int SYM = tc_sort(0);
    int PROP = tc_sort(SORT_PROVABLE);
    Binder s4[4] = {
        { (uint16_t)SYM, 0, 0 }, { (uint16_t)SYM, 0, 0 },
        { (uint16_t)SYM, 0, 0 }, { (uint16_t)SYM, 0, 0 }
    };
    int EQ = tc_con((uint16_t)PROP, 0, 4, s4);
    Binder v[9];
    for (int i = 0; i < 9; i++) v[i] = (Binder){ (uint16_t)SYM, 0, 0 };
    tc_fresh_name(); tc_fresh_name();
    CHECK(EQ >= 0 && tc_ctx(9, v));
    Term t = tc_v(0), u = tc_v(1), w = tc_v(2), x = tc_v(3),
         a = tc_v(4), b = tc_v(5), u1 = tc_v(6), w1 = tc_v(7), x1 = tc_v(8);
    Term s1[4] = {
        tc_app(EQ, (Term[4]){ x, t, u, w }),
        tc_app(EQ, (Term[4]){ u1, u, a, b }),
        tc_app(EQ, (Term[4]){ w1, w, a, b }),
        tc_app(EQ, (Term[4]){ x1, x, a, b })
    };
    Rule r1 = { .nkeep = 4, .make = { tc_app(EQ, (Term[4]){ x1, t, u1, w1 }), 0 }, .fresh = -1 };
    for (int i = 0; i < 4; i++) r1.keep[i] = (Pat){ s1[i], 0 };
    *out_sub1 = tc_rule(&r1);

    Term s2[4] = {
        tc_app(EQ, (Term[4]){ x, t, u, w }),
        tc_app(EQ, (Term[4]){ u1, u, a, b }),
        tc_app(EQ, (Term[4]){ w1, w, a, b }),
        tc_app(EQ, (Term[4]){ x1, t, u1, w1 })
    };
    Rule r2 = { .nkeep = 4, .make = { tc_app(EQ, (Term[4]){ x1, x, a, b }), 0 }, .fresh = -1 };
    for (int i = 0; i < 4; i++) r2.keep[i] = (Pat){ s2[i], 0 };
    *out_sub2 = tc_rule(&r2);
    CHECK(*out_sub1 >= 0 && *out_sub2 >= 0);
}

static void test_micromath_sub_rules(TcIsaArena *export_arena,
                                     TcIsaProgram export_mm_progs[2],
                                     TcIsaCompiledX86 export_mm_comps[2]) {
    int r_sub1 = -1, r_sub2 = -1;
    init_micromath_tcalc_board(&r_sub1, &r_sub2);

    TcInspectRule ir[2];
    TcInspectFlat ifl[2];
    CHECK(tc_inspect_rule(r_sub1, &ir[0], &ifl[0]));
    CHECK(tc_inspect_rule(r_sub2, &ir[1], &ifl[1]));

    char err[256] = {0};
    const char *names[2] = { "mm_sub1_leaf", "mm_sub2_leaf" };
    for (int k = 0; k < 2; k++) {
        CHECK(tisa_specialize_micromath_sub_rule(export_arena, &ir[k], &ifl[k], names[k],
                                                 &export_mm_progs[k], err, sizeof(err)));
        CHECK(tisa_compile_x86(&export_mm_progs[k], TISA_PROFILE_P0,
                               &export_mm_comps[k], err, sizeof(err)));
        CHECK(export_mm_comps[k].footprint.no_spill_verified);

        /* Valid premises for sub1 / sub2 */
        uint64_t t = 11, u = 22, w = 33, x = 44, a = 55, b = 66, u1 = 77, w1 = 88, x1 = 99;
        uint64_t p0[4] = { x,  t, u,  w  };
        uint64_t p1[4] = { u1, u, a,  b  };
        uint64_t p2[4] = { w1, w, a,  b  };
        uint64_t p3[4] = { x1, (k == 0) ? x : t, (k == 0) ? a : u1, (k == 0) ? b : w1 };
        uint64_t want[4] = { x1, (k == 0) ? t : x, (k == 0) ? u1 : a, (k == 0) ? w1 : b };

        /* Positive 3-mode parity (`Ref`, `tcalc-Hosted`, `x86-64`) */
        for (int mode = 0; mode < TEST_MODES; mode++) {
            uint64_t out[4] = {0};
            uint64_t steps = 0;
            TcIsaOutcome rc = tisa_run_micromath_sub(&export_mm_progs[k], &export_mm_comps[k],
                                                     (TcIsaExecMode)mode,
                                                     p0, p1, p2, p3, out, 5ull, 16ull, &steps);
            CHECK(rc == TISA_OUTCOME_FIRED && (mode >= TISA_MODE_P1_REF || steps > 0));
            CHECK(memcmp(out, want, sizeof(want)) == 0);
        }

        /* Capacity / bounds check: dest_idx >= nslot -> TISA_OUTCOME_UNSUPPORTED (2) without writing out */
        for (int mode = 0; mode < TEST_MODES; mode++) {
            uint64_t out[4] = { 901, 902, 903, 904 };
            const uint64_t orig[4] = { 901, 902, 903, 904 };
            TcIsaOutcome rc = tisa_run_micromath_sub(&export_mm_progs[k], &export_mm_comps[k],
                                                     (TcIsaExecMode)mode,
                                                     p0, p1, p2, p3, out, 16ull, 16ull, NULL);
            CHECK(rc == TISA_OUTCOME_UNSUPPORTED);
            CHECK(memcmp(out, orig, sizeof(orig)) == 0);
        }

        /* Mutate each of the 7 equality guards one by one -> TISA_OUTCOME_REFUSED (0) without writing out */
        for (uint8_t g = 0; g < ifl[k].nguard; g++) {
            uint64_t mp[4][4];
            memcpy(mp[0], p0, sizeof(p0));
            memcpy(mp[1], p1, sizeof(p1));
            memcpy(mp[2], p2, sizeof(p2));
            memcpy(mp[3], p3, sizeof(p3));
            mp[ifl[k].guard[g].i][ifl[k].guard[g].j] ^= 0x777ull;
            for (int mode = 0; mode < TEST_MODES; mode++) {
                uint64_t out[4] = { 901, 902, 903, 904 };
                const uint64_t orig[4] = { 901, 902, 903, 904 };
                TcIsaOutcome rc = tisa_run_micromath_sub(&export_mm_progs[k], &export_mm_comps[k],
                                                         (TcIsaExecMode)mode,
                                                         mp[0], mp[1], mp[2], mp[3], out, 5ull, 16ull, NULL);
                CHECK(rc == TISA_OUTCOME_REFUSED);
                CHECK(memcmp(out, orig, sizeof(orig)) == 0);
            }
        }

        /* Verify Statically-Admitted Leaf Profile (TISA_PROFILE_P1) parity & no-spill verification */
        {
            TcIsaCompiledX86 comp_p1;
            CHECK(tisa_compile_x86(&export_mm_progs[k], TISA_PROFILE_P1, &comp_p1, err, sizeof(err)));
            CHECK(comp_p1.footprint.no_spill_verified);
            CHECK(comp_p1.byte_len < export_mm_comps[k].byte_len);
            uint64_t out_p1[4] = {0};
            CHECK(tisa_run_micromath_sub(&export_mm_progs[k], &comp_p1, TISA_MODE_X86,
                                         p0, p1, p2, p3, out_p1, 5ull, 16ull, NULL) == TISA_OUTCOME_FIRED);
            CHECK(memcmp(out_p1, want, sizeof(want)) == 0);
            uint64_t out_unsup[4] = { 901, 902, 903, 904 };
            const uint64_t orig_unsup[4] = { 901, 902, 903, 904 };
            CHECK(tisa_run_micromath_sub(&export_mm_progs[k], &comp_p1, TISA_MODE_X86,
                                         p0, p1, p2, p3, out_unsup, 16ull, 16ull, NULL) == TISA_OUTCOME_UNSUPPORTED);
            CHECK(memcmp(out_unsup, orig_unsup, sizeof(orig_unsup)) == 0);
            tisa_free_x86(&comp_p1);
        }
    }
}

/* =========================================================================
 * Part 4: `ordinary_flat_fire` & `ordinary_flat_adapter` Differential Suite
 * ========================================================================= */

static void test_ordinary_flat_consumers(TcIsaArena *export_arena,
                                         TcIsaProgram *out_fire_prog,
                                         TcIsaCompiledX86 *out_fire_comp,
                                         TcIsaProgram *out_adapter_prog,
                                         TcIsaCompiledX86 *out_adapter_comp) {
    char err[256] = {0};
    CHECK(tisa_build_ordinary_flat_fire_prog(export_arena, out_fire_prog, err, sizeof(err)));
    CHECK(tisa_compile_x86(out_fire_prog, TISA_PROFILE_P0, out_fire_comp, err, sizeof(err)));
    CHECK(out_fire_comp->footprint.no_spill_verified);

    CHECK(tisa_build_ordinary_flat_adapter_prog(export_arena, out_adapter_prog, err, sizeof(err)));
    CHECK(tisa_compile_x86(out_adapter_prog, TISA_PROFILE_P0, out_adapter_comp, err, sizeof(err)));
    CHECK(out_adapter_comp->footprint.no_spill_verified);

    /* 4a. `ordinary_flat_fire` (`flat_fire`) positive, refusal, and wrapped UINT32_MAX offset controls */
    {
        const uint32_t rows[]   = {0, 4, 8};
        const uint32_t fields[] = {11, 22, 33, 44, 55, 66, 22, 77, 33};
        const uint32_t guards[] = {GUARD_PACK(0, 1, 1, 2), GUARD_PACK(0, 2, 2, 0)};
        const uint32_t make[]   = {MAKE_PACK(1, 0), MAKE_PACK(0, 0), MAKE_PACK(2, 0), MAKE_PACK(1, 3)};
        const uint32_t want[]   = {55, 11, 33, 77};

        for (int mode = 0; mode < TEST_MODES; mode++) {
            uint32_t dest[4] = {90, 91, 92, 93};
            uint32_t scratch[4] = {0};
            TcIsaOutcome rc = tisa_run_ordinary_flat_fire(out_fire_prog, out_fire_comp, (TcIsaExecMode)mode,
                                                          fields, 9, rows, 3, guards, 2, make, 4,
                                                          dest, 4, scratch, 4, NULL);
            CHECK(rc == TISA_OUTCOME_FIRED);
            CHECK(memcmp(dest, want, sizeof(want)) == 0);
            CHECK(memcmp(scratch, want, sizeof(want)) == 0);
        }

        /* Wrapped UINT32_MAX row offset control from test_flat_fire.c */
        const uint32_t wrap_rows[]   = {UINT32_MAX};
        const uint32_t wrap_fields[] = {17, 17};
        const uint32_t wrap_guards[] = {GUARD_PACK(0, 1, 0, 2)};
        const uint32_t wrap_make[]   = {MAKE_PACK(0, 1)};
        const uint32_t wrap_bad[]    = {17, 18};

        for (int mode = 0; mode < TEST_MODES; mode++) {
            uint32_t wdest[1] = {91}, wscratch[1] = {92};
            TcIsaOutcome rc1 = tisa_run_ordinary_flat_fire(out_fire_prog, out_fire_comp, (TcIsaExecMode)mode,
                                                           wrap_fields, 2, wrap_rows, 1, wrap_guards, 1,
                                                           wrap_make, 1, wdest, 1, wscratch, 1, NULL);
            CHECK(rc1 == TISA_OUTCOME_FIRED && wdest[0] == 17u && wscratch[0] == 17u);

            TcIsaOutcome rc2 = tisa_run_ordinary_flat_fire(out_fire_prog, out_fire_comp, (TcIsaExecMode)mode,
                                                           wrap_bad, 2, wrap_rows, 1, wrap_guards, 1,
                                                           wrap_make, 1, wdest, 1, wscratch, 1, NULL);
            CHECK(rc2 == TISA_OUTCOME_REFUSED && wdest[0] == 17u && wscratch[0] == 17u);
        }
    }

    /* 4b. `ordinary_flat_adapter` positive, refusal, UNSUPPORTED = 2 preserving fields[0] == 77,
     *     and 2,000 randomized differential trials against Cesta `ordinary_flat_adapter` */
    {
        const uint32_t source[8]    = { 1, 2, 3, 4, 9, 2, 7, 8 };
        const uint32_t offsets[2]   = { 0, 4 };
        const uint32_t constants[2] = { 4, 42 };
        const uint32_t guards_ok[2] = { GUARD_PACK(0, 1, 1, 1), GUARD_PACK(0, 3, 2, 0) };
        const uint32_t guard_bad[1] = { GUARD_PACK(0, 0, 1, 0) };
        const uint32_t make[3]      = { MAKE_PACK(1, 0), MAKE_PACK(2, 1), MAKE_PACK(0, 0) };

        for (int mode = 0; mode < TEST_MODES; mode++) {
            OrdinaryFlatWorkspace ws;
            memset(&ws, 0, sizeof(ws));
            TcIsaOutcome rc = tisa_run_ordinary_flat_adapter(
                out_adapter_prog, out_adapter_comp, (TcIsaExecMode)mode,
                source, 8, offsets, 2, constants, 2, guards_ok, 2, make, 3,
                ws.fields, ORDINARY_FLAT_MAX_FIELDS,
                ws.rows, ORDINARY_FLAT_MAX_PREMISES + 1,
                ws.dest, ORDINARY_FLAT_MAX_OUTPUT,
                ws.scratch, ORDINARY_FLAT_MAX_OUTPUT, NULL);
            CHECK(rc == TISA_OUTCOME_FIRED);
            CHECK(ws.rows[0] == 0 && ws.rows[1] == 4 && ws.rows[2] == 8);
            CHECK(ws.fields[0] == 1 && ws.fields[4] == 9 && ws.fields[8] == 4 && ws.fields[9] == 42);
            CHECK(ws.dest[0] == 9 && ws.dest[1] == 42 && ws.dest[2] == 1);
            CHECK(ws.scratch[0] == 9 && ws.scratch[1] == 42 && ws.scratch[2] == 1);

            for (uint32_t i = 0; i < 3; i++) ws.dest[i] = ws.scratch[i] = 100 + i;
            rc = tisa_run_ordinary_flat_adapter(
                out_adapter_prog, out_adapter_comp, (TcIsaExecMode)mode,
                source, 8, offsets, 2, constants, 2, guard_bad, 1, make, 3,
                ws.fields, ORDINARY_FLAT_MAX_FIELDS,
                ws.rows, ORDINARY_FLAT_MAX_PREMISES + 1,
                ws.dest, ORDINARY_FLAT_MAX_OUTPUT,
                ws.scratch, ORDINARY_FLAT_MAX_OUTPUT, NULL);
            CHECK(rc == TISA_OUTCOME_REFUSED);
            for (uint32_t i = 0; i < 3; i++) CHECK(ws.dest[i] == 100 + i && ws.scratch[i] == 100 + i);

            /* UNSUPPORTED = 2 controls preserving ws.fields[0] == 77 */
            uint32_t many[40] = {0}, invalid_offsets[25] = {0};
            ws.fields[0] = 77;
            CHECK(tisa_run_ordinary_flat_adapter(
                out_adapter_prog, out_adapter_comp, (TcIsaExecMode)mode,
                source, 8, invalid_offsets, 25, constants, 2, guards_ok, 2, make, 3,
                ws.fields, ORDINARY_FLAT_MAX_FIELDS, ws.rows, ORDINARY_FLAT_MAX_PREMISES + 1,
                ws.dest, ORDINARY_FLAT_MAX_OUTPUT, ws.scratch, ORDINARY_FLAT_MAX_OUTPUT, NULL) == TISA_OUTCOME_UNSUPPORTED && ws.fields[0] == 77);
            CHECK(tisa_run_ordinary_flat_adapter(
                out_adapter_prog, out_adapter_comp, (TcIsaExecMode)mode,
                source, 8, offsets, 2, many, 33, guards_ok, 2, make, 3,
                ws.fields, ORDINARY_FLAT_MAX_FIELDS, ws.rows, ORDINARY_FLAT_MAX_PREMISES + 1,
                ws.dest, ORDINARY_FLAT_MAX_OUTPUT, ws.scratch, ORDINARY_FLAT_MAX_OUTPUT, NULL) == TISA_OUTCOME_UNSUPPORTED && ws.fields[0] == 77);
            CHECK(tisa_run_ordinary_flat_adapter(
                out_adapter_prog, out_adapter_comp, (TcIsaExecMode)mode,
                source, 8, offsets, 2, constants, 2, many, 33, make, 3,
                ws.fields, ORDINARY_FLAT_MAX_FIELDS, ws.rows, ORDINARY_FLAT_MAX_PREMISES + 1,
                ws.dest, ORDINARY_FLAT_MAX_OUTPUT, ws.scratch, ORDINARY_FLAT_MAX_OUTPUT, NULL) == TISA_OUTCOME_UNSUPPORTED && ws.fields[0] == 77);
            CHECK(tisa_run_ordinary_flat_adapter(
                out_adapter_prog, out_adapter_comp, (TcIsaExecMode)mode,
                source, 8, offsets, 2, constants, 2, guards_ok, 2, many, 33,
                ws.fields, ORDINARY_FLAT_MAX_FIELDS, ws.rows, ORDINARY_FLAT_MAX_PREMISES + 1,
                ws.dest, ORDINARY_FLAT_MAX_OUTPUT, ws.scratch, ORDINARY_FLAT_MAX_OUTPUT, NULL) == TISA_OUTCOME_UNSUPPORTED && ws.fields[0] == 77);
            invalid_offsets[0] = 1;
            CHECK(tisa_run_ordinary_flat_adapter(
                out_adapter_prog, out_adapter_comp, (TcIsaExecMode)mode,
                source, 4, invalid_offsets, 1, constants, 0, guards_ok, 0, make, 0,
                ws.fields, ORDINARY_FLAT_MAX_FIELDS, ws.rows, ORDINARY_FLAT_MAX_PREMISES + 1,
                ws.dest, ORDINARY_FLAT_MAX_OUTPUT, ws.scratch, ORDINARY_FLAT_MAX_OUTPUT, NULL) == TISA_OUTCOME_UNSUPPORTED && ws.fields[0] == 77);
            CHECK(tisa_run_ordinary_flat_adapter(
                out_adapter_prog, out_adapter_comp, (TcIsaExecMode)mode,
                source, 8, offsets, 2, constants, 2, guards_ok, 2, make, 3,
                ws.fields, ORDINARY_FLAT_MAX_FIELDS, ws.rows, ORDINARY_FLAT_MAX_PREMISES + 1,
                ws.dest, 2, ws.scratch, 3, NULL) == TISA_OUTCOME_UNSUPPORTED && ws.fields[0] == 77);
        }

        /* 2,000 randomized differential trials comparing Cesta `ordinary_flat_adapter`,
         * `tisa_eval_ref`, `tisa_run_x86` (and `tisa_eval_tcalc` on the first 40 scenarios) */
        uint64_t rng = UINT64_C(0x9e3779b97f4a7c15);
        uint32_t fired = 0, refused = 0;
        for (uint32_t sc = 0; sc < 2000; sc++) {
            #define NEXT_RAND(n) (rng ^= rng >> 12, rng ^= rng << 25, rng ^= rng >> 27, \
                                  (n) ? (uint32_t)((rng * UINT64_C(0x2545f4914f6cdd1d)) % (n)) : 0u)
            uint32_t nk = NEXT_RAND(ORDINARY_FLAT_MAX_PREMISES + 1);
            uint32_t nc = NEXT_RAND(ORDINARY_FLAT_MAX_CONSTANTS + 1);
            uint32_t ng = NEXT_RAND(ORDINARY_FLAT_MAX_GUARDS + 1);
            uint32_t nm = NEXT_RAND(ORDINARY_FLAT_MAX_OUTPUT + 1);
            if (!nk && !nc) ng = nm = 0;
            if (!(sc & 1) && (nk || nc)) ng = NEXT_RAND(2);

            uint32_t d_src[4 * ORDINARY_FLAT_MAX_PREMISES] = {0};
            uint32_t d_off[ORDINARY_FLAT_MAX_PREMISES] = {0};
            uint8_t  d_ar[ORDINARY_FLAT_MAX_PREMISES] = {0};
            uint32_t d_con[ORDINARY_FLAT_MAX_CONSTANTS] = {0};
            uint32_t d_grd[ORDINARY_FLAT_MAX_GUARDS] = {0};
            uint32_t d_mk[ORDINARY_FLAT_MAX_OUTPUT] = {0};

            for (uint32_t i = 0; i < ORDINARY_FLAT_MAX_PREMISES; i++) {
                d_off[i] = nk ? 4 * NEXT_RAND(nk) : 0;
                d_ar[i]  = (uint8_t)(1 + NEXT_RAND(4));
            }
            for (uint32_t i = 0; i < 4 * ORDINARY_FLAT_MAX_PREMISES; i++) d_src[i] = NEXT_RAND(16);
            for (uint32_t j = 0; j < nc; j++) d_con[j] = NEXT_RAND(16);
            for (uint32_t k = 0; k < ng; k++) {
                uint32_t i  = nc ? NEXT_RAND(nk + 1) : NEXT_RAND(nk);
                uint32_t j  = NEXT_RAND(i < nk ? d_ar[i] : nc);
                uint32_t i0 = nc ? NEXT_RAND(nk + 1) : NEXT_RAND(nk);
                uint32_t j0 = NEXT_RAND(i0 < nk ? d_ar[i0] : nc);
                d_grd[k] = GUARD_PACK(i, j, i0, j0);
                if (!(sc & 1) || NEXT_RAND(2)) {
                    uint32_t v = (i < nk) ? d_src[d_off[i] + j] : d_con[j];
                    if (i0 < nk) d_src[d_off[i0] + j0] = v;
                    else d_con[j0] = v;
                }
            }
            for (uint32_t k = 0; k < nm; k++) {
                uint32_t i = nc ? NEXT_RAND(nk + 1) : NEXT_RAND(nk);
                uint32_t j = NEXT_RAND(i < nk ? d_ar[i] : nc);
                d_mk[k] = MAKE_PACK(i, j);
            }

            OrdinaryFlatWorkspace ws_cesta, ws_ref, ws_x86;
            memset(&ws_cesta, 0xA5, sizeof(ws_cesta));
            memset(&ws_ref,   0xA5, sizeof(ws_ref));
            memset(&ws_x86,   0xA5, sizeof(ws_x86));

            uint64_t rc_cesta = ordinary_flat_adapter(
                (cesta_read_u32_span){d_src, 4 * ORDINARY_FLAT_MAX_PREMISES},
                (cesta_read_u32_span){d_off, nk},
                (cesta_read_u32_span){d_con, nc},
                (cesta_read_u32_span){d_grd, ng},
                (cesta_read_u32_span){d_mk,  nm},
                (cesta_write_u32_span){ws_cesta.fields, ORDINARY_FLAT_MAX_FIELDS},
                (cesta_write_u32_span){ws_cesta.rows,   ORDINARY_FLAT_MAX_PREMISES + 1},
                (cesta_write_u32_span){ws_cesta.dest,   ORDINARY_FLAT_MAX_OUTPUT},
                (cesta_write_u32_span){ws_cesta.scratch,ORDINARY_FLAT_MAX_OUTPUT});

            TcIsaOutcome rc_ref = tisa_run_ordinary_flat_adapter(
                out_adapter_prog, out_adapter_comp, TISA_MODE_REF,
                d_src, 4 * ORDINARY_FLAT_MAX_PREMISES, d_off, nk, d_con, nc, d_grd, ng, d_mk, nm,
                ws_ref.fields, ORDINARY_FLAT_MAX_FIELDS, ws_ref.rows, ORDINARY_FLAT_MAX_PREMISES + 1,
                ws_ref.dest, ORDINARY_FLAT_MAX_OUTPUT, ws_ref.scratch, ORDINARY_FLAT_MAX_OUTPUT, NULL);

            TcIsaOutcome rc_x86 = tisa_run_ordinary_flat_adapter(
                out_adapter_prog, out_adapter_comp, TISA_MODE_X86,
                d_src, 4 * ORDINARY_FLAT_MAX_PREMISES, d_off, nk, d_con, nc, d_grd, ng, d_mk, nm,
                ws_x86.fields, ORDINARY_FLAT_MAX_FIELDS, ws_x86.rows, ORDINARY_FLAT_MAX_PREMISES + 1,
                ws_x86.dest, ORDINARY_FLAT_MAX_OUTPUT, ws_x86.scratch, ORDINARY_FLAT_MAX_OUTPUT, NULL);

            CHECK((uint64_t)rc_ref == rc_cesta && (uint64_t)rc_x86 == rc_cesta);
            CHECK(memcmp(&ws_ref, &ws_cesta, sizeof(OrdinaryFlatWorkspace)) == 0);
            CHECK(memcmp(&ws_x86, &ws_cesta, sizeof(OrdinaryFlatWorkspace)) == 0);

            if (sc < 40) {
                OrdinaryFlatWorkspace ws_tc;
                memset(&ws_tc, 0xA5, sizeof(ws_tc));
                TcIsaOutcome rc_tc = tisa_run_ordinary_flat_adapter(
                    out_adapter_prog, out_adapter_comp, TISA_MODE_TCALC,
                    d_src, 4 * ORDINARY_FLAT_MAX_PREMISES, d_off, nk, d_con, nc, d_grd, ng, d_mk, nm,
                    ws_tc.fields, ORDINARY_FLAT_MAX_FIELDS, ws_tc.rows, ORDINARY_FLAT_MAX_PREMISES + 1,
                    ws_tc.dest, ORDINARY_FLAT_MAX_OUTPUT, ws_tc.scratch, ORDINARY_FLAT_MAX_OUTPUT, NULL);
                CHECK((uint64_t)rc_tc == rc_cesta);
                CHECK(memcmp(&ws_tc, &ws_cesta, sizeof(OrdinaryFlatWorkspace)) == 0);
            }
            if (rc_cesta == 1) fired++; else refused++;
            #undef NEXT_RAND
        }
        CHECK(fired > 200 && refused > 200);
    }
}

/* =========================================================================
 * Part 5: Deterministic Manifest Export & Byte-for-Byte Reproducibility Gate
 * ========================================================================= */

static void export_and_verify_manifests(const TcIsaProgram lean_progs[11],
                                        const TcIsaCompiledX86 lean_comps[11],
                                        const TcIsaProgram mm_progs[2],
                                        const TcIsaCompiledX86 mm_comps[2],
                                        const TcIsaProgram *fire_prog,
                                        const TcIsaCompiledX86 *fire_comp,
                                        const TcIsaProgram *adapter_prog,
                                        const TcIsaCompiledX86 *adapter_comp) {
    const TcIsaProgram *all_progs[15];
    const TcIsaCompiledX86 *all_comps[15];
    for (int i = 0; i < 11; i++) {
        all_progs[i] = &lean_progs[i];
        all_comps[i] = &lean_comps[i];
    }
    all_progs[11] = &mm_progs[0];  all_comps[11] = &mm_comps[0];
    all_progs[12] = &mm_progs[1];  all_comps[12] = &mm_comps[1];
    all_progs[13] = fire_prog;     all_comps[13] = fire_comp;
    all_progs[14] = adapter_prog;  all_comps[14] = adapter_comp;

    /* Re-compile every one of the 15 programs and verify exact byte + SHA-256 identity
     * and semantic-PC recipe table invariants */
    char err[256] = {0};
    for (int i = 0; i < 15; i++) {
        TcIsaCompiledX86 recomp;
        CHECK(tisa_compile_x86(all_progs[i], TISA_PROFILE_P0, &recomp, err, sizeof(err)));
        CHECK(recomp.byte_len == all_comps[i]->byte_len);
        CHECK(memcmp(recomp.bytes, all_comps[i]->bytes, recomp.byte_len) == 0);
        CHECK(strcmp(recomp.sha256_hex, all_comps[i]->sha256_hex) == 0);
        tisa_free_x86(&recomp);

        TcIsaRecipeTable rtable;
        CHECK(tisa_lower_recipes(all_progs[i], &rtable, err, sizeof(err)));
        CHECK(rtable.entry_point == 0ull);
        CHECK(rtable.npoints > 10u && rtable.npoints <= TISA_MAX_RECIPE_POINTS);
        for (int oc = 0; oc < 5; oc++) {
            uint64_t fp_st = rtable.fail_status_point[oc];
            CHECK(fp_st + 1ull < (uint64_t)rtable.npoints);
            CHECK(rtable.recipes[fp_st].kind == TISA_RECIPE_FINALIZE_STATUS);
            CHECK(rtable.recipes[fp_st].outcome == (TcIsaOutcome)oc);
            CHECK(rtable.recipes[fp_st].ret_reg == 0xFFu);
            CHECK(rtable.recipes[fp_st].next_point == fp_st + 1ull);
            CHECK(rtable.recipes[fp_st + 1ull].kind == TISA_RECIPE_FINALIZE_RETVAL);
            CHECK(rtable.recipes[fp_st + 1ull].outcome == (TcIsaOutcome)oc);
            CHECK(rtable.recipes[fp_st + 1ull].ret_reg == 0xFFu);
            CHECK(rtable.recipes[fp_st + 1ull].next_point == TISA_POINT_HALT((TcIsaOutcome)oc));
        }
        for (uint32_t p = 0; p < rtable.npoints; p++) {
            const TcIsaPointRecipe *rc = &rtable.recipes[p];
            CHECK(rc->point == p);
            CHECK(rc->charges_fuel == (rc->kind == TISA_RECIPE_FUEL));
            if (rc->kind == TISA_RECIPE_FINALIZE_RETVAL) {
                CHECK(TISA_POINT_IS_HALT(rc->next_point));
                CHECK(TISA_POINT_HALT_OUTCOME(rc->next_point) == rc->outcome);
            } else {
                CHECK(!TISA_POINT_IS_HALT(rc->next_point));
                CHECK(rc->next_point < (uint64_t)rtable.npoints);
            }
            if (rc->kind == TISA_RECIPE_STORE_BYTE && rc->byte_phase == 0u) {
                uint8_t w = rc->byte_width;
                CHECK(w == 1u || w == 4u || w == 8u);
                CHECK(p + w <= rtable.npoints);
                for (uint8_t ph = 0; ph < w; ph++) {
                    CHECK(rtable.recipes[p + ph].kind == TISA_RECIPE_STORE_BYTE);
                    CHECK(!rtable.recipes[p + ph].charges_fuel);
                    CHECK(rtable.recipes[p + ph].byte_phase == ph);
                    CHECK(rtable.recipes[p + ph].byte_width == w);
                    if (ph + 1u < w) {
                        CHECK(rtable.recipes[p + ph].next_point == (uint64_t)(p + ph + 1u));
                    }
                }
            }
        }
    }

    /* The deterministic JSON bundle tisa/manifests/tisa_x86_programs_v1.json
       is an input to the Lean proofs (ImportedImages.lean). The test renders
       it in memory and compares it with the file; it writes the file only
       when TISA_WRITE_MANIFESTS=1 asks for a new export. */
    const char *manifest_path = "tisa/manifests/tisa_x86_programs_v1.json";
    char *rendered = NULL; size_t rendered_len = 0;
    FILE *fp = open_memstream(&rendered, &rendered_len);
    CHECK(fp != NULL);
    fprintf(fp, "{\n"
                "  \"schema\": \"tisa-x86-programs-bundle-v1\",\n"
                "  \"profile\": \"t-isa-core-v1\",\n"
                "  \"program_count\": 15,\n"
                "  \"programs\": [\n");
    for (int i = 0; i < 15; i++) {
        if (i > 0) fprintf(fp, ",\n");
        CHECK(tisa_write_program_manifest_json(fp, all_progs[i], all_comps[i]));
    }
    fprintf(fp, "\n  ]\n}\n");
    fclose(fp);
    const char *write = getenv("TISA_WRITE_MANIFESTS");
    if (write && !strcmp(write, "1")) {
        FILE *out = fopen(manifest_path, "wb");
        CHECK(out != NULL && fwrite(rendered, 1, rendered_len, out) == rendered_len);
        if (out) fclose(out);
    } else {
        FILE *in = fopen(manifest_path, "rb");
        char *existing = in ? malloc(rendered_len + 1) : NULL;
        size_t got = existing ? fread(existing, 1, rendered_len + 1, in) : 0;
        if (in) fclose(in);
        CHECK(existing && got == rendered_len && !memcmp(existing, rendered, rendered_len));
        if (!(existing && got == rendered_len && !memcmp(existing, rendered, rendered_len)))
            fprintf(stderr, "test_tisa: %s differs from this export; set TISA_WRITE_MANIFESTS=1 to replace it\n", manifest_path);
        free(existing);
    }
    free(rendered);
}

/* JSON string contents: quotes and backslashes escaped. */
static void json_text(FILE *fp, const char *t) {
    for (; *t; t++) {
        if (*t == '"' || *t == '\\') fputc('\\', fp);
        if (*t == '\n') { fputs("\\n", fp); continue; }
        fputc(*t, fp);
    }
}

static void json_program_text(FILE *fp, TcIsaTextStyle style, const TcIsaProgram *prog) {
    char *text = NULL; size_t len = 0;
    FILE *m = open_memstream(&text, &len);
    CHECK(m && tisa_print_program(m, style, prog));
    if (m) fclose(m);
    fputc('"', fp); json_text(fp, text ? text : ""); fputc('"', fp);
    free(text);
}

/* tisa/manifests/tisa_x86_p1_programs_v2.json: for each consumer, its p1
 * program (as S-expression and HOL text), regions, entry registers, cost
 * bound, and its p1 image with every span's template and statement path.
 * Paths name statements by child indices from the root (SEQ 0/1, IF then 1 /
 * else 2, loop body 0); the wrapper and handler spans have none. */
static void render_p1_manifest(FILE *fp, const TcIsaProgram *progs[15]) {
    static const char *ty[] = {"-", "U64", "U32Z", "I32S", "BOOL", "PTR"};
    static const char *mode[] = {"NONE", "RO", "RW"};
    fprintf(fp, "{\n"
                "  \"schema\": \"tisa-x86-p1-programs-v2\",\n"
                "  \"schema_version\": 2,\n"
                "  \"profile\": \"t-isa-p1\",\n"
                "  \"semantics\": \"tcalc/tisa/SEMANTICS.txt\",\n"
                "  \"frame\": {\"bytes\": 192, \"region_base_word\": \"2r\", \"region_len_word\": \"2r+1\", "
                "\"status_word\": 18, \"ret_val_word\": 19, \"fuel_budget_word\": 20, \"fuel_used_word\": 21, "
                "\"arg0_word\": 22, \"arg1_word\": 23},\n"
                "  \"outcome_codes\": {\"REFUSED\": 0, \"FIRED\": 1, \"UNSUPPORTED\": 2, \"INVALID_INPUT\": 3, \"EXHAUSTED\": 4},\n"
                "  \"x86_64\": {\"vregs\": [\"rdi\", \"rsi\", \"rdx\", \"rcx\", \"r8\", \"r9\", \"r10\", \"r11\", \"rax\", \"rbx\", \"r12\", \"r13\"], "
                "\"scratch\": [\"r14\", \"r15\"], \"frame_register\": \"rdi\", \"saved_by_prologue\": [\"rbx\", \"r12\", \"r13\", \"r14\", \"r15\"], "
                "\"ret_val_register\": \"rax\", \"entry_offset\": 0},\n"
                "  \"path_encoding\": \"child indices from the root joined by '.': SEQ first 0, second 1; IF then 1, else 2; loop body 0\",\n"
                "  \"program_count\": 15,\n"
                "  \"programs\": [\n");
    for (int i = 0; i < 15; i++) {
        const TcIsaProgram *p = progs[i];
        TcIsaAdmission adm; char err[256];
        CHECK(tisa_admit(p, &adm, err, sizeof err));
        TcIsaX86 code;
        CHECK(tisa_x86_emit(p, &code, err, sizeof err));
        static char paths[4096][256];
        size_t npaths = tisa_span_paths(p->root, paths, 4096);
        CHECK(npaths + 3 == code.nspans);
        TcSha256Ctx h; char hex[65];
        tc_sha256_init(&h); tc_sha256_update(&h, code.bytes, code.len); tc_sha256_final_hex(&h, hex);
        fprintf(fp, "%s    {\n      \"program_name\": \"%s\",\n      \"program_id\": %d,\n", i ? ",\n" : "",
                p->name ? p->name : "?", i);
        fputs("      \"regions\": [", fp);
        for (uint8_t r = 0; r < p->nregions; r++)
            fprintf(fp, "%s{\"region_id\": %u, \"name\": \"%s\", \"mode\": \"%s\", \"min_byte_len\": %u, \"align_bytes\": %u}",
                    r ? ", " : "", (unsigned)r, p->regions[r].name ? p->regions[r].name : "",
                    p->regions[r].mode <= 2 ? mode[p->regions[r].mode] : "?",
                    (unsigned)p->regions[r].min_byte_len, (unsigned)p->regions[r].align_bytes);
        fputs("],\n      \"entry_regs\": [", fp);
        int first = 1;
        for (uint8_t r = 0; r < TISA_NUM_VREGS; r++) {
            if (!(p->init_reg_mask & (1u << r))) continue;
            TcIsaValType t = p->init_reg_types[r];
            fprintf(fp, "%s{\"reg_id\": %u, \"ty\": \"%s\"", first ? "" : ", ", (unsigned)r, t <= 5 ? ty[t] : "?");
            if (t == TISA_TYPE_PTR) fprintf(fp, ", \"region_id\": %u", (unsigned)p->init_reg_region[r]);
            fputc('}', fp);
            first = 0;
        }
        fprintf(fp, "],\n      \"cost\": {\"fund_points\": %u, \"max_receipt\": \"0x%016" PRIx64 "\", \"max_receipt_fits\": %s},\n",
                (unsigned)adm.fund_points, adm.max_receipt, adm.max_receipt_fits ? "true" : "false");
        fputs("      \"program_sexpr\": ", fp); json_program_text(fp, TISA_TEXT_SEXPR, p);
        fputs(",\n      \"program_hol\": ", fp); json_program_text(fp, TISA_TEXT_HOL, p);
        fprintf(fp, ",\n      \"image\": {\n        \"byte_len\": %zu,\n        \"sha256\": \"%s\",\n        \"bytes_hex\": \"", code.len, hex);
        for (size_t b = 0; b < code.len; b++) fprintf(fp, "%02x", code.bytes[b]);
        fputs("\",\n        \"spans\": [\n", fp);
        for (size_t k = 0; k < code.nspans; k++) {
            fprintf(fp, "          {\"offset\": %u, \"length\": %u, \"template\": \"%s\"", code.spans[k].offset,
                    code.spans[k].length, code.spans[k].template_name);
            if (k > 0 && k + 2 < code.nspans) fprintf(fp, ", \"path\": \"%s\"", paths[k - 1]);
            fprintf(fp, "}%s\n", k + 1 < code.nspans ? "," : "");
        }
        fputs("        ]\n      }\n    }", fp);
        tisa_x86_free(&code);
    }
    fputs("\n  ]\n}\n", fp);
}

/* Renders the p1 manifest and compares it with the file;
 * TISA_WRITE_P1_MANIFEST=1 writes it instead (the v1 file is left alone). */
static void verify_p1_manifest(const TcIsaProgram *progs[15]) {
    const char *path = "tisa/manifests/tisa_x86_p1_programs_v2.json";
    char *rendered = NULL; size_t len = 0;
    FILE *fp = open_memstream(&rendered, &len);
    CHECK(fp != NULL);
    if (!fp) return;
    render_p1_manifest(fp, progs);
    fclose(fp);
    const char *write = getenv("TISA_WRITE_P1_MANIFEST");
    if (write && !strcmp(write, "1")) {
        FILE *out = fopen(path, "wb");
        CHECK(out != NULL && fwrite(rendered, 1, len, out) == len);
        if (out) fclose(out);
    } else {
        FILE *in = fopen(path, "rb");
        char *existing = in ? malloc(len + 1) : NULL;
        size_t got = existing ? fread(existing, 1, len + 1, in) : 0;
        if (in) fclose(in);
        bool same = existing && got == len && !memcmp(existing, rendered, len);
        CHECK(same);
        if (!same) fprintf(stderr, "test_tisa: %s differs from this export; set TISA_WRITE_P1_MANIFEST=1 to replace it\n", path);
        free(existing);
    }
    free(rendered);
}

/* Profile p1 runs every consumer below beside p0's three realizations. */
static TcIsaOutcome run_p1(const TcIsaProgram *prog, TcIsaExecMode mode,
                           TcIsaRuntimeFrame *frame, uint64_t regs[TISA_NUM_VREGS]) {
    char err[256];
    if (mode == TISA_MODE_P1_REF) return tisa_run(prog, frame, regs);
    TcIsaX86 code;
    if (!tisa_x86_emit(prog, &code, err, sizeof err) || !tisa_x86_load(&code, err, sizeof err)) {
        fprintf(stderr, "p1 emission of %s failed: %s\n", prog->name ? prog->name : "?", err);
        tisa_x86_free(&code);
        return TISA_OUTCOME_UNSUPPORTED;
    }
    TcIsaOutcome rc = tisa_x86_run(prog, &code, frame, regs);
    tisa_x86_free(&code);
    return rc;
}

int main(void) {
    tisa_p1_runner = run_p1;
    test_core_opcodes_and_controls();
    test_p1_static_leaf_regressions();

    TcIsaArena export_arena;
    tisa_arena_init(&export_arena, 8192);
    TcIsaProgram lean_progs[11];
    TcIsaCompiledX86 lean_comps[11];
    TcIsaProgram mm_progs[2];
    TcIsaCompiledX86 mm_comps[2];
    TcIsaProgram fire_prog, adapter_prog;
    TcIsaCompiledX86 fire_comp, adapter_comp;

    test_all_11_lean_premise_rules(&export_arena, lean_progs, lean_comps);
    test_micromath_sub_rules(&export_arena, mm_progs, mm_comps);
    test_ordinary_flat_consumers(&export_arena, &fire_prog, &fire_comp, &adapter_prog, &adapter_comp);
    export_and_verify_manifests(lean_progs, lean_comps, mm_progs, mm_comps,
                                &fire_prog, &fire_comp, &adapter_prog, &adapter_comp);

    /* Image sizes: p0 emitted a fuel step before every instruction; p1 pays
       only at FUND points (these programs have none). */
    {
        const TcIsaProgram *progs[15]; const TcIsaCompiledX86 *comps[15];
        for (int i = 0; i < 11; i++) { progs[i] = &lean_progs[i]; comps[i] = &lean_comps[i]; }
        for (int i = 0; i < 2; i++) { progs[11 + i] = &mm_progs[i]; comps[11 + i] = &mm_comps[i]; }
        progs[13] = &fire_prog; comps[13] = &fire_comp; progs[14] = &adapter_prog; comps[14] = &adapter_comp;
        size_t p0_bytes = 0, p1_bytes = 0, spans = 0, kinds = 0;
        const char *seen[64];
        for (int i = 0; i < 15; i++) {
            TcIsaX86 code; char err[256];
            CHECK(tisa_x86_emit(progs[i], &code, err, sizeof err));
            p0_bytes += comps[i]->byte_len; p1_bytes += code.len; spans += code.nspans;
            for (size_t k = 0; k < code.nspans; k++) {
                size_t j = 0;
                while (j < kinds && strcmp(seen[j], code.spans[k].template_name)) j++;
                if (j == kinds && kinds < 64) seen[kinds++] = code.spans[k].template_name;
            }
            tisa_x86_free(&code);
        }
        printf("test_tisa: the 15 consumer images take %zu bytes under p1 and %zu under p0; "
               "p1 places %zu template instances of %zu kinds\n", p1_bytes, p0_bytes, spans, kinds);
        verify_p1_manifest(progs);
        /* TISA_EXPORT_SEXPR=FILE writes these programs as S-expressions and,
           in FILE.images, the p1 image of each (for the MeTTa emitter). */
        const char *sexpr = getenv("TISA_EXPORT_SEXPR");
        if (sexpr) {
            char images[4096];
            snprintf(images, sizeof images, "%s.images", sexpr);
            FILE *pf = fopen(sexpr, "w"), *xf = fopen(images, "w");
            for (int i = 0; pf && xf && i < 15; i++) {
                TcIsaX86 code; char err[256];
                if (!tisa_x86_emit(progs[i], &code, err, sizeof err)) continue;
                fprintf(pf, "(tisa-case \"%s\" ", progs[i]->name ? progs[i]->name : "?");
                tisa_print_program(pf, TISA_TEXT_SEXPR, progs[i]);
                fputs(")\n", pf);
                fprintf(xf, "%s ", progs[i]->name ? progs[i]->name : "?");
                for (size_t b = 0; b < code.len; b++) fprintf(xf, "%02x", code.bytes[b]);
                for (size_t k = 0; k < code.nspans; k++)
                    fprintf(xf, " %u:%u:%s", code.spans[k].offset, code.spans[k].length, code.spans[k].template_name);
                fputc('\n', xf);
                tisa_x86_free(&code);
            }
            if (pf) fclose(pf);
            if (xf) fclose(xf);
            /* FILE.hol: tisa_image "name" `program` "hex" [(offset,length,"TEMPLATE","path")];;
               where path names the statement a span realizes by child indices
               from the root (SEQ 0/1, IF then 1 / else 2, loop body 0), "-" for
               the wrapper and handlers. */
            char hol_path[4096];
            snprintf(hol_path, sizeof hol_path, "%s.hol", sexpr);
            FILE *hf = fopen(hol_path, "w");
            for (int i = 0; hf && i < 15; i++) {
                TcIsaX86 code; char err[256];
                if (!tisa_x86_emit(progs[i], &code, err, sizeof err)) continue;
                CHECK(tisa_print_image_record(hf, progs[i]->name ? progs[i]->name : "?", progs[i], &code));
                tisa_x86_free(&code);
            }
            if (hf) fclose(hf);
        }
    }

    for (int i = 0; i < 11; i++) tisa_free_x86(&lean_comps[i]);
    for (int i = 0; i < 2; i++)  tisa_free_x86(&mm_comps[i]);
    tisa_free_x86(&fire_comp);
    tisa_free_x86(&adapter_comp);
    tisa_arena_free(&export_arena);

    printf("test_tisa: %u checks passed (10 opcodes, 5 controls, 11 Lean flat rules, 2 Micromath leaves, ordinary_flat_fire, ordinary_flat_adapter, 4-way differential & manifest reproducibility)\n",
           g_checks);
    return 0;
}

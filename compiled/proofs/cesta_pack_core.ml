(* Exact linked-byte proof for the Cesta-generated ordinary_flat_pack.
   The checked-failure stub is outside the admitted valid-span contract. *)

let ordinary_pack_mc = define_from_elf "ordinary_pack_mc" ordinary_pack_object;;

let ORDINARY_PACK_EXEC = X86_MK_EXEC_RULE ordinary_pack_mc;;

let ordinary_pack_span_valid = new_definition
 `ordinary_pack_span_valid (a:int64) (xs:int32 list) <=>
    LENGTH xs < 2 EXP 61 /\
    (LENGTH xs = 0 \/ ~(a = word 0)) /\
    word_and a (word 3) = word 0 /\
    val a + 4 * LENGTH xs <= 2 EXP 64`;;

let ordinary_pack_offsets_valid = new_definition
 `ordinary_pack_offsets_valid (source:int32 list) (offsets:int32 list) <=>
    ALL (\offset. val offset + 4 <= LENGTH source) offsets`;;

let ORDINARY_PACK_OFFSETS_VALID = prove
 (`!source offsets.
    ordinary_pack_offsets_valid source offsets <=>
    ALL (\offset. val offset <= LENGTH source /\
                  4 <= LENGTH source - val offset) offsets`,
  REWRITE_TAC[ordinary_pack_offsets_valid;
    ARITH_RULE `!n offset. offset + 4 <= n <=>
                           offset <= n /\ 4 <= n - offset`]);;

let ordinary_pack_shape_valid = new_definition
 `ordinary_pack_shape_valid (offsets:int32 list) (constants:int32 list)
      (fields:int32 list) (rows:int32 list) <=>
    LENGTH offsets <= 24 /\ LENGTH constants <= 32 /\
    4 * LENGTH offsets + LENGTH constants <= LENGTH fields /\
    LENGTH offsets + 1 <= LENGTH rows`;;

let ordinary_pack_result_fields = new_definition
 `ordinary_pack_result_fields (source:int32 list) (offsets:int32 list)
      (constants:int32 list) (fields:int32 list) =
    APPEND
      (ordinary_fields
        (ordinary_arena_rows source (MAP (\offset. val offset) offsets)) constants)
      (ordinary_drop (4 * LENGTH offsets + LENGTH constants) fields)`;;

let ordinary_pack_result_rows = new_definition
 `ordinary_pack_result_rows (source:int32 list) (offsets:int32 list)
      (rows:int32 list) =
    APPEND
      (ordinary_rows
        (ordinary_arena_rows source (MAP (\offset. val offset) offsets)))
      (ordinary_drop (LENGTH offsets + 1) rows)`;;

let ordinary_pack_rejects = new_definition
 `ordinary_pack_rejects (source:int32 list) (offsets:int32 list)
      (constants:int32 list) (fields:int32 list) (rows:int32 list) <=>
    ~(ordinary_pack_shape_valid offsets constants fields rows) \/
    ~(ordinary_pack_offsets_valid source offsets)`;;

let ordinary_pack_entry = new_definition
 `ordinary_pack_entry pc source premises constants fields rows
      (source_xs:int32 list) (offsets:int32 list) (constants_xs:int32 list)
      (fields_xs:int32 list) (rows_xs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15 e s <=>
    bytes_loaded s (word pc) ordinary_pack_mc /\
    read RIP s = word pc /\
    read RSP s = stackpointer /\
    read (memory :> bytes64 stackpointer) s = returnaddress /\
    C_ARGUMENTS [source; word(LENGTH source_xs);
                 premises; word(LENGTH offsets);
                 constants; word(LENGTH constants_xs)] s /\
    read (memory :> bytes64 (word_add stackpointer (word 8))) s = fields /\
    read (memory :> bytes64 (word_add stackpointer (word 16))) s =
      word(LENGTH fields_xs) /\
    read (memory :> bytes64 (word_add stackpointer (word 24))) s = rows /\
    read (memory :> bytes64 (word_add stackpointer (word 32))) s =
      word(LENGTH rows_xs) /\
    read RBP s = init_rbp /\ read RBX s = init_rbx /\
    read R12 s = init_r12 /\ read R13 s = init_r13 /\
    read R14 s = init_r14 /\ read R15 s = init_r15 /\
    read events s = e /\
    wordlist_from_memory(source,LENGTH source_xs) s = source_xs /\
    wordlist_from_memory(premises,LENGTH offsets) s = offsets /\
    wordlist_from_memory(constants,LENGTH constants_xs) s = constants_xs /\
    wordlist_from_memory(fields,LENGTH fields_xs) s = fields_xs /\
    wordlist_from_memory(rows,LENGTH rows_xs) s = rows_xs`;;

let ordinary_pack_return = new_definition
 `ordinary_pack_return returnvalue stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s <=>
    read RIP s = returnaddress /\
    read RSP s = word_add stackpointer (word 8) /\
    C_RETURN s = word returnvalue /\
    read RBP s = init_rbp /\ read RBX s = init_rbx /\
    read R12 s = init_r12 /\ read R13 s = init_r13 /\
    read R14 s = init_r14 /\ read R15 s = init_r15`;;

let ordinary_pack_trace = new_definition
 `ordinary_pack_trace e source premises constants fields rows
      (source_xs:int32 list) (offsets:int32 list) (constants_xs:int32 list)
      (fields_xs:int32 list) (rows_xs:int32 list) stackpointer s <=>
    ?e2. read events s = APPEND e2 e /\
         memaccess_inbounds e2
           [(source,4 * LENGTH source_xs);
            (premises,4 * LENGTH offsets);
            (constants,4 * LENGTH constants_xs);
            (word_sub stackpointer (word 72),80)]
           [(word_sub stackpointer (word 72),72);
            (fields,4 * LENGTH fields_xs);
            (rows,4 * LENGTH rows_xs)]`;;

let ordinary_pack_reject_frame = new_definition
 `ordinary_pack_reject_frame stackpointer : x86state->x86state->bool =
    MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [events] ,,
    MAYCHANGE [memory :> bytes(word_sub stackpointer (word 72),72)]`;;

let ordinary_pack_frame = new_definition
 `ordinary_pack_frame fields rows (fields_xs:int32 list) (rows_xs:int32 list)
      stackpointer : x86state->x86state->bool =
    ordinary_pack_reject_frame stackpointer ,,
    MAYCHANGE [memory :> bytes(fields,4 * LENGTH fields_xs);
               memory :> bytes(rows,4 * LENGTH rows_xs)]`;;

let ORDINARY_PACK_STACK_RESTORE = prove
 (`!sp:int64.
     word_add (word_sub sp (word 72)) (word 72) = sp /\
     word_add (word_sub sp (word 72)) (word 80) = word_add sp (word 8) /\
     word_add (word_sub sp (word 72)) (word 88) = word_add sp (word 16) /\
     word_add (word_sub sp (word 72)) (word 96) = word_add sp (word 24) /\
     word_add (word_sub sp (word 72)) (word 104) = word_add sp (word 32)`,
  CONV_TAC WORD_RULE);;

let ORDINARY_PACK_WORD_SCALE4 = prove
 (`!n. word_shl (word n:int64) 2 = word(4 * n)`,
  CONV_TAC WORD_RULE);;

let ORDINARY_PACK_WORD_FIELD_COUNT = prove
 (`!nk nc. word_add (word nc:int64) (word_shl (word nk) 2) =
             word(4 * nk + nc)`,
  CONV_TAC WORD_RULE);;

let ORDINARY_PACK_WORD_ROW_COUNT = prove
 (`!n. word_add (word n:int64) (word 1) = word(n + 1)`,
  CONV_TAC WORD_RULE);;

let ORDINARY_PACK_COUNT_VAL = prove
 (`!nk nc. nk <= 24 /\ nc <= 32
     ==> val(word(4 * nk + nc):int64) = 4 * nk + nc /\
         val(word(nk + 1):int64) = nk + 1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64] THEN
  ASM_ARITH_TAC);;

let ORDINARY_WORD_ZX_EQ_0 = prove
 (`!x:M word. dimindex(:M) <= dimindex(:N)
     ==> ((word_zx:M word->N word) x = word 0 <=> x = word 0)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM VAL_EQ; VAL_WORD_ZX; VAL_WORD_0]);;

let ordinary_pack_normalize_state : tactic = fun ((asl,_) as goal) ->
  let stateful th = exists (fun v -> type_of v = `:x86state`) (frees(concl th)) in
  let facts = filter (fun th -> not(stateful th)) (map snd asl) in
  let rules = [ORDINARY_PACK_STACK_RESTORE; CESTA_STACK_RESTORE; CESTA_BYTE_RESIDUE; CESTA_LOW_BYTE_JOIN;
               CESTA_SUB_ZERO; WORD_AND_0; WORD_OR_0; WORD_OR_EQ_0;
               ORDINARY_PACK_WORD_SCALE4; ORDINARY_PACK_WORD_FIELD_COUNT;
               ORDINARY_PACK_WORD_ROW_COUNT; ORDINARY_PACK_COUNT_VAL;
               WORD_ULT; WORD_ULE; VAL_WORD_EQ_EQ;
               ORDINARY_WORD_ZX_EQ_0; WORD_OR_REFL; WORD_AND_REFL;
               WORD_SUB_0; VAL_WORD_0; VAL_WORD_1; VAL_EQ_0; ARITH_EQ; CONJUNCT1 LT; LENGTH;
               DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64; DIMINDEX_128;
               ARITH_RULE `n <= 0 <=> n = 0`;
               ARITH_RULE `~(a < b) /\ ~(a = b) <=> b < a`;
               ARITH_RULE `~(a < b \/ a = b) <=> b < a`] in
  RULE_ASSUM_TAC (fun th -> if stateful th then
    REWRITE_RULE (rules @ facts) (CONV_RULE WORD_REDUCE_CONV (REWRITE_RULE rules th))
    else th) goal;;

let ordinary_pack_steps exec indices =
  MAP_EVERY (fun index ->
    X86_STEPS_TAC exec [index] THEN ordinary_pack_normalize_state) indices;;

let ordinary_pack_sim_return exec steps =
  GHOST_INTRO_TAC `rax_before_return:int64` `read RAX` THEN
  GHOST_INTRO_TAC `r8_before_return:int64` `read R8` THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ordinary_pack_steps exec (1--steps) THEN ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ORDINARY_PACK_STACK_RESTORE] THEN
  SUBGOAL_THEN
   `(EventLoad(stackpointer:int64,8):uarch_event) =
    EventLoad(word_add (word_sub stackpointer (word 72)) (word 72),8)`
  ASSUME_TAC THENL [REWRITE_TAC[ORDINARY_PACK_STACK_RESTORE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let ordinary_pack_count_exfalso : tactic = fun ((asl,w) as goal) ->
  let fact tm = try Some(snd(List.find (fun (_,th) -> concl th = tm) asl))
                with Not_found -> None in
  match fact `24 < LENGTH(offsets:int32 list) \/
                 32 < LENGTH(constants_xs:int32 list)`,
        fact `LENGTH(offsets:int32 list) = 0`,
        fact `LENGTH(constants_xs:int32 list) = 0` with
  | Some bad,Some z1,Some z2 ->
      ACCEPT_TAC (MATCH_MP (TAUT (mk_imp(`F`,w))) (REWRITE_RULE
        [z1; z2; ARITH_RULE `24 < 0 <=> F`; ARITH_RULE `32 < 0 <=> F`;
         TAUT `(F \/ F) <=> F`] bad)) goal
  | _ -> ALL_TAC goal;;

let ordinary_pack_validate_spans : tactic =
  MAP_EVERY VAL_INT64_TAC
    [`LENGTH(source_xs:int32 list)`; `LENGTH(offsets:int32 list)`;
     `LENGTH(constants_xs:int32 list)`; `LENGTH(fields_xs:int32 list)`;
     `LENGTH(rows_xs:int32 list)`] THEN
  SUBGOAL_THEN
   `word_ushr (word(LENGTH(source_xs:int32 list)):int64) 61 = word 0 /\
    word_ushr (word(LENGTH(offsets:int32 list)):int64) 61 = word 0 /\
    word_ushr (word(LENGTH(constants_xs:int32 list)):int64) 61 = word 0 /\
    word_ushr (word(LENGTH(fields_xs:int32 list)):int64) 61 = word 0 /\
    word_ushr (word(LENGTH(rows_xs:int32 list)):int64) 61 = word 0`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[CESTA_LENGTH_SHIFT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_and (word_zx (source:int64):byte) (word 3) = word 0 /\
    word_and (word_zx (premises:int64):byte) (word 3) = word 0 /\
    word_and (word_zx (constants:int64):byte) (word 3) = word 0 /\
    word_and (word_zx (fields:int64):byte) (word 3) = word 0 /\
    word_and (word_zx (rows:int64):byte) (word 3) = word 0`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[CESTA_ALIGNED_BYTE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(LENGTH(source_xs:int32 list) = 0 \/ ~(val(source:int64) = 0)) /\
    (LENGTH(offsets:int32 list) = 0 \/ ~(val(premises:int64) = 0)) /\
    (LENGTH(constants_xs:int32 list) = 0 \/ ~(val(constants:int64) = 0)) /\
    (LENGTH(fields_xs:int32 list) = 0 \/ ~(val(fields:int64) = 0)) /\
    (LENGTH(rows_xs:int32 list) = 0 \/ ~(val(rows:int64) = 0))`
  (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THENL
   [ASM_MESON_TAC[VAL_EQ_0]; ALL_TAC] THEN
  GHOST_INTRO_TAC `rax_before_return:int64` `read RAX` THEN
  GHOST_INTRO_TAC `r8_before_return:int64` `read R8` THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ordinary_pack_steps ORDINARY_PACK_EXEC (1--9) THEN
  SUBGOAL_THEN
   `word_add (read RSP s9) (word 80) = word_add stackpointer (word 8) /\
    word_add (read RSP s9) (word 88) = word_add stackpointer (word 16) /\
    word_add (read RSP s9) (word 96) = word_add stackpointer (word 24) /\
    word_add (read RSP s9) (word 104) = word_add stackpointer (word 32)`
  (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THENL
   [REPEAT CONJ_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes64 (word_add (read RSP s9) (word 80))) s9 = fields /\
    read (memory :> bytes64 (word_add (read RSP s9) (word 88))) s9 =
      word(LENGTH(fields_xs:int32 list)) /\
    read (memory :> bytes64 (word_add (read RSP s9) (word 96))) s9 = rows /\
    read (memory :> bytes64 (word_add (read RSP s9) (word 104))) s9 =
      word(LENGTH(rows_xs:int32 list))`
  (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ordinary_pack_steps ORDINARY_PACK_EXEC (10--13) THEN
  ASM_CASES_TAC `LENGTH(source_xs:int32 list) = 0` THENL
   [ordinary_pack_steps ORDINARY_PACK_EXEC (1--2);
    SUBGOAL_THEN `~(val(source:int64) = 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ordinary_pack_steps ORDINARY_PACK_EXEC (1--7) THEN
    ordinary_pack_steps ORDINARY_PACK_EXEC (8--9)] THEN
  (ASM_CASES_TAC `LENGTH(offsets:int32 list) = 0` THENL
   [ordinary_pack_steps ORDINARY_PACK_EXEC (1--2);
    SUBGOAL_THEN `~(val(premises:int64) = 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ordinary_pack_steps ORDINARY_PACK_EXEC (1--9)]) THEN
  (ASM_CASES_TAC `LENGTH(constants_xs:int32 list) = 0` THENL
   [ordinary_pack_steps ORDINARY_PACK_EXEC (1--2);
    SUBGOAL_THEN `~(val(constants:int64) = 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ordinary_pack_steps ORDINARY_PACK_EXEC (1--9)]) THEN
  (ASM_CASES_TAC `LENGTH(fields_xs:int32 list) = 0` THENL
   [ordinary_pack_steps ORDINARY_PACK_EXEC (1--2);
    SUBGOAL_THEN `~(val(fields:int64) = 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ordinary_pack_steps ORDINARY_PACK_EXEC (1--2) THEN
    ordinary_pack_steps ORDINARY_PACK_EXEC (3--9)]) THEN
  (ASM_CASES_TAC `LENGTH(rows_xs:int32 list) = 0` THENL
   [ordinary_pack_steps ORDINARY_PACK_EXEC (1--2);
    SUBGOAL_THEN `~(val(rows:int64) = 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ordinary_pack_steps ORDINARY_PACK_EXEC (1--9)]);;


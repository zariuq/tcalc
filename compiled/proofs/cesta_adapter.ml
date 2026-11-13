(* Exact linked-byte proof for the Cesta-generated ordinary_flat_adapter.
   The leaf and pack are separate linked subprograms; their proofs are composed
   at the actual call sites rather than identified with the adapter's entry. *)

let ordinary_cesta_mc = define_from_elf "ordinary_cesta_mc" ordinary_cesta_object;;
Printf.printf "CESTA_ADAPTER defined bytes\n%!";;

let ORDINARY_CESTA_EXEC = X86_MK_EXEC_RULE ordinary_cesta_mc;;
Printf.printf "CESTA_ADAPTER exec rule\n%!";;

let ordinary_adapter_span_valid = new_definition
 `ordinary_adapter_span_valid (a:int64) (xs:int32 list) <=>
    LENGTH xs < 2 EXP 61 /\
    (LENGTH xs = 0 \/ ~(a = word 0)) /\
    word_and a (word 3) = word 0 /\
    val a + 4 * LENGTH xs <= 2 EXP 64`;;

let ordinary_adapter_offsets_valid = new_definition
 `ordinary_adapter_offsets_valid (source:int32 list) (offsets:int32 list) <=>
    ALL (\offset. val offset + 4 <= LENGTH source) offsets`;;

let ordinary_adapter_shape_valid = new_definition
 `ordinary_adapter_shape_valid (offsets:int32 list) (constants:int32 list)
      (guards:int32 list) (makes:int32 list) (fields:int32 list)
      (rows:int32 list) (dest:int32 list) (scratch:int32 list) <=>
    LENGTH offsets <= 24 /\ LENGTH constants <= 32 /\
    LENGTH guards <= 32 /\ LENGTH makes <= 32 /\
    4 * LENGTH offsets + LENGTH constants <= LENGTH fields /\
    LENGTH offsets + 1 <= LENGTH rows /\
    LENGTH makes <= LENGTH dest /\ LENGTH makes <= LENGTH scratch`;;

let ordinary_adapter_entry = new_definition
 `ordinary_adapter_entry pc source premises constants guards makes fields rows
      dest scratch (source_xs:int32 list) (offsets:int32 list)
      (constants_xs:int32 list) (guards_xs:int32 list) (makes_xs:int32 list)
      (fields_xs:int32 list) (rows_xs:int32 list) (dest_xs:int32 list)
      (scratch_xs:int32 list) stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e s <=>
    bytes_loaded s (word pc) ordinary_cesta_mc /\
    read RIP s = word (pc + 0x2e5) /\
    read RSP s = stackpointer /\
    read (memory :> bytes64 stackpointer) s = returnaddress /\
    C_ARGUMENTS [source; word(LENGTH source_xs);
                 premises; word(LENGTH offsets);
                 constants; word(LENGTH constants_xs)] s /\
    read (memory :> bytes64 (word_add stackpointer (word 8))) s = guards /\
    read (memory :> bytes64 (word_add stackpointer (word 16))) s =
      word(LENGTH guards_xs) /\
    read (memory :> bytes64 (word_add stackpointer (word 24))) s = makes /\
    read (memory :> bytes64 (word_add stackpointer (word 32))) s =
      word(LENGTH makes_xs) /\
    read (memory :> bytes64 (word_add stackpointer (word 40))) s = fields /\
    read (memory :> bytes64 (word_add stackpointer (word 48))) s =
      word(LENGTH fields_xs) /\
    read (memory :> bytes64 (word_add stackpointer (word 56))) s = rows /\
    read (memory :> bytes64 (word_add stackpointer (word 64))) s =
      word(LENGTH rows_xs) /\
    read (memory :> bytes64 (word_add stackpointer (word 72))) s = dest /\
    read (memory :> bytes64 (word_add stackpointer (word 80))) s =
      word(LENGTH dest_xs) /\
    read (memory :> bytes64 (word_add stackpointer (word 88))) s = scratch /\
    read (memory :> bytes64 (word_add stackpointer (word 96))) s =
      word(LENGTH scratch_xs) /\
    read RBP s = init_rbp /\ read RBX s = init_rbx /\
    read R12 s = init_r12 /\ read R13 s = init_r13 /\
    read R14 s = init_r14 /\ read R15 s = init_r15 /\
    read events s = e /\
    wordlist_from_memory(source,LENGTH source_xs) s = source_xs /\
    wordlist_from_memory(premises,LENGTH offsets) s = offsets /\
    wordlist_from_memory(constants,LENGTH constants_xs) s = constants_xs /\
    wordlist_from_memory(guards,LENGTH guards_xs) s = guards_xs /\
    wordlist_from_memory(makes,LENGTH makes_xs) s = makes_xs /\
    wordlist_from_memory(fields,LENGTH fields_xs) s = fields_xs /\
    wordlist_from_memory(rows,LENGTH rows_xs) s = rows_xs /\
    wordlist_from_memory(dest,LENGTH dest_xs) s = dest_xs /\
    wordlist_from_memory(scratch,LENGTH scratch_xs) s = scratch_xs`;;

let ordinary_adapter_return = new_definition
 `ordinary_adapter_return returnvalue stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s <=>
    read RIP s = returnaddress /\
    read RSP s = word_add stackpointer (word 8) /\
    C_RETURN s = word returnvalue /\
    read RBP s = init_rbp /\ read RBX s = init_rbx /\
    read R12 s = init_r12 /\ read R13 s = init_r13 /\
    read R14 s = init_r14 /\ read R15 s = init_r15`;;

let ordinary_adapter_reject_frame = new_definition
 `ordinary_adapter_reject_frame stackpointer : (x86state,x86state)rel =
    MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [events; memory :> bytes(word_sub stackpointer (word 120),120)]`;;

let ordinary_adapter_frame = new_definition
 `ordinary_adapter_frame fields rows dest scratch
      (fields_xs:int32 list) (rows_xs:int32 list) (dest_xs:int32 list)
      (scratch_xs:int32 list) stackpointer : (x86state,x86state)rel =
    ordinary_adapter_reject_frame stackpointer ,,
    MAYCHANGE [memory :> bytes(fields,4 * LENGTH fields_xs);
               memory :> bytes(rows,4 * LENGTH rows_xs);
               memory :> bytes(dest,4 * LENGTH dest_xs);
               memory :> bytes(scratch,4 * LENGTH scratch_xs)]`;;

let ORDINARY_ADAPTER_STACK_RESTORE = prove
 (`!sp:int64.
     word_add (word_sub sp (word 120)) (word 120) = sp /\
     word_add (word_sub sp (word 120)) (word 128) = word_add sp (word 8)`,
  CONV_TAC WORD_RULE);;

let ordinary_adapter_reject_trace = new_definition
 `ordinary_adapter_reject_trace e stackpointer s <=>
    ?e2. read events s = APPEND e2 e /\
         memaccess_inbounds e2
           [(word_sub stackpointer (word 120),128)]
           [(word_sub stackpointer (word 120),120)]`;;

let ordinary_adapter_normalize_state : tactic = fun ((asl,_) as goal) ->
  let stateful th = exists (fun v -> type_of v = `:x86state`) (frees(concl th)) in
  let facts = filter (fun th -> not(stateful th)) (map snd asl) in
  let rules = [ORDINARY_ADAPTER_STACK_RESTORE; CESTA_STACK_RESTORE;
               CESTA_BYTE_RESIDUE; CESTA_LOW_BYTE_JOIN; CESTA_SUB_ZERO;
               WORD_AND_0; WORD_OR_0; WORD_OR_REFL; WORD_AND_REFL;
               WORD_SUB_0; VAL_WORD_0; VAL_WORD_1; ARITH_EQ; CONJUNCT1 LT; LENGTH;
               ARITH_RULE `n <= 0 <=> n = 0`;
               ARITH_RULE `~(a < b) /\ ~(a = b) <=> b < a`;
               ARITH_RULE `~(a < b \/ a = b) <=> b < a`] in
  RULE_ASSUM_TAC (fun th -> if stateful th then
    REWRITE_RULE (rules @ facts) (CONV_RULE WORD_REDUCE_CONV (REWRITE_RULE rules th))
    else th) goal;;

let ordinary_adapter_steps exec indices =
  MAP_EVERY (fun index -> X86_STEPS_TAC exec [index] THEN ordinary_adapter_normalize_state) indices;;

let ORDINARY_ADAPTER_COUNT_REJECT_MC_CORRECT = prove
 (`!pc source premises constants guards makes fields rows dest scratch
      source_xs offsets constants_xs guards_xs makes_xs fields_xs rows_xs
      dest_xs scratch_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e.
    ordinary_adapter_span_valid source source_xs /\
    ordinary_adapter_span_valid premises offsets /\
    ordinary_adapter_span_valid constants constants_xs /\
    ordinary_adapter_span_valid guards guards_xs /\
    ordinary_adapter_span_valid makes makes_xs /\
    ordinary_adapter_span_valid fields fields_xs /\
    ordinary_adapter_span_valid rows rows_xs /\
    ordinary_adapter_span_valid dest dest_xs /\
    ordinary_adapter_span_valid scratch scratch_xs /\
    (32 < LENGTH guards_xs \/ 32 < LENGTH makes_xs \/
     LENGTH dest_xs < LENGTH makes_xs \/ LENGTH scratch_xs < LENGTH makes_xs) /\
    120 <= val stackpointer /\
    ALL (nonoverlapping (word_sub stackpointer (word 120),128))
      [(word pc,LENGTH ordinary_cesta_mc);
       (source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs); (guards,4 * LENGTH guards_xs);
       (makes,4 * LENGTH makes_xs); (fields,4 * LENGTH fields_xs);
       (rows,4 * LENGTH rows_xs); (dest,4 * LENGTH dest_xs);
       (scratch,4 * LENGTH scratch_xs)]
    ==> ensures x86
      (ordinary_adapter_entry pc source premises constants guards makes fields rows
         dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
         rows_xs dest_xs scratch_xs stackpointer returnaddress
         init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e)
      (\s. ordinary_adapter_return 2 stackpointer returnaddress
             init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s /\
           ordinary_adapter_reject_trace e stackpointer s /\
           wordlist_from_memory(source,LENGTH source_xs) s = source_xs /\
           wordlist_from_memory(premises,LENGTH offsets) s = offsets /\
           wordlist_from_memory(constants,LENGTH constants_xs) s = constants_xs /\
           wordlist_from_memory(guards,LENGTH guards_xs) s = guards_xs /\
           wordlist_from_memory(makes,LENGTH makes_xs) s = makes_xs /\
           wordlist_from_memory(fields,LENGTH fields_xs) s = fields_xs /\
           wordlist_from_memory(rows,LENGTH rows_xs) s = rows_xs /\
           wordlist_from_memory(dest,LENGTH dest_xs) s = dest_xs /\
           wordlist_from_memory(scratch,LENGTH scratch_xs) s = scratch_xs)
      (ordinary_adapter_reject_frame stackpointer)`,
  REWRITE_TAC[ordinary_adapter_span_valid; ordinary_adapter_entry;
              ordinary_adapter_return; ordinary_adapter_reject_trace;
              ordinary_adapter_reject_frame; C_ARGUMENTS; SOME_FLAGS; ALL;
              NONOVERLAPPING_CLAUSES; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst ORDINARY_CESTA_EXEC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY VAL_INT64_TAC
    [`LENGTH(source_xs:int32 list)`; `LENGTH(offsets:int32 list)`;
     `LENGTH(constants_xs:int32 list)`; `LENGTH(guards_xs:int32 list)`;
     `LENGTH(makes_xs:int32 list)`; `LENGTH(fields_xs:int32 list)`;
     `LENGTH(rows_xs:int32 list)`; `LENGTH(dest_xs:int32 list)`;
     `LENGTH(scratch_xs:int32 list)`] THEN
  SUBGOAL_THEN
   `word_ushr (word(LENGTH(source_xs:int32 list)):int64) 61 = word 0 /\
    word_ushr (word(LENGTH(offsets:int32 list)):int64) 61 = word 0 /\
    word_ushr (word(LENGTH(constants_xs:int32 list)):int64) 61 = word 0 /\
    word_ushr (word(LENGTH(guards_xs:int32 list)):int64) 61 = word 0 /\
    word_ushr (word(LENGTH(makes_xs:int32 list)):int64) 61 = word 0 /\
    word_ushr (word(LENGTH(fields_xs:int32 list)):int64) 61 = word 0 /\
    word_ushr (word(LENGTH(rows_xs:int32 list)):int64) 61 = word 0 /\
    word_ushr (word(LENGTH(dest_xs:int32 list)):int64) 61 = word 0 /\
    word_ushr (word(LENGTH(scratch_xs:int32 list)):int64) 61 = word 0`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[CESTA_LENGTH_SHIFT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_and (word_zx (source:int64):byte) (word 3) = word 0 /\
    word_and (word_zx (premises:int64):byte) (word 3) = word 0 /\
    word_and (word_zx (constants:int64):byte) (word 3) = word 0 /\
    word_and (word_zx (guards:int64):byte) (word 3) = word 0 /\
    word_and (word_zx (makes:int64):byte) (word 3) = word 0 /\
    word_and (word_zx (fields:int64):byte) (word 3) = word 0 /\
    word_and (word_zx (rows:int64):byte) (word 3) = word 0 /\
    word_and (word_zx (dest:int64):byte) (word 3) = word 0 /\
    word_and (word_zx (scratch:int64):byte) (word 3) = word 0`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[CESTA_ALIGNED_BYTE]; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--25) THEN
  ASM_CASES_TAC `LENGTH(source_xs:int32 list) = 0` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--1);
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--8)] THEN
  ASM_CASES_TAC `LENGTH(offsets:int32 list) = 0` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--1);
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--8)] THEN
  ASM_CASES_TAC `LENGTH(constants_xs:int32 list) = 0` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--1);
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--8)] THEN
  ASM_CASES_TAC `LENGTH(guards_xs:int32 list) = 0` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--1);
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--8)] THEN
  ASM_CASES_TAC `LENGTH(makes_xs:int32 list) = 0` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--1);
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--9)] THEN
  ASM_CASES_TAC `LENGTH(fields_xs:int32 list) = 0` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--1);
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--9)] THEN
  ASM_CASES_TAC `LENGTH(rows_xs:int32 list) = 0` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--1);
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--8)] THEN
  ASM_CASES_TAC `LENGTH(dest_xs:int32 list) = 0` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--1);
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--8)] THEN
  ASM_CASES_TAC `LENGTH(scratch_xs:int32 list) = 0` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--1);
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--8)] THEN
  ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--9) THEN
  ASM_CASES_TAC
   `32 < LENGTH(guards_xs:int32 list) \/ 32 < LENGTH(makes_xs:int32 list) \/
    LENGTH(dest_xs:int32 list) < LENGTH(makes_xs:int32 list)` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--2);
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--3)] THEN
  ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--9) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ORDINARY_ADAPTER_STACK_RESTORE] THEN
  SUBGOAL_THEN
   `(EventLoad(stackpointer:int64,8):uarch_event) =
    EventLoad(word_add (word_sub stackpointer (word 120)) (word 120),8)`
  ASSUME_TAC THENL [REWRITE_TAC[ORDINARY_ADAPTER_STACK_RESTORE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC);;


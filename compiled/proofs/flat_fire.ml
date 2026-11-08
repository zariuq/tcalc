(* Generic flat-rule firing on the x86-64 model of s2n-bignum. *)

needs "x86/proofs/base.ml";;

type_invention_error := true;;

let flat_fire_mc =
  define_assert_from_elf "flat_fire_mc" flat_fire_object
[
  0xf3; 0x0f; 0x1e; 0xfa;
  0x55; 0x53; 0x41; 0x54; 0x41; 0x55; 0x41; 0x56; 0x41; 0x57;
  0x4c; 0x8b; 0x64; 0x24; 0x38; 0x4c; 0x8b; 0x6c; 0x24; 0x40;
  0x45; 0x31; 0xd2; 0x45; 0x31; 0xdb; 0x48; 0x85; 0xc9; 0x74; 0x4d;
  0x42; 0x8b; 0x04; 0x92; 0x89; 0xc3; 0x81; 0xe3; 0xff; 0x00; 0x00; 0x00;
  0x89; 0xc5; 0xc1; 0xed; 0x08; 0x81; 0xe5; 0xff; 0x00; 0x00; 0x00;
  0x41; 0x89; 0xc6; 0x41; 0xc1; 0xee; 0x10;
  0x41; 0x81; 0xe6; 0xff; 0x00; 0x00; 0x00; 0xc1; 0xe8; 0x18;
  0x44; 0x8b; 0x3c; 0x9e; 0x41; 0x01; 0xef; 0x42; 0x8b; 0x1c; 0xb6;
  0x01; 0xc3; 0x42; 0x8b; 0x04; 0xbf; 0x3b; 0x04; 0x9f;
  0x0f; 0x95; 0xc0; 0x0f; 0xb6; 0xc0; 0x41; 0x09; 0xc3;
  0x49; 0xff; 0xc2; 0x49; 0x39; 0xca; 0x75; 0xb3;
  0x45; 0x85; 0xdb; 0x75; 0x51;
  0x45; 0x31; 0xd2; 0x4d; 0x85; 0xc9; 0x74; 0x29;
  0x43; 0x8b; 0x04; 0x90; 0x89; 0xc3; 0x81; 0xe3; 0xff; 0x00; 0x00; 0x00;
  0xc1; 0xe8; 0x08; 0x25; 0xff; 0x00; 0x00; 0x00;
  0x8b; 0x2c; 0x9e; 0x01; 0xc5; 0x8b; 0x04; 0xaf;
  0x43; 0x89; 0x44; 0x95; 0x00; 0x49; 0xff; 0xc2; 0x4d; 0x39; 0xca; 0x75; 0xd7;
  0x45; 0x31; 0xd2; 0x4d; 0x85; 0xc9; 0x74; 0x11;
  0x43; 0x8b; 0x44; 0x95; 0x00; 0x43; 0x89; 0x04; 0x94;
  0x49; 0xff; 0xc2; 0x4d; 0x39; 0xca; 0x75; 0xef;
  0xb8; 0x01; 0x00; 0x00; 0x00; 0xeb; 0x02; 0x31; 0xc0;
  0x41; 0x5f; 0x41; 0x5e; 0x41; 0x5d; 0x41; 0x5c; 0x5b; 0x5d; 0xc3
];;

let FLAT_FIRE_EXEC = X86_MK_EXEC_RULE flat_fire_mc;;

let flat_prefix = new_recursive_definition num_RECURSION
 `(flat_prefix 0 (l:int32 list) = []) /\
  (flat_prefix (SUC n) l =
     if l = [] then [] else CONS (HD l) (flat_prefix n (TL l)))`;;

let FLAT_PREFIX_SUC_EL = prove
 (`!l (i:num). i < LENGTH l
      ==> flat_prefix (i + 1) l = APPEND (flat_prefix i l) [EL i l]`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[GSYM ADD1] THEN ONCE_REWRITE_TAC[flat_prefix] THEN
    REWRITE_TAC[CONJUNCT1 flat_prefix; NOT_CONS_NIL; HD; TL; APPEND; EL];
    ALL_TAC] THEN
  REWRITE_TAC[LENGTH; GSYM ADD1] THEN ONCE_REWRITE_TAC[flat_prefix] THEN
  REWRITE_TAC[CONJUNCT1 flat_prefix; NOT_CONS_NIL; HD; TL; APPEND; EL] THEN
  DISCH_TAC THEN REWRITE_TAC[ADD1] THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (is_forall o concl)) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[LT_SUC]) THEN REWRITE_TAC[];
    REWRITE_TAC[]]);;

let FLAT_PREFIX_MAP = prove
 (`!f l n. flat_prefix n (MAP f l) = MAP f (flat_prefix n l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[flat_prefix; MAP; NOT_CONS_NIL; HD; TL] THEN
  ASM_REWRITE_TAC[]);;

let FLAT_PREFIX_ALL = prove
 (`!l. flat_prefix (LENGTH l) l = l`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; flat_prefix; NOT_CONS_NIL; HD; TL] THEN
  ASM_REWRITE_TAC[]);;

let flat_i = new_definition
 `flat_i (g:int32) = val (word_and g (word 255))`;;
let flat_j = new_definition
 `flat_j (g:int32) = val (word_and (word_ushr g 8) (word 255))`;;
let flat_i0 = new_definition
 `flat_i0 (g:int32) = val (word_and (word_ushr g 16) (word 255))`;;
let flat_j0 = new_definition
 `flat_j0 (g:int32) = val (word_ushr g 24)`;;

let flat_offset = new_definition
 `flat_offset (rs:int32 list) m =
    val (word_add (EL (flat_i m) rs) (word (flat_j m)):int32)`;;

let flat_offset0 = new_definition
 `flat_offset0 (rs:int32 list) g =
    val (word_add (EL (flat_i0 g) rs) (word (flat_j0 g)):int32)`;;

let flat_field = new_definition
 `flat_field (fs:int32 list) (rs:int32 list) m =
    EL (flat_offset rs m) fs`;;

let flat_guard_holds = new_definition
 `flat_guard_holds (fs:int32 list) (rs:int32 list) g <=>
    EL (flat_offset rs g) fs = EL (flat_offset0 rs g) fs`;;

let flat_guard_valid = new_definition
 `flat_guard_valid (fs:int32 list) (rs:int32 list) g <=>
    flat_i g < LENGTH rs /\ flat_i0 g < LENGTH rs /\
    flat_offset rs g < LENGTH fs /\ flat_offset0 rs g < LENGTH fs`;;

let flat_make_valid = new_definition
 `flat_make_valid (fs:int32 list) (rs:int32 list) m <=>
    flat_i m < LENGTH rs /\ flat_offset rs m < LENGTH fs`;;

let flat_guards_hold = new_definition
 `flat_guards_hold (fs:int32 list) (rs:int32 list) gs = ALL (flat_guard_holds fs rs) gs`;;

let flat_selected = new_definition
 `flat_selected (fs:int32 list) (rs:int32 list) ms = MAP (flat_field fs rs) ms`;;

let flat_valid = new_definition
 `flat_valid (fs:int32 list) (rs:int32 list) gs ms <=>
    ALL (flat_guard_valid fs rs) gs /\ ALL (flat_make_valid fs rs) ms`;;

let flat_saved = new_definition
 `flat_saved stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
              init_r14 init_r15 s <=>
    read RSP s = word_sub stackpointer (word 48) /\
    read (memory :> bytes64 stackpointer) s = returnaddress /\
    read (memory :> bytes64 (word_sub stackpointer (word 8))) s = init_rbp /\
    read (memory :> bytes64 (word_sub stackpointer (word 16))) s = init_rbx /\
    read (memory :> bytes64 (word_sub stackpointer (word 24))) s = init_r12 /\
    read (memory :> bytes64 (word_sub stackpointer (word 32))) s = init_r13 /\
    read (memory :> bytes64 (word_sub stackpointer (word 40))) s = init_r14 /\
    read (memory :> bytes64 (word_sub stackpointer (word 48))) s = init_r15`;;

let flat_mid = new_definition
 `flat_mid pc fields rows guards make dest scratch (fs:int32 list) (rs:int32 list) (gs:int32 list)
           (ms:int32 list) (ds:int32 list) (zs:int32 list)
           stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
           init_r14 init_r15 s <=>
    bytes_loaded s (word pc) flat_fire_mc /\
    read RIP s = word (pc + 0x70) /\
    read RDI s = fields /\ read RSI s = rows /\ read RDX s = guards /\
    read RCX s = word (LENGTH gs) /\ read R8 s = make /\
    read R9 s = word (LENGTH ms) /\ read R12 s = dest /\ read R13 s = scratch /\
    read R11 s = word (bitval (~flat_guards_hold fs rs gs)) /\
    wordlist_of_num (LENGTH fs) (read (memory :> bytes(fields,4 * LENGTH fs)) s) = fs /\
    wordlist_of_num (LENGTH rs) (read (memory :> bytes(rows,4 * LENGTH rs)) s) = rs /\
    wordlist_of_num (LENGTH gs) (read (memory :> bytes(guards,4 * LENGTH gs)) s) = gs /\
    flat_saved stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
               init_r14 init_r15 s`;;

let FLAT_GUARD_VALID_EL = prove
 (`!fs rs gs ms i. flat_valid fs rs gs ms /\ i < LENGTH gs
      ==> flat_guard_valid fs rs (EL i gs)`,
  REWRITE_TAC[flat_valid; GSYM ALL_EL] THEN MESON_TAC[]);;

let FLAT_MAKE_VALID_EL = prove
 (`!fs rs gs ms i. flat_valid fs rs gs ms /\ i < LENGTH ms
      ==> flat_make_valid fs rs (EL i ms)`,
  REWRITE_TAC[flat_valid; GSYM ALL_EL] THEN MESON_TAC[]);;

let FLAT_BAD_WORD = prove
 (`!P Q. word_or (word (bitval (~P)):int64) (word (bitval (~Q))) =
         word (bitval (~(P /\ Q)))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let FLAT_READ = prove
 (`!(fs:int32 list) (a:int64) (s:x86state) i.
      i < LENGTH fs /\ wordlist_from_memory(a,LENGTH fs) s = fs
      ==> read (memory :> bytes32 (word_add a (word (4 * i)))) s = EL i fs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `LENGTH(fs:int32 list)`; `i:num`; `s:x86state`]
                (INST_TYPE [`:4`,`:N`] EL_WORDLIST_FROM_MEMORY)) THEN
  ASM_REWRITE_TAC[BYTES32_WBYTES; DIMINDEX_4; EQ_SYM_EQ]);;

let WORDLIST_FROM_MEMORY_32 = prove
 (`!a n s. wordlist_from_memory(a,n) s : int32 list =
           wordlist_of_num n (read (memory :> bytes(a,4 * n)) s)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `n:num`; `s:x86state`]
                (INST_TYPE [`:4`,`:N`] WORDLIST_FROM_MEMORY)) THEN
  REWRITE_TAC[DIMINDEX_4]);;

let FLAT_STACK24 = prove
 (`!(sp:int64). word_sub sp (word 24) =
        word_sub (word_sub (word_sub sp (word 8)) (word 8)) (word 8)`,
  CONV_TAC WORD_RULE);;
let FLAT_STACK32 = prove
 (`!(sp:int64). word_sub sp (word 32) =
        word_sub (word_sub (word_sub (word_sub sp (word 8)) (word 8)) (word 8))
                 (word 8)`,
  CONV_TAC WORD_RULE);;
let FLAT_STACK40 = prove
 (`!(sp:int64). word_sub sp (word 40) =
        word_sub (word_sub (word_sub (word_sub (word_sub sp (word 8)) (word 8))
                  (word 8)) (word 8)) (word 8)`,
  CONV_TAC WORD_RULE);;
let FLAT_STACK48 = prove
 (`!(sp:int64). word_sub sp (word 48) =
        word_sub (word_sub (word_sub (word_sub (word_sub (word_sub (sp) (word 8)) (word 8)) (word 8)) (word 8)) (word 8)) (word 8)`,
  CONV_TAC WORD_RULE);;

let flat_guard_inv = new_definition
 `flat_guard_inv fields rows guards make dest scratch (fs:int32 list) (rs:int32 list) (gs:int32 list)
           (ms:int32 list) (ds:int32 list) (zs:int32 list)
                 stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
                 init_r14 init_r15 i s <=>
    read RDI s = fields /\ read RSI s = rows /\ read RDX s = guards /\
    read RCX s = word (LENGTH gs) /\ read R8 s = make /\
    read R9 s = word (LENGTH ms) /\ read R12 s = dest /\ read R13 s = scratch /\
    read R10 s = word i /\
    read R11 s = word (bitval (~flat_guards_hold fs rs (flat_prefix i gs))) /\
    wordlist_of_num (LENGTH fs) (read (memory :> bytes(fields,4 * LENGTH fs)) s) = fs /\
    wordlist_of_num (LENGTH rs) (read (memory :> bytes(rows,4 * LENGTH rs)) s) = rs /\
    wordlist_of_num (LENGTH gs) (read (memory :> bytes(guards,4 * LENGTH gs)) s) = gs /\
    flat_saved stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
               init_r14 init_r15 s`;;

let FLAT_FIRE_GUARDS_NONZERO = prove
 (`!fields rows guards make dest scratch (fs:int32 list) (rs:int32 list) (gs:int32 list)
           (ms:int32 list) (ds:int32 list) (zs:int32 list) pc stackpointer
    returnaddress init_rbp init_rbx init_r12 init_r13 init_r14 init_r15.
    flat_valid fs rs gs ms /\ 0 < LENGTH gs /\
    LENGTH ds = LENGTH ms /\ LENGTH zs = LENGTH ms /\
    LENGTH fs < 2 EXP 58 /\ LENGTH rs < 2 EXP 58 /\
    LENGTH gs < 2 EXP 58 /\ LENGTH ms < 2 EXP 58 /\
    ALLPAIRS nonoverlapping
      [(word pc,LENGTH flat_fire_mc); (word_sub stackpointer (word 48),48)]
      [(fields,4 * LENGTH fs); (rows,4 * LENGTH rs);
       (guards,4 * LENGTH gs); (make,4 * LENGTH ms);
       (dest,4 * LENGTH ms); (scratch,4 * LENGTH ms)] /\
    nonoverlapping (word pc,LENGTH flat_fire_mc)
      (word_sub stackpointer (word 48),48) /\
    ALL (nonoverlapping (scratch,4 * LENGTH ms))
      [(fields,4 * LENGTH fs); (rows,4 * LENGTH rs);
       (guards,4 * LENGTH gs); (make,4 * LENGTH ms); (dest,4 * LENGTH ms)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) flat_fire_mc /\
           read RIP s = word pc /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           read (memory :> bytes64 (word_add stackpointer (word 8))) s = dest /\
           read (memory :> bytes64 (word_add stackpointer (word 16))) s = scratch /\
           read RBP s = init_rbp /\ read RBX s = init_rbx /\
           read R12 s = init_r12 /\ read R13 s = init_r13 /\
           read R14 s = init_r14 /\ read R15 s = init_r15 /\
           C_ARGUMENTS [fields; rows; guards; word (LENGTH gs); make;
                        word (LENGTH ms)] s /\
           wordlist_from_memory(fields,LENGTH fs) s = fs /\
           wordlist_from_memory(rows,LENGTH rs) s = rs /\
           wordlist_from_memory(guards,LENGTH gs) s = gs /\
           wordlist_from_memory(make,LENGTH ms) s = ms /\
           wordlist_from_memory(dest,LENGTH ms) s = ds /\
           wordlist_from_memory(scratch,LENGTH ms) s = zs)
      (\s. flat_mid pc fields rows guards make dest scratch fs rs gs ms ds zs
                    stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
                    init_r14 init_r15 s)
      (MAYCHANGE [RIP; RSP; RAX; RBX; RBP; R10; R11; R12; R13; R14; R15] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(dest,4 * LENGTH ms);
                  memory :> bytes(scratch,4 * LENGTH ms);
                  memory :> bytes(word_sub stackpointer (word 48),48)])`,
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; ALLPAIRS; ALL;
              NONOVERLAPPING_CLAUSES; flat_mid; flat_saved; fst FLAT_FIRE_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  VAL_INT64_TAC `LENGTH(gs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(ms:int32 list)` THEN
  ENSURES_WHILE_PAUP_TAC `0` `LENGTH(gs:int32 list)` `pc + 0x23` `pc + 0x6e`
   `\i s. flat_guard_inv fields rows guards make dest scratch fs rs gs ms ds zs
                         stackpointer returnaddress init_rbp init_rbx init_r12
                         init_r13 init_r14 init_r15 i s /\
          (read ZF s <=> i = LENGTH gs)` THEN
  REPEAT CONJ_TAC THEN PRINT_GOAL_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[flat_guard_inv; flat_saved; flat_prefix; ALL;
                FLAT_STACK24; FLAT_STACK32; FLAT_STACK40; FLAT_STACK48;
                WORDLIST_FROM_MEMORY_32] THEN
    X86_SIM_TAC FLAT_FIRE_EXEC (1--13) THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`];
    REMARK_TAC "guard body: begin" THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[flat_guard_inv; flat_saved] THEN
    REMARK_TAC "guard body: simulate" THEN
    X86_SIM_TAC ~preprocess_tac:
     (REMARK_TAC "guard body: preprocess" THEN
      SUBGOAL_THEN `flat_guard_valid fs rs (EL i gs)` ASSUME_TAC THENL
       [MATCH_MP_TAC FLAT_GUARD_VALID_EL THEN EXISTS_TAC `ms:int32 list` THEN
        ASM_REWRITE_TAC[]; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[flat_guard_valid]) THEN
      SUBGOAL_THEN `i + 1 < 2 EXP 64` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      REMARK_TAC "guard body: valid" THEN
      SUBGOAL_THEN
       `read (memory :> bytes32 (word_add guards (word (4 * i)))) (s0:x86state) =
          EL i (gs:int32 list) /\
        read (memory :> bytes32 (word_add rows (word (4 * flat_i (EL i gs))))) s0 =
          EL (flat_i (EL i gs)) (rs:int32 list) /\
        read (memory :> bytes32 (word_add rows (word (4 * flat_i0 (EL i gs))))) s0 =
          EL (flat_i0 (EL i gs)) rs /\
        read (memory :> bytes32 (word_add fields
          (word (4 * flat_offset rs (EL i gs))))) s0 =
          EL (flat_offset rs (EL i gs)) (fs:int32 list) /\
        read (memory :> bytes32 (word_add fields
          (word (4 * flat_offset0 rs (EL i gs))))) s0 =
          EL (flat_offset0 rs (EL i gs)) fs`
      MP_TAC THENL
       [REPEAT CONJ_TAC THEN
        ASM_MESON_TAC[FLAT_READ; flat_guard_valid; flat_offset; flat_offset0;
                      WORDLIST_FROM_MEMORY_32];
        DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[flat_offset; flat_offset0]) THEN
      ASM_CASES_TAC `flat_guard_holds fs rs (EL i gs)` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[flat_guard_holds; flat_offset; flat_offset0]))
    FLAT_FIRE_EXEC (1--19) THEN PRINT_GOAL_TAC THEN
    ASM_SIMP_TAC[flat_i; flat_j; flat_i0; flat_j0; flat_offset; flat_offset0;
                 flat_guard_holds;
                 FLAT_PREFIX_SUC_EL; flat_guards_hold; ALL_APPEND; ALL;
                 FLAT_BAD_WORD; WORD_ADD; VAL_WORD_ADD; VAL_WORD;
                 DIMINDEX_32; DIMINDEX_64; MOD_LT; MOD_MOD_REFL];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[flat_guard_inv; flat_saved; WORDLIST_FROM_MEMORY_32] THEN
    X86_SIM_TAC FLAT_FIRE_EXEC [1];
    ASM_REWRITE_TAC[flat_guard_inv; flat_mid; flat_saved; FLAT_PREFIX_ALL;
                    WORDLIST_FROM_MEMORY_32] THEN
    X86_SIM_TAC FLAT_FIRE_EXEC [1] THEN
    ASM_REWRITE_TAC[flat_mid; flat_saved]] THEN PRINT_GOAL_TAC);;


let FLAT_FIRE_GUARDS_ZERO = prove
 (`!fields rows guards make dest scratch (fs:int32 list) (rs:int32 list)
    (gs:int32 list) (ms:int32 list) (ds:int32 list) (zs:int32 list)
    pc stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
    init_r15.
    flat_valid fs rs gs ms /\ gs = [] /\
    LENGTH ds = LENGTH ms /\ LENGTH zs = LENGTH ms /\
    LENGTH fs < 2 EXP 58 /\ LENGTH rs < 2 EXP 58 /\
    LENGTH gs < 2 EXP 58 /\ LENGTH ms < 2 EXP 58 /\
    ALLPAIRS nonoverlapping
      [(word pc,LENGTH flat_fire_mc); (word_sub stackpointer (word 48),48)]
      [(fields,4 * LENGTH fs); (rows,4 * LENGTH rs);
       (guards,4 * LENGTH gs); (make,4 * LENGTH ms);
       (dest,4 * LENGTH ms); (scratch,4 * LENGTH ms)] /\
    nonoverlapping (word pc,LENGTH flat_fire_mc)
      (word_sub stackpointer (word 48),48) /\
    ALL (nonoverlapping (scratch,4 * LENGTH ms))
      [(fields,4 * LENGTH fs); (rows,4 * LENGTH rs);
       (guards,4 * LENGTH gs); (make,4 * LENGTH ms); (dest,4 * LENGTH ms)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) flat_fire_mc /\
           read RIP s = word pc /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           read (memory :> bytes64 (word_add stackpointer (word 8))) s = dest /\
           read (memory :> bytes64 (word_add stackpointer (word 16))) s = scratch /\
           read RBP s = init_rbp /\ read RBX s = init_rbx /\
           read R12 s = init_r12 /\ read R13 s = init_r13 /\
           read R14 s = init_r14 /\ read R15 s = init_r15 /\
           C_ARGUMENTS [fields; rows; guards; word (LENGTH gs); make;
                        word (LENGTH ms)] s /\
           wordlist_from_memory(fields,LENGTH fs) s = fs /\
           wordlist_from_memory(rows,LENGTH rs) s = rs /\
           wordlist_from_memory(guards,LENGTH gs) s = gs /\
           wordlist_from_memory(make,LENGTH ms) s = ms /\
           wordlist_from_memory(dest,LENGTH ms) s = ds /\
           wordlist_from_memory(scratch,LENGTH ms) s = zs)
      (\s. flat_mid pc fields rows guards make dest scratch fs rs gs ms ds zs
                    stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
                    init_r14 init_r15 s)
      (MAYCHANGE [RIP; RSP; RAX; RBX; RBP; R10; R11; R12; R13; R14; R15] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(dest,4 * LENGTH ms);
                  memory :> bytes(scratch,4 * LENGTH ms);
                  memory :> bytes(word_sub stackpointer (word 48),48)])`,
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; ALLPAIRS; ALL;
              NONOVERLAPPING_CLAUSES; flat_mid; flat_saved; fst FLAT_FIRE_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  VAL_INT64_TAC `LENGTH(gs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(ms:int32 list)` THEN
  REWRITE_TAC[WORDLIST_FROM_MEMORY_32; FLAT_STACK24; FLAT_STACK32;
              FLAT_STACK40; FLAT_STACK48; flat_guards_hold; ALL;
              wordlist_of_num] THEN
  X86_SIM_TAC FLAT_FIRE_EXEC (1--13));;

(* ========================================================================= *)
(* Controls for callbacks.ml: a mutated image must not meet add64's          *)
(* contract.                                                                 *)
(*                                                                           *)
(* add64_mut_mc is add64's 34 bytes with the ALU opcode byte (offset 19)     *)
(* 0x01 (ADD) replaced by 0x29 (SUB); it is sub64's image.                   *)
(*   1. add64's own proof script, run on the mutant, fails, at the result.   *)
(*   2. ADD64_MUT_CONTRACT_FALSE: the statement of ADD64_CONTRACT with the   *)
(*      mutant's bytes is false. Witness: in[0] = in[1] = 0xF0F0F0F0F0F0F0F0 *)
(*      and a byte 0xF0 (LOCK, which the decoder rejects) at the return      *)
(*      address, so a run stops at its first return; there SUB64_CORE gives  *)
(*      out = 0, and the contract would give (x + y) mod 2^64 = 0xE1..E0.    *)
(* ========================================================================= *)

needs "native/callbacks/callbacks.ml";;

let add64_mut_mc =
  let lit = List.mapi (fun i b -> if i = 19 then 0x29 else b) (assoc "add64" !cb_literals) in
  new_definition (mk_eq (mk_var ("add64_mut_mc", `:byte list`), cb_byte_list lit));;

let ADD64_MUT_EXEC = X86_MK_EXEC_RULE add64_mut_mc;;
cb_print_decodes "add64_mut" ADD64_MUT_EXEC;;

let ADD64_MUT_IS_SUB64 = prove
 (`add64_mut_mc = sub64_mc`,
  REWRITE_TAC[add64_mut_mc; sub64_mc]);;

let cb_control label f =
  let refused = (try ignore(f()); false with Failure _ -> true) in
  Printf.printf "CONTROL %s: %s\n%!" label (if refused then "refused" else "ACCEPTED (wrong)");
  refused;;

(* ------------------------------------------------------------------------- *)
(* 1. add64's proof script on the mutant.                                    *)
(* ------------------------------------------------------------------------- *)

let cb_add64_on_mut_goal = cb_core_goal `add64_mut_mc` `word_add:int64->int64->int64`;;

cb_control "add64's proof on add64_mut_mc"
  (fun () -> prove(cb_add64_on_mut_goal, CB_CORE_TAC ADD64_MUT_EXEC));;

(* What is left after the run: the result clause. *)
let () =
  let _,gl,_ = CB_CORE_STEPS_TAC ADD64_MUT_EXEC ([],cb_add64_on_mut_goal) in
  List.iter (fun (_,w) -> Printf.printf "CONTROL add64 on add64_mut_mc leaves: %s\n%!"
                            (string_of_term w)) gl;;

(* ------------------------------------------------------------------------- *)
(* 2. A stuck state, and two eventualities that must meet in it.            *)
(* ------------------------------------------------------------------------- *)

let CB_DECODE_F0 = prove
 (`!l. decode (CONS (word 0xf0) l) = NONE`,
  GEN_TAC THEN REWRITE_TAC[decode; read_prefixes] THEN
  CONV_TAC(ONCE_DEPTH_CONV BITMATCH_MEMO_CONV) THEN REWRITE_TAC[obind]);;

let CB_DECODE_NIL = prove
 (`decode [] = NONE`,
  REWRITE_TAC[decode; read_prefixes; obind]);;

let CB_READ_BYTES8 = prove
 (`!(a:int64) s. read (memory :> bytes8 a) s = read memory s a`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES8_ELEMENT; READ_ELEMENT]);;

(* A state whose next byte is 0xF0 has no successor. *)
let CB_STUCK = prove
 (`!s. read (memory :> bytes8 (read RIP s)) s = word 0xf0 ==> !s'. ~(x86 s s')`,
  REWRITE_TAC[CB_READ_BYTES8; x86; x86_decode] THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `len:num` (X_CHOOSE_THEN `instr:instruction`
    (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:byte list` (CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC))) THEN
  STRUCT_CASES_TAC(ISPEC `l:byte list` list_CASES) THEN
  REWRITE_TAC[CB_DECODE_NIL; distinctness "option"] THEN
  REWRITE_TAC[bytes_loaded; LENGTH; READ_COMPONENT_COMPOSE; bytelist_clauses; CONS_11] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM o CONJUNCT1) THEN
  FIRST_X_ASSUM(MP_TAC o check (can (find_term ((=) `decode`)) o concl)) THEN
  REWRITE_TAC[CB_DECODE_F0; distinctness "option"]);;

(* Two eventualities whose goal states are stuck meet in one state. *)
let CB_EVENTUALLY_JOIN = prove
 (`!(step:A->A->bool) G P Q.
     (!s. G s ==> !s'. ~step s s')
     ==> !s. eventually step (\s. G s /\ P s) s
             ==> eventually step (\s. G s /\ Q s) s
             ==> ?s'. G s' /\ P s' /\ Q s'`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC eventually_INDUCT THEN CONJ_TAC THEN X_GEN_TAC `s:A` THEN
  BETA_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[eventually_CASES] THEN
  BETA_TAC THEN ASM_MESON_TAC[]);;

(* Hence two ensures from one state, whose goals (with their frames) imply a *)
(* stuck guard G, cannot have goals that exclude each other.                *)
let CB_ENSURES_DISJOINT = prove
 (`!(step:A->A->bool) P1 Q1 C1 P2 Q2 C2 G s0.
     (!s. G s ==> !s'. ~step s s') /\
     P1 s0 /\ ensures step P1 Q1 C1 /\
     P2 s0 /\ ensures step P2 Q2 C2 /\
     (!s. Q1 s /\ C1 s0 s ==> G s) /\
     (!s. Q2 s /\ C2 s0 s ==> G s) /\
     (!s. Q1 s /\ C1 s0 s /\ Q2 s /\ C2 s0 s ==> F)
     ==> F`,
  REWRITE_TAC[ensures] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`step:A->A->bool`; `G:A->bool`;
                 `\s:A. Q1 s /\ C1 (s0:A) s`; `\s:A. Q2 s /\ C2 (s0:A) s`]
         CB_EVENTUALLY_JOIN) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s0:A`) THEN
  MATCH_MP_TAC(TAUT `a /\ b /\ ~c ==> (a ==> b ==> c) ==> F`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] EVENTUALLY_MONO) THEN
    EXISTS_TAC `\s:A. Q1 s /\ C1 (s0:A) s` THEN BETA_TAC THEN ASM_MESON_TAC[];
    MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] EVENTUALLY_MONO) THEN
    EXISTS_TAC `\s:A. Q2 s /\ C2 (s0:A) s` THEN BETA_TAC THEN ASM_MESON_TAC[];
    BETA_TAC THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 3. The witness. Code at 0x10000, in at 0x20000, out at 0x30000, the       *)
(* return word at 0x40000; every other byte is 0xF0 except the top three     *)
(* bytes of the return word, which are 0. So the return address is           *)
(* 0xF0F0F0F0F0 (canonical), the byte there is 0xF0, and in[0] = in[1] =     *)
(* 0xF0F0F0F0F0F0F0F0.                                                       *)
(* ------------------------------------------------------------------------- *)

let cb_wmem = new_definition
 `cb_wmem (a:int64) =
    if 65536 <= val a /\ val a < 65570 then EL (val a - 65536) add64_mut_mc
    else if 262149 <= val a /\ val a < 262152 then word 0
    else word 0xf0`;;

let cb_wstate = new_definition
 `cb_wstate =
    write memory cb_wmem
     (write RIP (word 65536)
       (write RSP (word 262144)
         (write RDI (word 131072)
           (write RSI (word 196608)
             (write events ([]:uarch_event list) (ARB:x86state))))))`;;

let cb_wvals =
  [`65536`; `word 131072:int64`; `word 196608:int64`;
   `word 17361641481138401520:int64`; `word 17361641481138401520:int64`;
   `word 262144:int64`; `word 1034834473200:int64`; `[]:uarch_event list`];;

let CB_W_COMPONENTS = prove
 (`read memory cb_wstate = cb_wmem /\
   read RIP cb_wstate = word 65536 /\
   read RSP cb_wstate = word 262144 /\
   read RDI cb_wstate = word 131072 /\
   read RSI cb_wstate = word 196608 /\
   read events cb_wstate = []`,
  REWRITE_TAC[cb_wstate] THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN REWRITE_TAC[]);;

let CB_W_BYTE = prove
 (`!a. read (memory :> bytes8 a) cb_wstate = cb_wmem a`,
  REWRITE_TAC[CB_READ_BYTES8; CB_W_COMPONENTS]);;

(* cb_wmem (word n), n a numeral, to its byte. *)
let CB_WMEM_CONV =
  REWR_CONV cb_wmem THENC
  REWRITE_CONV[VAL_WORD; DIMINDEX_64] THENC NUM_REDUCE_CONV THENC
  REWRITE_CONV[add64_mut_mc] THENC TRY_CONV(ONCE_DEPTH_CONV EL_CONV);;

let CB_BYTES_LOADED_CONS = prove
 (`!s pc h t. bytes_loaded s pc (CONS h t) <=>
              read (memory :> bytes8 pc) s = h /\ bytes_loaded s (word_add pc (word 1)) t`,
  REWRITE_TAC[bytes_loaded; LENGTH; READ_COMPONENT_COMPOSE; bytelist_clauses; CONS_11;
              BYTES8_ELEMENT; READ_ELEMENT]);;

let CB_W_LOADED = prove
 (`bytes_loaded cb_wstate (word 65536) add64_mut_mc`,
  REWRITE_TAC[add64_mut_mc; CB_BYTES_LOADED_CONS; bytes_loaded_nil] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[CB_W_BYTE] THEN
  CONV_TAC(ONCE_DEPTH_CONV CB_WMEM_CONV) THEN REWRITE_TAC[]);;

let CB_READ_BYTES64 = prove
 (`!(a:int64) s. read (memory :> bytes64 a) s = word(read (memory :> bytes(a,8)) s)`,
  REWRITE_TAC[bytes64; READ_COMPONENT_COMPOSE; asword; through; read]);;

let CB_W_WORDS = prove
 (`read (memory :> bytes64 (word 262144)) cb_wstate = word 1034834473200 /\
   read (memory :> bytes64 (word 131072)) cb_wstate = word 17361641481138401520 /\
   read (memory :> bytes64 (word_add (word 131072) (word 8))) cb_wstate =
     word 17361641481138401520`,
  REWRITE_TAC[CB_READ_BYTES64] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV BYTES_EXPAND_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[CB_W_BYTE] THEN
  CONV_TAC(ONCE_DEPTH_CONV CB_WMEM_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

(* The witness's places meet the entry facts. *)
let CB_W_SEP = prove
 (`nonoverlapping (word 196608:int64,8) (word 65536,34) /\
   nonoverlapping (word 196608:int64,8) (word 262144,8) /\
   nonoverlapping (word 196608:int64,8) (word 131072,16)`,
  REWRITE_TAC[nonoverlapping; VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC NONOVERLAPPING_MODULO_SIMPLE THEN
  CONV_TAC NUM_REDUCE_CONV);;

let CB_AREA_LOW = prove
 (`!a n. a + n <= 2 EXP 47 ==> cb_area (word a) n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[cb_area; cb_canonical] THEN
  REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `!i. i <= n ==> (a + i) MOD 2 EXP 64 = a + i` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `a + n <= 2 EXP 47` THEN UNDISCH_TAC `i <= n` THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[ADD_CLAUSES; LE_0] THEN
    DISCH_THEN SUBST1_TAC THEN UNDISCH_TAC `a + n <= 2 EXP 47` THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    REPEAT STRIP_TAC THEN DISJ1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    UNDISCH_TAC `a + n <= 2 EXP 47` THEN UNDISCH_TAC `i < n` THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]);;

let CB_W_ENTRY = prove
 (`cb_entry 65536 (word 131072) (word 196608) (word 262144) (word 1034834473200)`,
  REWRITE_TAC[cb_entry; CB_W_SEP] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64; DIVIDES_MOD] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64; DIVIDES_MOD] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64; DIVIDES_MOD] THEN CONV_TAC NUM_REDUCE_CONV;
    MATCH_MP_TAC CB_AREA_LOW THEN CONV_TAC NUM_REDUCE_CONV;
    MATCH_MP_TAC CB_AREA_LOW THEN CONV_TAC NUM_REDUCE_CONV;
    MATCH_MP_TAC CB_AREA_LOW THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[cb_canonical; VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV;
    CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
    REWRITE_TAC[cb_canonical; VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV]);;

(* The frame keeps the byte at the return address: that byte is apart from  *)
(* the output word, and every other component the frame names is a          *)
(* register, a flag or the event log.                                        *)
let CB_READ_WRITE_ORTH = prove
 (`!(c:(A,B)component) (d:(A,C)component) y s.
     orthogonal_components c d ==> read c (write d y s) = read c s`,
  SIMP_TAC[orthogonal_components]);;

let CB_W_ORTH = prove
 (`orthogonal_components (memory :> bytes8 (word 1034834473200))
                         (memory :> bytes64 (word 196608))`,
  SUBGOAL_THEN `nonoverlapping (word 1034834473200:int64,1) (word 196608,8)` MP_TAC THENL
   [REWRITE_TAC[nonoverlapping; VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC NONOVERLAPPING_MODULO_SIMPLE THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_TAC THEN ORTHOGONAL_COMPONENTS_TAC]);;

let CB_W_FRAME = prove
 (`!s s'. (MAYCHANGE [RIP; RSP; RAX; RDX] ,, MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes64 (word 196608)]) s s'
          ==> read (memory :> bytes8 (word 1034834473200)) s' =
              read (memory :> bytes8 (word 1034834473200)) s`,
  REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN REWRITE_TAC[GSYM SEQ_ASSOC] THEN
  PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[ASSIGNS_THM] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[MATCH_MP CB_READ_WRITE_ORTH CB_W_ORTH] THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV COMPONENT_READ_OVER_WRITE_ORTHOGONAL_CONV)) THEN
  REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* 4. add64's contract, stated for the mutant's bytes, is false.             *)
(* ------------------------------------------------------------------------- *)

let cb_wguard =
 `\s. read RIP s = word 1034834473200 /\
      read (memory :> bytes8 (word 1034834473200)) s = word 240`;;

let ADD64_MUT_CONTRACT_FALSE =
  let tm = subst [`add64_mut_mc`, `add64_mc`] (concl ADD64_CONTRACT) in
  let th1 = MP (SPECL cb_wvals (ASSUME tm)) CB_W_ENTRY in
  let th2 = PURE_REWRITE_RULE[GSYM ADD64_MUT_IS_SUB64] (MP (SPECL cb_wvals SUB64_CORE) CB_W_SEP) in
  let args th = snd(strip_comb(concl th)) in
  let p1,q1,c1 = (match args th1 with [_;p;q;c] -> p,q,c | _ -> failwith "contract")
  and p2,q2,c2 = (match args th2 with [_;p;q;c] -> p,q,c | _ -> failwith "core") in
  let inst = ISPECL [`x86`; p1; q1; c1; p2; q2; c2; cb_wguard; `cb_wstate`]
                    CB_ENSURES_DISJOINT in
  let pre_tac = BETA_TAC THEN
    REWRITE_TAC[C_ARGUMENTS; CB_W_LOADED; CB_W_COMPONENTS; CB_W_WORDS] in
  let guard_tac = GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP CB_W_FRAME) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CB_W_BYTE] THEN
    CONV_TAC(ONCE_DEPTH_CONV CB_WMEM_CONV) THEN REWRITE_TAC[] in
  let ths = match conjuncts(lhand(concl inst)) with
    | [c_stuck; c_p1; _; c_p2; _; c_g1; c_g2; c_contra] ->
       [prove(c_stuck, GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN
                       MATCH_MP_TAC CB_STUCK THEN ASM_REWRITE_TAC[]);
        prove(c_p1, pre_tac); th1;
        prove(c_p2, pre_tac); th2;
        prove(c_g1, guard_tac); prove(c_g2, guard_tac);
        prove(c_contra, GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN
          FIRST_X_ASSUM(MP_TAC o check (can (find_term ((=) `MOD`)) o concl)) THEN
          ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
          CONV_TAC NUM_REDUCE_CONV)]
    | _ -> failwith "ADD64_MUT_CONTRACT_FALSE: premises" in
  NOT_INTRO(DISCH tm (MP inst (end_itlist CONJ ths)));;

Printf.printf "CONTROL add64's contract on add64_mut_mc: %s\n%!"
  (if hyp ADD64_MUT_CONTRACT_FALSE = [] &&
      concl ADD64_MUT_CONTRACT_FALSE =
        mk_neg(subst [`add64_mut_mc`, `add64_mc`] (concl ADD64_CONTRACT))
   then "refuted (ADD64_MUT_CONTRACT_FALSE)" else "NOT REFUTED");;

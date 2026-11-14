(* ========================================================================= *)
(* Symbolic execution that keeps the whole memory.                           *)
(*                                                                           *)
(* The native realization of t-ISA is related to the semantics by equality   *)
(* of the whole memory: read memory s = tmem t. s2n-bignum's stepping keeps  *)
(* facts about components, so this step additionally (1) rewrites values     *)
(* loaded from the old state's memory into reads of the memory function,     *)
(* and (2) after a store, derives read memory s' = write ... (read memory s) *)
(* from the step's explicit state equation, before old-state facts go.       *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "tisa/hol/tisa_p1_memory.ml";;

(* A read of a memory function. It is read c m, under another name, because
   s2n-bignum's old-state cleanup treats every read c X as a read of a state X
   and would discard facts about loaded values. *)
let tisa_mread = new_definition
 `tisa_mread (c:((int64->byte),A)component) (m:int64->byte) = read c m`;;

let TISA_READ_MEMORY_COMPOSE = prove
 (`!s:x86state m. read memory s = m ==> !c:((int64->byte),A)component.
       read (memory :> c) s = tisa_mread c m`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE; tisa_mread]);;

let tisa_rmem = `read (memory:(x86state,int64->byte)component)`;;

let rec tisa_base_state t =
  match t with
  | Comb(Comb(Comb(Const("write",_),_),_),s) -> tisa_base_state s
  | _ -> t;;

let tisa_writes_memory t =
  can (find_term (fun u ->
         match u with
         | Comb(Comb(Comb(Const("write",_),Comb(Comb(Const(":>",_),Const("memory",_)),_)),_),_) -> true
         | _ -> false)) t;;

(* memth: |- read memory s = m for the state s before the step, if known;
   olds: the facts read c s = x about that state, captured before the step. *)
let TISA_STRIP_COMPONENT_TAC memth olds th =
  match memth with
  | None -> STRIP_TAC
  | Some mth ->
      let s = rand(lhs(concl mth)) in
      let ex = lhs(concl th) in
      let compose = MP (ISPECL [s; rhs(concl mth)] TISA_READ_MEMORY_COMPOSE) mth in
      let fix_new = CONV_TAC(LAND_CONV(TOP_DEPTH_CONV(GEN_REWRITE_CONV I [compose]))) in
      let mem_new =
        if not (tisa_writes_memory ex) then ALL_TAC else
        let eq = (REWRITE_CONV[WRITE_COMPONENT_COMPOSE] THENC
                  TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) (mk_comb(tisa_rmem,ex)) in
        let eq1 = TRANS (SYM(AP_TERM tisa_rmem th)) eq in
        let eq2 = GEN_REWRITE_RULE (RAND_CONV o TOP_DEPTH_CONV) [compose] eq1 in
        let eq3 = GEN_REWRITE_RULE (RAND_CONV o TOP_DEPTH_CONV) (mth::olds) eq2 in
        let eq4 = GEN_REWRITE_RULE (RAND_CONV o TOP_DEPTH_CONV) [WORD_ADD_0] eq3 in
        ASSUME_TAC eq4 in
      fix_new THEN STRIP_TAC THEN mem_new;;

let TISA_STEP_TAC execth sname (asl,w) =
  let s = rand w in
  let facts = map snd asl in
  let memth =
    try Some(find (fun f -> let c = concl f in is_eq c && lhs c = mk_comb(tisa_rmem,s)) facts)
    with Failure _ -> None in
  let olds = filter (fun f ->
      let c = concl f in
      is_eq c && is_comb(lhs c) && rand(lhs c) = s &&
      (match rator(lhs c) with Comb(Const("read",_),_) -> true | _ -> false)) facts in
  (X86_STEP_TAC execth [] sname None (TISA_STRIP_COMPONENT_TAC memth olds) THEN
   DISCARD_OLDSTATE_TAC sname) (asl,w);;

let TISA_STEPS_TAC execth snums =
  MAP_EVERY (fun n -> TISA_STEP_TAC execth ("s"^string_of_int n)) snums;;

(* ------------------------------------------------------------------------- *)
(* Reads of the memory function in the forms the semantics uses.            *)
(* ------------------------------------------------------------------------- *)

let TISA_MREAD_BYTES64 = prove
 (`!(a:int64) m. tisa_mread (bytes64 a) m = word(read (bytes(a,8)) m)`,
  REWRITE_TAC[tisa_mread; bytes64; asword; through; read; READ_COMPONENT_COMPOSE]);;

let TISA_MREAD_BYTES32 = prove
 (`!(a:int64) m. tisa_mread (bytes32 a) m = word(read (bytes(a,4)) m)`,
  REWRITE_TAC[tisa_mread; bytes32; asword; through; read; READ_COMPONENT_COMPOSE]);;

let TISA_MREAD_BYTES8 = prove
 (`!(a:int64) m. tisa_mread (bytes8 a) m = word(read (bytes(a,1)) m)`,
  REWRITE_TAC[tisa_mread; bytes8; asword; through; read; READ_COMPONENT_COMPOSE]);;

(* ------------------------------------------------------------------------- *)
(* Running a template to its end: step, and at a conditional jump split on   *)
(* its condition, until rip is at one of the stop offsets from pc.           *)
(* ------------------------------------------------------------------------- *)

let tisa_rip_fact s f =
  let c = concl f in
  is_eq c && (match lhs c with
              | Comb(Comb(Const("read",_),Const("RIP",_)),s') -> s' = s
              | _ -> false);;

let tisa_rip_offset pc tm =
  (* word(pc + k) -> Some k; word pc -> Some 0 *)
  match tm with
  | Comb(Const("word",_),Comb(Comb(Const("+",_),p),k)) when p = pc -> Some(dest_small_numeral k)
  | Comb(Const("word",_),p) when p = pc -> Some 0
  | _ -> None;;

let rec TISA_RUN_TAC execth pc stops n (asl,w) =
  let s = rand w in
  let rip = try snd(find (tisa_rip_fact s o snd) asl) with Failure _ -> failwith "TISA_RUN_TAC: no rip" in
  let v = rhs(concl rip) in
  if is_cond v then
    let c,_ = dest_cond v in
    let resolve b (asl,w) =
      let cth = ASSUME (if b then c else mk_neg c) in
      (FIRST_X_ASSUM(fun f -> if tisa_rip_fact s f then ASSUME_TAC(REWRITE_RULE[cth] f) else failwith "") THEN
       TISA_RUN_TAC execth pc stops n) (asl,w) in
    (ASM_CASES_TAC c THENL [resolve true; resolve false]) (asl,w)
  else
    match tisa_rip_offset pc v with
    | Some k when mem k stops -> ALL_TAC (asl,w)
    | _ -> (TISA_STEP_TAC execth ("s"^string_of_int n) THEN
            TISA_RUN_TAC execth pc stops (n + 1)) (asl,w);;

(* Native stores of a word write the same bytes as the semantics' store. *)
let TISA_WRITE_BYTES64 = prove
 (`!(a:int64) (w:int64) m. write (bytes64 a) w m = write (bytes(a,8)) (val w) m`,
  REWRITE_TAC[bytes64; asword; through; write; WRITE_COMPONENT_COMPOSE; read]);;

let TISA_WRITE_BYTES32 = prove
 (`!(a:int64) (w:int32) m. write (bytes32 a) w m = write (bytes(a,4)) (val w) m`,
  REWRITE_TAC[bytes32; asword; through; write; WRITE_COMPONENT_COMPOSE; read]);;

let TISA_WRITE_BYTES8 = prove
 (`!(a:int64) (w:byte) m. write (bytes8 a) w m = write (bytes(a,1)) (val w) m`,
  REWRITE_TAC[bytes8; asword; through; write; WRITE_COMPONENT_COMPOSE; read]);;

(* Effective addresses: the semantics computes them exactly, as integers. *)
let TISA_IWORD_VAL = prove
 (`!x:int64. iword(&(val x)) = x`,
  REWRITE_TAC[GSYM WORD_IWORD; WORD_VAL]);;

let TISA_IWORD_VAL_ADD = prove
 (`!(x:int64) n. iword(&(val x) + &n) = word_add x (word n)`,
  REWRITE_TAC[INT_OF_NUM_ADD; GSYM WORD_IWORD; WORD_ADD; WORD_VAL]);;

(* A negative offset: the x86 adds its two's complement (the decoder
   sign-extends the displacement). *)
let TISA_IWORD_VAL_NEG = prove
 (`!(x:int64) n. n <= 2 EXP 64 ==> iword(&(val x) + -- &n) = word_add x (word(2 EXP 64 - n))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM TISA_IWORD_VAL_ADD; IWORD_EQ; DIMINDEX_64] THEN
  ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN
  REWRITE_TAC[int_congruent] THEN EXISTS_TAC `-- &1:int` THEN
  REWRITE_TAC[GSYM INT_OF_NUM_POW] THEN INT_ARITH_TAC);;

let TISA_IWORD_VAL_NEG_CONV tm =
  match tm with
  | Comb(Const("iword",_),Comb(Comb(Const("int_add",_),Comb(Const("int_of_num",_),Comb(Const("val",_),x))),
                               Comb(Const("int_neg",_),Comb(Const("int_of_num",_),n)))) when is_numeral n ->
      let th = MP (ISPECL [x; n] TISA_IWORD_VAL_NEG)
                  (EQT_ELIM (NUM_REDUCE_CONV (mk_binop `(<=):num->num->bool` n `2 EXP 64`))) in
      CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV NUM_REDUCE_CONV))) th
  | _ -> failwith "TISA_IWORD_VAL_NEG_CONV";;

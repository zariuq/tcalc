(* ========================================================================= *)
(* The five native binary callbacks add64, sub64, and64, or64, xor64,        *)
(* proved against s2n-bignum's x86 model from their exact bytes.             *)
(*                                                                           *)
(* Each image is 34 bytes, bool fn(const uint64_t *in, uint64_t *out) under  *)
(* the System V ABI:                                                         *)
(*   ENDBR64; MOV RAX,[RDI+0]; MOV RDX,[RDI+8]; op RAX,RDX; MOV [RSI+0],RAX;  *)
(*   MOV EAX,1; RET                                                          *)
(* with op ADD, SUB, AND, OR or XOR. Every theorem runs from the entry, RIP  *)
(* at the ENDBR64 landing pad and RSP at the caller's return word, to the    *)
(* return; the model executes ENDBR64 itself (as a no-op).                   *)
(*                                                                           *)
(*   NAME_CORE      the run in the model's terms: out = op x y, RAX = 1,     *)
(*                  return to the caller with RSP + 8, the inputs kept, the  *)
(*                  exact trace of memory accesses, and the frame; only the  *)
(*                  separation the run needs (out apart from the code, the   *)
(*                  return word and the input words).                        *)
(*   NAME_CONTRACT  the shared contract (CONTRACT.txt): its entry facts      *)
(*                  (cb_entry), the result in the contract's own arithmetic, *)
(*                  and every memory access inside the input words, the      *)
(*                  return word (reads) and the output word (the write).     *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(* ------------------------------------------------------------------------- *)
(* The bytes. Each image record NAME.hol (also the census gate's input), the *)
(* artifact NAME.bin and the literal list below must agree byte for byte.    *)
(* ------------------------------------------------------------------------- *)

let cb_home = tcalc_path "native/callbacks";;
let cb_artifacts = tcalc_path "native/callbacks/binary-callbacks";;

let cb_records = ref ([] : (string * string) list);;
let cb_image name hex = cb_records := (name, String.lowercase_ascii hex) :: !cb_records;;

loadt "native/callbacks/add64.hol";;
loadt "native/callbacks/sub64.hol";;
loadt "native/callbacks/and64.hol";;
loadt "native/callbacks/or64.hol";;
loadt "native/callbacks/xor64.hol";;

let cb_hex_bytes hex =
  let n = String.length hex in
  if n mod 2 <> 0 then failwith "cb_hex_bytes: odd length" else
  List.init (n / 2) (fun i -> int_of_string ("0x" ^ String.sub hex (2 * i) 2));;

let cb_file_bytes file =
  let ic = open_in_bin file in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  List.init n (fun i -> Char.code (String.get s i));;

let cb_byte_list literal =
  mk_list (map (fun b -> mk_comb(`word:num->byte`, mk_small_numeral b)) literal, `:byte`);;

(* NAME_mc := the literal, once it equals the record and the .bin. *)
let cb_literals = ref ([] : (string * int list) list);;

let cb_define name literal =
  let record = try cb_hex_bytes (assoc name !cb_records)
               with Failure _ -> failwith ("cb_define: no image record for " ^ name) in
  let file = cb_artifacts ^ "/" ^ name ^ ".bin" in
  let bin = cb_file_bytes file in
  if length literal <> 34 then failwith ("cb_define: " ^ name ^ " is not 34 bytes") else
  if record <> literal then failwith ("cb_define: " ^ name ^ ".hol differs from the literal") else
  if bin <> literal then failwith ("cb_define: " ^ name ^ ".bin differs from the literal") else
  let th = new_definition (mk_eq (mk_var (name ^ "_mc", `:byte list`), cb_byte_list literal)) in
  cb_literals := (name, literal) :: !cb_literals;
  Printf.printf "BYTES %s: 34 bytes, the literal = %s.hol = %s.bin (md5 %s)\n%!"
    name name name (Digest.to_hex (Digest.file file));
  th;;

let add64_mc = cb_define "add64"
 [0xf3; 0x0f; 0x1e; 0xfa;                      (* ENDBR64 *)
  0x48; 0x8b; 0x87; 0x00; 0x00; 0x00; 0x00;   (* MOV (% rax) (Memop Quadword (%% (rdi,0))) *)
  0x48; 0x8b; 0x97; 0x08; 0x00; 0x00; 0x00;   (* MOV (% rdx) (Memop Quadword (%% (rdi,8))) *)
  0x48; 0x01; 0xd0;                            (* ADD (% rax) (% rdx) *)
  0x48; 0x89; 0x86; 0x00; 0x00; 0x00; 0x00;   (* MOV (Memop Quadword (%% (rsi,0))) (% rax) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;                (* MOV (% eax) (Imm32 (word 1)) *)
  0xc3];;                                      (* RET *)

let sub64_mc = cb_define "sub64"
 [0xf3; 0x0f; 0x1e; 0xfa;                      (* ENDBR64 *)
  0x48; 0x8b; 0x87; 0x00; 0x00; 0x00; 0x00;   (* MOV (% rax) (Memop Quadword (%% (rdi,0))) *)
  0x48; 0x8b; 0x97; 0x08; 0x00; 0x00; 0x00;   (* MOV (% rdx) (Memop Quadword (%% (rdi,8))) *)
  0x48; 0x29; 0xd0;                            (* SUB (% rax) (% rdx) *)
  0x48; 0x89; 0x86; 0x00; 0x00; 0x00; 0x00;   (* MOV (Memop Quadword (%% (rsi,0))) (% rax) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;                (* MOV (% eax) (Imm32 (word 1)) *)
  0xc3];;                                      (* RET *)

let and64_mc = cb_define "and64"
 [0xf3; 0x0f; 0x1e; 0xfa;                      (* ENDBR64 *)
  0x48; 0x8b; 0x87; 0x00; 0x00; 0x00; 0x00;   (* MOV (% rax) (Memop Quadword (%% (rdi,0))) *)
  0x48; 0x8b; 0x97; 0x08; 0x00; 0x00; 0x00;   (* MOV (% rdx) (Memop Quadword (%% (rdi,8))) *)
  0x48; 0x21; 0xd0;                            (* AND (% rax) (% rdx) *)
  0x48; 0x89; 0x86; 0x00; 0x00; 0x00; 0x00;   (* MOV (Memop Quadword (%% (rsi,0))) (% rax) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;                (* MOV (% eax) (Imm32 (word 1)) *)
  0xc3];;                                      (* RET *)

let or64_mc = cb_define "or64"
 [0xf3; 0x0f; 0x1e; 0xfa;                      (* ENDBR64 *)
  0x48; 0x8b; 0x87; 0x00; 0x00; 0x00; 0x00;   (* MOV (% rax) (Memop Quadword (%% (rdi,0))) *)
  0x48; 0x8b; 0x97; 0x08; 0x00; 0x00; 0x00;   (* MOV (% rdx) (Memop Quadword (%% (rdi,8))) *)
  0x48; 0x09; 0xd0;                            (* OR (% rax) (% rdx) *)
  0x48; 0x89; 0x86; 0x00; 0x00; 0x00; 0x00;   (* MOV (Memop Quadword (%% (rsi,0))) (% rax) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;                (* MOV (% eax) (Imm32 (word 1)) *)
  0xc3];;                                      (* RET *)

let xor64_mc = cb_define "xor64"
 [0xf3; 0x0f; 0x1e; 0xfa;                      (* ENDBR64 *)
  0x48; 0x8b; 0x87; 0x00; 0x00; 0x00; 0x00;   (* MOV (% rax) (Memop Quadword (%% (rdi,0))) *)
  0x48; 0x8b; 0x97; 0x08; 0x00; 0x00; 0x00;   (* MOV (% rdx) (Memop Quadword (%% (rdi,8))) *)
  0x48; 0x31; 0xd0;                            (* XOR (% rax) (% rdx) *)
  0x48; 0x89; 0x86; 0x00; 0x00; 0x00; 0x00;   (* MOV (Memop Quadword (%% (rsi,0))) (% rax) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;                (* MOV (% eax) (Imm32 (word 1)) *)
  0xc3];;                                      (* RET *)

let ADD64_EXEC = X86_MK_EXEC_RULE add64_mc;;
let SUB64_EXEC = X86_MK_EXEC_RULE sub64_mc;;
let AND64_EXEC = X86_MK_EXEC_RULE and64_mc;;
let OR64_EXEC = X86_MK_EXEC_RULE or64_mc;;
let XOR64_EXEC = X86_MK_EXEC_RULE xor64_mc;;

(* What the model decodes at each offset: the instruction of each step. *)
let cb_print_decodes name (_,decs) =
  Array.iteri (fun i d -> match d with
    | Some th -> Printf.printf "DECODE %s +%d: %s\n%!" name i
                   (string_of_term (rand(snd(strip_forall(snd(dest_imp(snd(strip_forall(concl th)))))))))
    | None -> ()) decs;;

cb_print_decodes "add64" ADD64_EXEC;;
cb_print_decodes "sub64" SUB64_EXEC;;
cb_print_decodes "and64" AND64_EXEC;;
cb_print_decodes "or64" OR64_EXEC;;
cb_print_decodes "xor64" XOR64_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The run in the model's terms.                                             *)
(*                                                                           *)
(* Entry: the 34 bytes at pc, RIP = pc, RSP = stackpointer with the return   *)
(* word returnaddress there, RDI = inp, RSI = outp, in[0] = x, in[1] = y     *)
(* (8-byte little-endian words), the event log e.                            *)
(* Return: RIP = returnaddress, RSP = stackpointer + 8, RAX = 1,             *)
(* out[0] = op x y, in[0] and in[1] unchanged, and the log extended by       *)
(* exactly the run's accesses (newest first): the return's jump and its read *)
(* of the return word, the store to out[0], the reads of in[1] and in[0].    *)
(* Frame: only RIP, RSP, RAX, RDX, the six arithmetic flags, the event log   *)
(* and the eight bytes of out[0] may differ from the entry state; every      *)
(* other register (RBX, RBP, R12-R15, RDI, RSI, RCX, R8-R11, the vector and  *)
(* mask registers), every other RFLAGS bit and every other byte is kept.     *)
(* ------------------------------------------------------------------------- *)

let cb_core_template =
 `!pc inp outp x y stackpointer returnaddress e.
     nonoverlapping (outp,8) (word pc,34) /\
     nonoverlapping (outp,8) (stackpointer,8) /\
     nonoverlapping (outp,8) (inp,16)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [inp; outp] s /\
               read (memory :> bytes64 inp) s = x /\
               read (memory :> bytes64 (word_add inp (word 8))) s = y /\
               read events s = e)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               read RAX s = word 1 /\
               read (memory :> bytes64 outp) s = op x y /\
               read (memory :> bytes64 inp) s = x /\
               read (memory :> bytes64 (word_add inp (word 8))) s = y /\
               read events s =
                 APPEND [EventJump (word(pc + 34),returnaddress);
                         EventLoad (stackpointer,8);
                         EventStore (outp,8);
                         EventLoad (word_add inp (word 8),8);
                         EventLoad (inp,8)] e)
          (MAYCHANGE [RIP; RSP; RAX; RDX] ,, MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes64 outp])`;;

let cb_core_goal mc op =
  vsubst [mc, `mc:byte list`; op, `op:int64->int64->int64`] cb_core_template;;

(* The seven steps (ENDBR64 first), then the final state against the        *)
(* postcondition and the frame.                                              *)
let CB_CORE_STEPS_TAC execth =
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC
   [`pc:num`; `inp:int64`; `outp:int64`; `x:int64`; `y:int64`;
    `stackpointer:int64`; `returnaddress:int64`; `e:uarch_event list`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC execth (1--7) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[APPEND; WORD_ADD_0];;

let CB_CORE_TAC execth =
  CB_CORE_STEPS_TAC execth THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE;;

let ADD64_CORE = prove(cb_core_goal `add64_mc` `word_add:int64->int64->int64`, CB_CORE_TAC ADD64_EXEC);;
let SUB64_CORE = prove(cb_core_goal `sub64_mc` `word_sub:int64->int64->int64`, CB_CORE_TAC SUB64_EXEC);;
let AND64_CORE = prove(cb_core_goal `and64_mc` `word_and:int64->int64->int64`, CB_CORE_TAC AND64_EXEC);;
let OR64_CORE = prove(cb_core_goal `or64_mc` `word_or:int64->int64->int64`, CB_CORE_TAC OR64_EXEC);;
let XOR64_CORE = prove(cb_core_goal `xor64_mc` `word_xor:int64->int64->int64`, CB_CORE_TAC XOR64_EXEC);;

(* ------------------------------------------------------------------------- *)
(* The shared contract.                                                      *)
(*                                                                           *)
(* Entry facts (CONTRACT.txt, "Shared entry assumptions"): in, out and the   *)
(* return-word address 8-byte aligned; the 16 input bytes, the 8 output      *)
(* bytes and the 8 return-word bytes at canonical addresses, without wrap;   *)
(* the return address canonical, and the stack after the return; out[0..7]   *)
(* apart from the 34 code bytes, the return word and the 16 input bytes.     *)
(* Canonical is the 48-bit form (four-level paging): bits 63..47 equal.      *)
(* ------------------------------------------------------------------------- *)

let cb_canonical = new_definition
 `cb_canonical (a:int64) <=> val a < 2 EXP 47 \/ 2 EXP 64 - 2 EXP 47 <= val a`;;

let cb_area = new_definition
 `cb_area (a:int64) n <=>
    val a + n <= 2 EXP 64 /\ !i. i < n ==> cb_canonical (word_add a (word i))`;;

let cb_entry = new_definition
 `cb_entry pc (inp:int64) (outp:int64) (stackpointer:int64) (returnaddress:int64) <=>
    aligned 8 inp /\ aligned 8 outp /\ aligned 8 stackpointer /\
    cb_area inp 16 /\ cb_area outp 8 /\ cb_area stackpointer 8 /\
    cb_canonical returnaddress /\ cb_canonical (word_add stackpointer (word 8)) /\
    nonoverlapping (outp,8) (word pc,34) /\
    nonoverlapping (outp,8) (stackpointer,8) /\
    nonoverlapping (outp,8) (inp,16)`;;

(* The result in the contract's arithmetic: unsigned words mod 2^64 for ADD  *)
(* and SUB (SUB as the integer difference reduced mod 2^64), bit by bit for  *)
(* AND, OR and XOR.                                                          *)

let CB_ADD_ARITH = prove
 (`!x y:int64. val(word_add x y) = (val x + val y) MOD 2 EXP 64`,
  REWRITE_TAC[VAL_WORD_ADD; DIMINDEX_64]);;

let CB_SUB_ARITH = prove
 (`!x y:int64. &(val(word_sub x y)):int = (&(val x) - &(val y)) rem &(2 EXP 64)`,
  REWRITE_TAC[INT_VAL_WORD_SUB; DIMINDEX_64; INT_OF_NUM_POW]);;

(* Bit i of a word is false from i = 64 on, so the bitwise laws hold for every i. *)
let CB_AND_BITS = prove
 (`!x y:int64 i. bit i (word_and x y) <=> bit i x /\ bit i y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIT_WORD_AND] THEN
  MESON_TAC[BIT_GUARD]);;

let CB_OR_BITS = prove
 (`!x y:int64 i. bit i (word_or x y) <=> bit i x \/ bit i y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIT_WORD_OR] THEN
  MESON_TAC[BIT_GUARD]);;

let CB_XOR_BITS = prove
 (`!x y:int64 i. bit i (word_xor x y) <=> ~(bit i x <=> bit i y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIT_WORD_XOR] THEN
  MESON_TAC[BIT_GUARD; BIT_TRIVIAL; NOT_LT]);;

(* The accesses of a run: reads inside the 16 input bytes and the return     *)
(* word, the one write inside the output word.                               *)
let CB_TRACE_INBOUNDS = prove
 (`!pc inp outp stackpointer returnaddress.
     memaccess_inbounds
       [EventJump (word(pc + 34),returnaddress); EventLoad (stackpointer,8);
        EventStore (outp,8); EventLoad (word_add inp (word 8),8); EventLoad (inp,8)]
       [(inp,16); (stackpointer,8)] [(outp,8)]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[memaccess_inbounds; ALL; EX] THEN
  REWRITE_TAC[CONTAINED_MODULO_REFL; ARITH_RULE `8 <= 8 /\ 8 <= 16`] THEN
  DISJ1_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64; CONTAINED_MODULO_LMOD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC CONTAINED_MODULO_OFFSET_SIMPLE THEN
  CONV_TAC NUM_REDUCE_CONV);;

let cb_contract_template =
 `!pc inp outp x y stackpointer returnaddress e.
     cb_entry pc inp outp stackpointer returnaddress
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [inp; outp] s /\
               read (memory :> bytes64 inp) s = x /\
               read (memory :> bytes64 (word_add inp (word 8))) s = y /\
               read events s = e)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               read RAX s = word 1 /\
               result x y (read (memory :> bytes64 outp) s) /\
               read (memory :> bytes64 inp) s = x /\
               read (memory :> bytes64 (word_add inp (word 8))) s = y /\
               (?e'. read events s = APPEND e' e /\
                     memaccess_inbounds e' [(inp,16); (stackpointer,8)] [(outp,8)]))
          (MAYCHANGE [RIP; RSP; RAX; RDX] ,, MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes64 outp])`;;

let cb_contract_goal mc result =
  let tm = vsubst [mc, `mc:byte list`; result, `result:int64->int64->int64->bool`]
                  cb_contract_template in
  rhs(concl(TOP_DEPTH_CONV BETA_CONV tm));;

let CB_CONTRACT_TAC core arith =
  let q = rand(rator(snd(dest_imp(snd(strip_forall(concl core)))))) in
  REWRITE_TAC[cb_entry] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC q THEN CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[arith] THEN
    EXISTS_TAC
     `[EventJump (word(pc + 34),returnaddress:int64); EventLoad (stackpointer:int64,8);
       EventStore (outp:int64,8); EventLoad (word_add (inp:int64) (word 8),8);
       EventLoad (inp,8)]` THEN
    REWRITE_TAC[CB_TRACE_INBOUNDS];
    MATCH_MP_TAC core THEN ASM_REWRITE_TAC[]];;

let ADD64_CONTRACT = prove
 (cb_contract_goal `add64_mc`
    `\(x:int64) (y:int64) (r:int64). val r = (val x + val y) MOD 2 EXP 64`,
  CB_CONTRACT_TAC ADD64_CORE CB_ADD_ARITH);;

let SUB64_CONTRACT = prove
 (cb_contract_goal `sub64_mc`
    `\(x:int64) (y:int64) (r:int64). &(val r):int = (&(val x) - &(val y)) rem &(2 EXP 64)`,
  CB_CONTRACT_TAC SUB64_CORE CB_SUB_ARITH);;

let AND64_CONTRACT = prove
 (cb_contract_goal `and64_mc`
    `\(x:int64) (y:int64) (r:int64). !i. bit i r <=> bit i x /\ bit i y`,
  CB_CONTRACT_TAC AND64_CORE CB_AND_BITS);;

let OR64_CONTRACT = prove
 (cb_contract_goal `or64_mc`
    `\(x:int64) (y:int64) (r:int64). !i. bit i r <=> bit i x \/ bit i y`,
  CB_CONTRACT_TAC OR64_CORE CB_OR_BITS);;

let XOR64_CONTRACT = prove
 (cb_contract_goal `xor64_mc`
    `\(x:int64) (y:int64) (r:int64). !i. bit i r <=> ~(bit i x <=> bit i y)`,
  CB_CONTRACT_TAC XOR64_CORE CB_XOR_BITS);;

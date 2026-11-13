(* ========================================================================= *)
(* unpack, the record plans' leaf 2 (tcalc/native/PLANS.txt): the field a   *)
(* of a packed key word k0 = tag + 8a whose tag is the expected one. The    *)
(* program is tcalc/native/leaves/unpack/unpack.metta's text               *)
(* (unpack_prog.txt; image record unpack.hol). No regions; arg0 k0, arg1    *)
(* the tag.                                                                  *)
(*                                                                           *)
(* UNPACK_RUN: every run from a state entry validation accepts ends in      *)
(* unpack_post: the status word is the outcome, the fuel receipt is kept,   *)
(* and                                                                       *)
(*   FIRED with ret_val k0 DIV 8 when k0 MOD 8 is the tag;                  *)
(*   REFUSED otherwise.                                                     *)
(* With UNPACK_DECLS and UNPACK_LEAF_WF that is pl_unpack_spec unpack       *)
(* (tcalc/native/leaves/leaves_spec.ml, over plans_leaves.ml).              *)
(* ========================================================================= *)

needs "native/leaves/common/leaf_lib.ml";;

(* The program, as its text unpack_prog.txt. *)
let UNPACK_TERM = new_definition
 `unpack = (TProg [] [] (TSeq (TInstr (TLoadFrame TyU64 1 22)) (TSeq (TInstr (TLoadFrame TyU64 2 23)) (TSeq (TInstr (TImm TyU64 3 (word 7))) (TSeq (TInstr (TBin BinAnd TyU64 3 1 3)) (TSeq (TInstr (TCmp CondEq TyU64 4 3 (OpReg 2))) (TSeq (TIf 4 (TSeq (TInstr (TShift ShiftRightU TyU64 5 1 3)) (TReturn 1 5)) TSkip) (TReturn 0 4))))))))`;;

let UNPACK_DECLS = prove(`tisa_decls unpack = []`, REWRITE_TAC[UNPACK_TERM; tisa_decls]);;

let UNPACK_LEAF_WF = prove(`tisa_leaf_wf unpack`, LEAF_WF_TAC UNPACK_DECLS UNPACK_TERM);;

(* What every run leaves. *)
let unpack_post = new_definition
 `unpack_post t k u <=>
    tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21 /\
    (if val(tisa_fword t 22) MOD 8 = val(tisa_fword t 23)
     then k = 1 /\ tisa_fword u 19 = word(val(tisa_fword t 22) DIV 8)
     else k = 0)`;;

(* The tag: the low three bits; the field: the rest. *)
let UNPACK_LOW = prove
 (`!k0 tag:int64. word_and k0 (word 7) = tag <=> val k0 MOD 8 = val tag`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV (ISPECL [`k0:int64`; `3`] VAL_WORD_AND_MASK_WORD)) THEN
  DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let UNPACK_HIGH = prove
 (`!k0:int64. word_ushr k0 3 = word(val k0 DIV 8)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `k0:int64` VAL_BOUND_64) THEN MP_TAC(SPECL [`val(k0:int64)`; `8`] DIV_LE) THEN
  ARITH_TAC);;

let UNPACK_WP = prove
 (`!t. tisa_entry_ok unpack t ==> tisa_wp (tisa_root unpack) (\s. F) (unpack_post t) t`,
  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP LEAF_ENTRY_FRAME) THEN
  REWRITE_TAC[UNPACK_TERM; tisa_root] THEN TISA_VCG_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[UNPACK_LOW]) THEN
  REWRITE_TAC[unpack_post] THEN TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[UNPACK_HIGH]);;

let UNPACK_RUN = prove
 (`!t k u. tisa_entry_ok unpack t /\ tisa_run unpack t = TStop k u ==> unpack_post t k u`,
  MESON_TAC[LEAF_RUN_BY_WP; UNPACK_WP]);;

(* Every theorem this file states, for the audits. *)
let unpack_theorems =
 ["UNPACK_TERM", UNPACK_TERM;
  "UNPACK_DECLS", UNPACK_DECLS;
  "UNPACK_LEAF_WF", UNPACK_LEAF_WF;
  "unpack_post", unpack_post;
  "UNPACK_LOW", UNPACK_LOW;
  "UNPACK_HIGH", UNPACK_HIGH;
  "UNPACK_WP", UNPACK_WP;
  "UNPACK_RUN", UNPACK_RUN];;

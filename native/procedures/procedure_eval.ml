(* Functional execution derived from the bounded procedure relations. *)
needs "native/procedures/procedure_rules.ml";;

let procedure_function_leaf = new_definition
 `procedure_function_leaf fn (b:num) (st:int64 list) (cw:num->num) (s:A) (used:num) (k:num) (pay:num) (s1:A) (used1:num) <=>
    fn b st cw s used = (k,pay,s1,used1)`;;

let procedure_eval_exec = define
 `(procedure_eval_exec call_tag fn invoke (b:num) [] i cw (s:A) (used:num) = (1,i,cw,s,used)) /\
  (procedure_eval_exec call_tag fn invoke b (CONS st sts) i cw s used =
    if call_tag < val(EL 0 st) then (3,i,cw,s,used)
    else let r = if val(EL 0 st) = call_tag
                 then invoke (val(EL 1 st)) (procedure_args st cw) s used
                 else fn b st cw s used in
         let cw1 = procedure_set cw (val(EL 17 st)) (FST(SND r)) in
         if FST r = 1
         then procedure_eval_exec call_tag fn invoke b sts (i + 1) cw1 (FST(SND(SND r))) (SND(SND(SND r)))
         else (FST r,i,cw1,FST(SND(SND r)),SND(SND(SND r))))`;;

let procedure_eval_choose = define
 `(procedure_eval_choose call_tag fn invoke (b:num) [] args (s:A) (used:num) = (0,0,s,used)) /\
  (procedure_eval_choose call_tag fn invoke b (CONS clause cls) args s used =
    let r = procedure_eval_exec call_tag fn invoke b clause 0 (procedure_frame args) s used in
    if FST r = 0
    then procedure_eval_choose call_tag fn invoke b cls args (FST(SND(SND(SND r)))) (SND(SND(SND(SND r))))
    else (FST r,(FST(SND(SND r))) 7,FST(SND(SND(SND r))),SND(SND(SND(SND r)))))`;;

let procedure_eval_boundary = new_definition
 `procedure_eval_boundary (r:num#num#A#num) =
    (procedure_call_outcome(FST r),FST(SND r),FST(SND(SND r)),SND(SND(SND r)))`;;

let procedure_eval_call = new_recursive_definition num_RECURSION
 `(procedure_eval_call 0 call_tag fn P b pid args (s:A) used =
    if b < used then (3,3,s,used)
    else if LENGTH P <= pid then (3,3,s,used)
    else (2,0,s,used)) /\
  (procedure_eval_call (SUC n) call_tag fn P b pid args s used =
    if b < used then (3,3,s,used)
    else if LENGTH P <= pid then (3,3,s,used)
    else if used = b then (4,4,s,used)
    else procedure_eval_boundary
          (procedure_eval_choose call_tag fn (procedure_eval_call n call_tag fn P b) b (EL pid P) args s (used + 1)))`;;

let PROCEDURE_EVAL_BAD_RECEIPT = prove
 (`!call_tag n fn P b pid args (s:A) used. b < used
    ==> procedure_eval_call n call_tag fn P b pid args s used = (3,3,s,used)`,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[procedure_eval_call]);;

let PROCEDURE_EVAL_BAD_TARGET = prove
 (`!call_tag n fn P b pid args (s:A) used. used <= b /\ LENGTH P <= pid
    ==> procedure_eval_call n call_tag fn P b pid args s used = (3,3,s,used)`,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[procedure_eval_call;ARITH_RULE `u <= b ==> ~(b < u)`]);;

let PROCEDURE_EVAL_FULL = prove
 (`!call_tag fn P b pid args (s:A) used. used <= b /\ pid < LENGTH P
    ==> procedure_eval_call 0 call_tag fn P b pid args s used = (2,0,s,used)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[procedure_eval_call;ARITH_RULE `u <= b ==> ~(b < u)`;
               ARITH_RULE `p < n ==> ~(n <= p)`]);;

let PROCEDURE_EVAL_EXHAUSTED = prove
 (`!call_tag n fn P b pid args (s:A) used. 0 < n /\ pid < LENGTH P /\ used = b
    ==> procedure_eval_call n call_tag fn P b pid args s used = (4,4,s,used)`,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[CONJUNCT1 LT] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[procedure_eval_call;LT_REFL;ARITH_RULE `p < n ==> ~(n <= p)`]);;

let PROCEDURE_EVAL_ENTER = prove
 (`!call_tag fn P b cap depth pid args (s:A) used. depth < cap /\ pid < LENGTH P /\ used < b
    ==> procedure_eval_call (cap - depth) call_tag fn P b pid args s used =
        procedure_eval_boundary
          (procedure_eval_choose call_tag fn (procedure_eval_call (cap - (depth + 1)) call_tag fn P b)
            b (EL pid P) args s (used + 1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `cap - depth = SUC(cap - (depth + 1))` SUBST1_TAC THENL
   [ASM_ARITH_TAC;ALL_TAC] THEN
  ASM_SIMP_TAC[procedure_eval_call;ARITH_RULE `u < b ==> ~(b < u) /\ ~(u = b)`;
               ARITH_RULE `p < n ==> ~(n <= p)`]);;

let PROCEDURE_EVAL_RULE_PREP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[procedure_function_leaf]);;

let PROCEDURE_EVAL_DERIVATIONS = prove
 (`!fn.
   (!call_tag L P b cap depth p i cw (s:A) used r.
      procedure_exec call_tag L P b cap depth p i cw s used r
      ==> L = procedure_function_leaf fn
      ==> procedure_eval_exec call_tag fn (procedure_eval_call (cap - depth) call_tag fn P b) b p i cw s used = r) /\
   (!call_tag L P b cap depth cls args (s:A) used r.
      procedure_choose call_tag L P b cap depth cls args s used r
      ==> L = procedure_function_leaf fn
      ==> procedure_eval_choose call_tag fn (procedure_eval_call (cap - depth) call_tag fn P b) b cls args s used = r) /\
   (!call_tag L P b cap depth pid args (s:A) used r.
      procedure_call call_tag L P b cap depth pid args s used r
      ==> L = procedure_function_leaf fn
      ==> procedure_eval_call (cap - depth) call_tag fn P b pid args s used = r)`,
  GEN_TAC THEN MATCH_MP_TAC procedure_INDUCT THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[procedure_eval_exec];
    PROCEDURE_EVAL_RULE_PREP_TAC THEN
    ASM_SIMP_TAC[procedure_eval_exec;LET_DEF;LET_END_DEF;FST;SND;
      ARITH_RULE `(n:num) < call_tag ==> ~(call_tag < n) /\ ~(n = call_tag)`];
    PROCEDURE_EVAL_RULE_PREP_TAC THEN
    ASM_SIMP_TAC[procedure_eval_exec;LET_DEF;LET_END_DEF;FST;SND;
      ARITH_RULE `(n:num) < call_tag ==> ~(call_tag < n) /\ ~(n = call_tag)`];
    PROCEDURE_EVAL_RULE_PREP_TAC THEN
    ASM_REWRITE_TAC[procedure_eval_exec;LET_DEF;LET_END_DEF;FST;SND;ARITH_EQ;LT_REFL];
    PROCEDURE_EVAL_RULE_PREP_TAC THEN
    ASM_REWRITE_TAC[procedure_eval_exec;LET_DEF;LET_END_DEF;FST;SND;ARITH_EQ;LT_REFL];
    PROCEDURE_EVAL_RULE_PREP_TAC THEN ASM_REWRITE_TAC[procedure_eval_exec];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[procedure_eval_choose];
    PROCEDURE_EVAL_RULE_PREP_TAC THEN
    ASM_REWRITE_TAC[procedure_eval_choose;LET_DEF;LET_END_DEF;FST;SND];
    PROCEDURE_EVAL_RULE_PREP_TAC THEN
    ASM_REWRITE_TAC[procedure_eval_choose;LET_DEF;LET_END_DEF;FST;SND];
    PROCEDURE_EVAL_RULE_PREP_TAC THEN ASM_SIMP_TAC[PROCEDURE_EVAL_BAD_RECEIPT];
    PROCEDURE_EVAL_RULE_PREP_TAC THEN ASM_SIMP_TAC[PROCEDURE_EVAL_BAD_TARGET];
    PROCEDURE_EVAL_RULE_PREP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `cap <= d ==> cap - d = 0`;PROCEDURE_EVAL_FULL];
    PROCEDURE_EVAL_RULE_PREP_TAC THEN MATCH_MP_TAC PROCEDURE_EVAL_EXHAUSTED THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    PROCEDURE_EVAL_RULE_PREP_TAC THEN
    ASM_SIMP_TAC[PROCEDURE_EVAL_ENTER;procedure_eval_boundary;FST;SND]]);;

let PROCEDURE_FUNCTION_LEAF_TOTAL = prove
 (`!fn:num->int64 list->(num->num)->A->num->num#num#A#num.
     procedure_leaf_total (procedure_function_leaf fn)`,
  REWRITE_TAC[procedure_leaf_total;procedure_function_leaf] THEN
  REPEAT GEN_TAC THEN MAP_EVERY EXISTS_TAC
   [`FST((fn:num->int64 list->(num->num)->A->num->num#num#A#num) b st cw s used)`;
    `FST(SND((fn:num->int64 list->(num->num)->A->num->num#num#A#num) b st cw s used))`;
    `FST(SND(SND((fn:num->int64 list->(num->num)->A->num->num#num#A#num) b st cw s used)))`;
    `SND(SND(SND((fn:num->int64 list->(num->num)->A->num->num#num#A#num) b st cw s used)))`] THEN
  REWRITE_TAC[PAIR]);;

let PROCEDURE_EVAL_EXEC_RUN,PROCEDURE_EVAL_CHOOSE_RUN,PROCEDURE_EVAL_CALL_RUN =
  match map
    (fun th -> GEN_ALL(REWRITE_RULE[]
      (SPECL [`call_tag:num`;`procedure_function_leaf
              (fn:num->int64 list->(num->num)->A->num->num#num#A#num)`] th)))
    (CONJUNCTS(SPEC_ALL PROCEDURE_EVAL_DERIVATIONS)) with
  | [x;y;z] -> x,y,z
  | _ -> failwith "procedure derivation theorem shape";;

let PROCEDURE_FUNCTION_CALL_TOTAL = GEN_ALL
 (MATCH_MP
   (ISPECL [`call_tag:num`;`procedure_function_leaf
      (fn:num->int64 list->(num->num)->A->num->num#num#A#num)`] PROCEDURE_CALL_TOTAL)
   (SPEC_ALL PROCEDURE_FUNCTION_LEAF_TOTAL));;

let PROCEDURE_FUNCTION_EXEC_TOTAL = prove
 (`!call_tag fn P b cap depth.
    !p i cw (s:A) used. ?k i1 cw1 s1 used1.
      procedure_exec call_tag (procedure_function_leaf fn) P b cap depth p i cw s used
        (k,i1,cw1,s1,used1)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC PROCEDURE_EXEC_TOTAL THEN
  REWRITE_TAC[PROCEDURE_FUNCTION_LEAF_TOTAL] THEN
  MATCH_ACCEPT_TAC PROCEDURE_FUNCTION_CALL_TOTAL);;

let PROCEDURE_FUNCTION_CHOOSE_TOTAL = prove
 (`!call_tag fn P b cap depth.
    !cls args (s:A) used. ?k pay s1 used1.
      procedure_choose call_tag (procedure_function_leaf fn) P b cap depth cls args s used
        (k,pay,s1,used1)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC PROCEDURE_CHOOSE_TOTAL THEN
  MATCH_ACCEPT_TAC PROCEDURE_FUNCTION_EXEC_TOTAL);;

let PROCEDURE_EVAL_CALL_EXACT = prove
 (`!call_tag fn P b cap depth pid args (s:A) used r.
    procedure_call call_tag (procedure_function_leaf fn) P b cap depth pid args s used r <=>
    procedure_eval_call (cap - depth) call_tag fn P b pid args s used = r`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL
   [`call_tag:num`;`fn:num->int64 list->(num->num)->A->num->num#num#A#num`;
    `P:(((int64 list)list)list)list`;`b:num`;`cap:num`;`depth:num`;
    `pid:num`;`args:num list`;`s:A`;`used:num`] PROCEDURE_FUNCTION_CALL_TOTAL) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `pay:num`
    (X_CHOOSE_THEN `s1:A` (X_CHOOSE_THEN `used1:num` ASSUME_TAC)))) THEN
  ASM_MESON_TAC[PROCEDURE_EVAL_CALL_RUN]);;

let PROCEDURE_EVAL_EXEC_EXACT = prove
 (`!call_tag fn P b cap depth p i cw (s:A) used r.
    procedure_exec call_tag (procedure_function_leaf fn) P b cap depth p i cw s used r <=>
    procedure_eval_exec call_tag fn (procedure_eval_call (cap - depth) call_tag fn P b) b p i cw s used = r`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL
   [`call_tag:num`;`fn:num->int64 list->(num->num)->A->num->num#num#A#num`;
    `P:(((int64 list)list)list)list`;`b:num`;`cap:num`;`depth:num`;
    `p:(int64 list)list`;`i:num`;`cw:num->num`;`s:A`;`used:num`]
   PROCEDURE_FUNCTION_EXEC_TOTAL) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `i1:num`
    (X_CHOOSE_THEN `cw1:num->num` (X_CHOOSE_THEN `s1:A`
      (X_CHOOSE_THEN `used1:num` ASSUME_TAC))))) THEN
  ASM_MESON_TAC[PROCEDURE_EVAL_EXEC_RUN]);;

let PROCEDURE_EVAL_CHOOSE_EXACT = prove
 (`!call_tag fn P b cap depth cls args (s:A) used r.
    procedure_choose call_tag (procedure_function_leaf fn) P b cap depth cls args s used r <=>
    procedure_eval_choose call_tag fn (procedure_eval_call (cap - depth) call_tag fn P b) b cls args s used = r`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL
   [`call_tag:num`;`fn:num->int64 list->(num->num)->A->num->num#num#A#num`;
    `P:(((int64 list)list)list)list`;`b:num`;`cap:num`;`depth:num`;
    `cls:((int64 list)list)list`;`args:num list`;`s:A`;`used:num`]
   PROCEDURE_FUNCTION_CHOOSE_TOTAL) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `pay:num`
    (X_CHOOSE_THEN `s1:A` (X_CHOOSE_THEN `used1:num` ASSUME_TAC)))) THEN
  ASM_MESON_TAC[PROCEDURE_EVAL_CHOOSE_RUN]);;

let procedure_eval_theorems =
 ["PROCEDURE_EVAL_BAD_RECEIPT",PROCEDURE_EVAL_BAD_RECEIPT;
  "PROCEDURE_EVAL_BAD_TARGET",PROCEDURE_EVAL_BAD_TARGET;
  "PROCEDURE_EVAL_FULL",PROCEDURE_EVAL_FULL;
  "PROCEDURE_EVAL_EXHAUSTED",PROCEDURE_EVAL_EXHAUSTED;
  "PROCEDURE_EVAL_ENTER",PROCEDURE_EVAL_ENTER;
  "PROCEDURE_EVAL_DERIVATIONS",PROCEDURE_EVAL_DERIVATIONS;
  "PROCEDURE_FUNCTION_LEAF_TOTAL",PROCEDURE_FUNCTION_LEAF_TOTAL;
  "PROCEDURE_EVAL_EXEC_RUN",PROCEDURE_EVAL_EXEC_RUN;
  "PROCEDURE_EVAL_CHOOSE_RUN",PROCEDURE_EVAL_CHOOSE_RUN;
  "PROCEDURE_EVAL_CALL_RUN",PROCEDURE_EVAL_CALL_RUN;
  "PROCEDURE_FUNCTION_CALL_TOTAL",PROCEDURE_FUNCTION_CALL_TOTAL;
  "PROCEDURE_FUNCTION_EXEC_TOTAL",PROCEDURE_FUNCTION_EXEC_TOTAL;
  "PROCEDURE_FUNCTION_CHOOSE_TOTAL",PROCEDURE_FUNCTION_CHOOSE_TOTAL;
  "PROCEDURE_EVAL_CALL_EXACT",PROCEDURE_EVAL_CALL_EXACT;
  "PROCEDURE_EVAL_EXEC_EXACT",PROCEDURE_EVAL_EXEC_EXACT;
  "PROCEDURE_EVAL_CHOOSE_EXACT",PROCEDURE_EVAL_CHOOSE_EXACT];;

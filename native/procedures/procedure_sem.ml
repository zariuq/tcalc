(* Bounded procedures over the existing 18-word call plans. The primitive
   relation supplies the same outcomes, payload, world and receipt as the
   native component interface. World effects survive a failed clause. *)
needs "Library/words.ml";;

let procedure_args = new_definition
 `procedure_args (st:int64 list) (cw:num->num) =
    [cw(val(EL 10 st));cw(val(EL 11 st));cw(val(EL 12 st));cw(val(EL 13 st));
     cw(val(EL 14 st));cw(val(EL 15 st));cw(val(EL 16 st))]`;;

let procedure_frame = new_definition
 `procedure_frame (args:num list) n =
    if n <= 6 then n else if 8 <= n /\ n < 15 then EL (n - 8) args else 0`;;

let procedure_set = new_definition
 `procedure_set (cw:num->num) n v j = if j = n then v else cw j`;;

let procedure_call_outcome = new_definition
 `procedure_call_outcome k = if k = 0 then 3 else k`;;

(* The depth is the number of live work-region frames. Call checks occur
   before activation; one successful activation charges exactly one unit.
   Clause selection does not reset the world or the accumulated receipt. *)
let procedure_RULES,procedure_INDUCT,procedure_CASES = new_inductive_definition
 `(!call_tag L P b cap depth i cw s used.
     procedure_exec call_tag L P b cap depth [] i cw (s:A) used (1,i,cw,s,used)) /\
  (!call_tag L P b cap depth st sts i cw s used pay s1 used1 r.
     val(EL 0 st) < call_tag /\ L b st cw (s:A) used 1 pay s1 used1 /\
     procedure_exec call_tag L P b cap depth sts (i + 1)
       (procedure_set cw (val(EL 17 st)) pay) s1 used1 r
     ==> procedure_exec call_tag L P b cap depth (CONS st sts) i cw s used r) /\
  (!call_tag L P b cap depth st sts i cw s used k pay s1 used1.
     val(EL 0 st) < call_tag /\ L b st cw (s:A) used k pay s1 used1 /\ ~(k = 1)
     ==> procedure_exec call_tag L P b cap depth (CONS st sts) i cw s used
       (k,i,procedure_set cw (val(EL 17 st)) pay,s1,used1)) /\
  (!call_tag L P b cap depth st sts i cw s used pay s1 used1 r.
     val(EL 0 st) = call_tag /\
     procedure_call call_tag L P b cap depth (val(EL 1 st)) (procedure_args st cw) (s:A) used
       (1,pay,s1,used1) /\
     procedure_exec call_tag L P b cap depth sts (i + 1)
       (procedure_set cw (val(EL 17 st)) pay) s1 used1 r
     ==> procedure_exec call_tag L P b cap depth (CONS st sts) i cw s used r) /\
  (!call_tag L P b cap depth st sts i cw s used k pay s1 used1.
     val(EL 0 st) = call_tag /\
     procedure_call call_tag L P b cap depth (val(EL 1 st)) (procedure_args st cw) (s:A) used
       (k,pay,s1,used1) /\ ~(k = 1)
     ==> procedure_exec call_tag L P b cap depth (CONS st sts) i cw s used
       (k,i,procedure_set cw (val(EL 17 st)) pay,s1,used1)) /\
  (!call_tag L P b cap depth st sts i cw s used.
     call_tag < val(EL 0 st)
     ==> procedure_exec call_tag L P b cap depth (CONS st sts) i cw (s:A) used (3,i,cw,s,used)) /\
  (!call_tag L P b cap depth args s used.
     procedure_choose call_tag L P b cap depth [] args (s:A) used (0,0,s,used)) /\
  (!call_tag L P b cap depth c cs args s used i cw1 s1 used1 r.
     procedure_exec call_tag L P b cap depth c 0 (procedure_frame args) (s:A) used
       (0,i,cw1,s1,used1) /\
     procedure_choose call_tag L P b cap depth cs args s1 used1 r
     ==> procedure_choose call_tag L P b cap depth (CONS c cs) args s used r) /\
  (!call_tag L P b cap depth c cs args s used k i cw1 s1 used1.
     procedure_exec call_tag L P b cap depth c 0 (procedure_frame args) (s:A) used
       (k,i,cw1,s1,used1) /\ ~(k = 0)
     ==> procedure_choose call_tag L P b cap depth (CONS c cs) args s used (k,cw1 7,s1,used1)) /\
  (!call_tag L P b cap depth pid args s used.
     b < used
     ==> procedure_call call_tag L P b cap depth pid args (s:A) used (3,3,s,used)) /\
  (!call_tag L P b cap depth pid args s used.
     used <= b /\ LENGTH P <= pid
     ==> procedure_call call_tag L P b cap depth pid args (s:A) used (3,3,s,used)) /\
  (!call_tag L P b cap depth pid args s used.
     used <= b /\ pid < LENGTH P /\ cap <= depth
     ==> procedure_call call_tag L P b cap depth pid args (s:A) used (2,0,s,used)) /\
  (!call_tag L P b cap depth pid args s used.
     pid < LENGTH P /\ depth < cap /\ used = b
     ==> procedure_call call_tag L P b cap depth pid args (s:A) used (4,4,s,used)) /\
  (!call_tag L P b cap depth pid args s used k pay s1 used1.
     pid < LENGTH P /\ depth < cap /\ used < b /\
     procedure_choose call_tag L P b cap (depth + 1) (EL pid P) args (s:A) (used + 1)
       (k,pay,s1,used1)
     ==> procedure_call call_tag L P b cap depth pid args s used
       (procedure_call_outcome k,pay,s1,used1))`;;

let PROCEDURE_EXEC_CASES,procedure_tail_cases = CONJ_PAIR procedure_CASES;;
let PROCEDURE_CHOOSE_CASES,PROCEDURE_CALL_CASES = CONJ_PAIR procedure_tail_cases;;

let PROCEDURE_FRAME_CONSTANTS = prove
 (`!args n. n <= 6 ==> procedure_frame args n = n`,
  SIMP_TAC[procedure_frame]);;
let PROCEDURE_FRAME_RESULT = prove
 (`!args. procedure_frame args 7 = 0`,
  REWRITE_TAC[procedure_frame] THEN CONV_TAC NUM_REDUCE_CONV);;
let PROCEDURE_ARGS_LENGTH = prove
 (`!st cw. LENGTH(procedure_args st cw) = 7`,
  REWRITE_TAC[procedure_args;LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;
let PROCEDURE_CALL_NOT_REFUSED = prove
 (`!k. ~(procedure_call_outcome k = 0)`,
  REWRITE_TAC[procedure_call_outcome] THEN GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[ARITH_EQ]);;

let procedure_leaf_receipt_ok = new_definition
 `procedure_leaf_receipt_ok L b <=>
    !(st:int64 list) (cw:num->num) (s:A) used (k:num) (pay:num) (s1:A) used1.
      used <= b /\ L b st cw s used k pay s1 used1
      ==> used <= used1 /\ used1 <= b`;;

let PROCEDURE_RECEIPTS = prove
 (`(!call_tag L P b cap depth p i cw (s:A) used r.
       procedure_exec call_tag L P b cap depth p i cw s used r
       ==> procedure_leaf_receipt_ok L b /\ used <= b
       ==> used <= SND(SND(SND(SND r))) /\ SND(SND(SND(SND r))) <= b) /\
   (!call_tag L P b cap depth cls args (s:A) used r.
       procedure_choose call_tag L P b cap depth cls args s used r
       ==> procedure_leaf_receipt_ok L b /\ used <= b
       ==> used <= SND(SND(SND r)) /\ SND(SND(SND r)) <= b) /\
   (!call_tag L P b cap depth pid args (s:A) used r.
       procedure_call call_tag L P b cap depth pid args s used r
       ==> procedure_leaf_receipt_ok L b /\ used <= b
       ==> used <= SND(SND(SND r)) /\ SND(SND(SND r)) <= b)`,
  MATCH_MP_TAC procedure_INDUCT THEN
  REWRITE_TAC[FST;SND] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[procedure_leaf_receipt_ok] THEN STRIP_TAC THEN STRIP_TAC THEN
  ASM_MESON_TAC[LE_TRANS;LE_REFL;ARITH_RULE `u < b ==> u + 1 <= b /\ u <= u + 1`;
                ARITH_RULE `~(b < u /\ u <= b)`]);;

let procedure_leaf_frame = new_definition
 `procedure_leaf_frame L R <=>
    !(b:num) (st:int64 list) (cw:num->num) (s:A) (used:num) (k:num)
      (pay:num) (s1:A) (used1:num).
      L b st cw s used k pay s1 used1 ==> R s s1`;;

let PROCEDURE_WORLD_FRAME = prove
 (`!R:A->A->bool.
     (!s. R s s) /\ (!s t u. R s t /\ R t u ==> R s u)
     ==> (!call_tag L P b cap depth p i cw s used r.
           procedure_exec call_tag L P b cap depth p i cw s used r
           ==> procedure_leaf_frame L R ==> R s (FST(SND(SND(SND r))))) /\
         (!call_tag L P b cap depth cls args s used r.
           procedure_choose call_tag L P b cap depth cls args s used r
           ==> procedure_leaf_frame L R ==> R s (FST(SND(SND r)))) /\
         (!call_tag L P b cap depth pid args s used r.
           procedure_call call_tag L P b cap depth pid args s used r
           ==> procedure_leaf_frame L R ==> R s (FST(SND(SND r))))`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC procedure_INDUCT THEN
  REWRITE_TAC[FST;SND;procedure_leaf_frame] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[]);;

let procedure_leaf_total = new_definition
 `procedure_leaf_total L <=>
    !(b:num) (st:int64 list) (cw:num->num) (s:A) (used:num).
      ?(k:num) (pay:num) (s1:A) (used1:num). L b st cw s used k pay s1 used1`;;

let procedure_has name th =
  can (find_term (fun t -> is_const t && fst(dest_const t) = name)) (concl th);;

let PROCEDURE_TOTAL_CONTINUE_TAC rule =
  FIRST_X_ASSUM(MP_TAC o SPECL [`i + 1`;`procedure_set cw (val(EL 17 (h:int64 list))) pay`;
                                `s1:A`;`used1:num`] o
    check (fun th -> is_forall(concl th) && procedure_has "procedure_exec" th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `i1:num`
    (X_CHOOSE_THEN `cw1:num->num` (X_CHOOSE_THEN `s2:A`
      (X_CHOOSE_THEN `used2:num` ASSUME_TAC))))) THEN
  MAP_EVERY EXISTS_TAC [`k1:num`;`i1:num`;`cw1:num->num`;`s2:A`;`used2:num`] THEN
  MATCH_MP_TAC rule THEN MAP_EVERY EXISTS_TAC [`pay:num`;`s1:A`;`used1:num`] THEN
  ASM_REWRITE_TAC[];;

let PROCEDURE_TOTAL_STOP_TAC rule =
  MAP_EVERY EXISTS_TAC [`k:num`;`i:num`;
    `procedure_set cw (val(EL 17 (h:int64 list))) pay`;`s1:A`;`used1:num`] THEN
  MATCH_MP_TAC rule THEN ASM_REWRITE_TAC[];;

let PROCEDURE_EXEC_TOTAL = prove
 (`!call_tag L P b cap depth.
     procedure_leaf_total L /\
     (!pid args (s:A) used. ?k pay s1 used1.
       procedure_call call_tag L P b cap depth pid args s used (k,pay,s1,used1))
     ==> !p i cw s used. ?k i1 cw1 s1 used1.
       procedure_exec call_tag L P b cap depth p i cw s used (k,i1,cw1,s1,used1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[procedure_leaf_total] THEN STRIP_TAC THEN
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN MAP_EVERY EXISTS_TAC
      [`1`;`i:num`;`cw:num->num`;`s:A`;`used:num`] THEN
    MATCH_ACCEPT_TAC(CONJUNCT1 procedure_RULES);
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `val(EL 0 (h:int64 list)) < call_tag` THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`b:num`;`h:int64 list`;`cw:num->num`;`s:A`;`used:num`] o
      check (fun th -> is_forall(concl th) &&
        not(procedure_has "procedure_exec" th) && not(procedure_has "procedure_call" th))) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `pay:num`
      (X_CHOOSE_THEN `s1:A` (X_CHOOSE_THEN `used1:num` ASSUME_TAC)))) THEN
    ASM_CASES_TAC `k = 1` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN PROCEDURE_TOTAL_CONTINUE_TAC (el 1 (CONJUNCTS procedure_RULES));
      PROCEDURE_TOTAL_STOP_TAC (el 2 (CONJUNCTS procedure_RULES))];
    ALL_TAC] THEN
  ASM_CASES_TAC `val(EL 0 (h:int64 list)) = call_tag` THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`val(EL 1 (h:int64 list))`;`procedure_args h cw`;
                                  `s:A`;`used:num`] o
      check (fun th -> is_forall(concl th) && procedure_has "procedure_call" th &&
        not(procedure_has "procedure_exec" th))) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `pay:num`
      (X_CHOOSE_THEN `s1:A` (X_CHOOSE_THEN `used1:num` ASSUME_TAC)))) THEN
    ASM_CASES_TAC `k = 1` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN PROCEDURE_TOTAL_CONTINUE_TAC (el 3 (CONJUNCTS procedure_RULES));
      PROCEDURE_TOTAL_STOP_TAC (el 4 (CONJUNCTS procedure_RULES))];
    MAP_EVERY EXISTS_TAC [`3`;`i:num`;`cw:num->num`;`s:A`;`used:num`] THEN
    MATCH_MP_TAC (el 5 (CONJUNCTS procedure_RULES)) THEN ASM_ARITH_TAC]);;

let PROCEDURE_CHOOSE_TOTAL = prove
 (`!call_tag L P b cap depth.
     (!p i cw (s:A) used. ?k i1 cw1 s1 used1.
       procedure_exec call_tag L P b cap depth p i cw s used (k,i1,cw1,s1,used1))
     ==> !cls args s used. ?k pay s1 used1.
       procedure_choose call_tag L P b cap depth cls args s used (k,pay,s1,used1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN MAP_EVERY EXISTS_TAC [`0`;`0`;`s:A`;`used:num`] THEN
    MATCH_ACCEPT_TAC (el 6 (CONJUNCTS procedure_RULES));ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`h:(int64 list)list`;`0`;`procedure_frame args`;
                                `s:A`;`used:num`] o
    check (fun th -> is_forall(concl th) && procedure_has "procedure_exec" th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `i1:num`
    (X_CHOOSE_THEN `cw1:num->num` (X_CHOOSE_THEN `s1:A`
      (X_CHOOSE_THEN `used1:num` ASSUME_TAC))))) THEN
  ASM_CASES_TAC `k = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`args:num list`;`s1:A`;`used1:num`] o
      check (fun th -> is_forall(concl th) && procedure_has "procedure_choose" th)) THEN
    DISCH_THEN(X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `pay:num`
      (X_CHOOSE_THEN `s2:A` (X_CHOOSE_THEN `used2:num` ASSUME_TAC)))) THEN
    MAP_EVERY EXISTS_TAC [`k2:num`;`pay:num`;`s2:A`;`used2:num`] THEN
    MATCH_MP_TAC (el 7 (CONJUNCTS procedure_RULES)) THEN
    MAP_EVERY EXISTS_TAC [`i1:num`;`cw1:num->num`;`s1:A`;`used1:num`] THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`k:num`;`(cw1:num->num) 7`;`s1:A`;`used1:num`] THEN
    MATCH_MP_TAC (el 8 (CONJUNCTS procedure_RULES)) THEN EXISTS_TAC `i1:num` THEN
    ASM_REWRITE_TAC[]]);;

let PROCEDURE_CALL_BOUNDARY = prove
 (`!call_tag L P b cap depth pid args (s:A) used.
     cap <= depth \/ b <= used \/ LENGTH P <= pid
     ==> ?k pay s1 used1. procedure_call call_tag L P b cap depth pid args s used (k,pay,s1,used1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `b < used` THENL
   [MAP_EVERY EXISTS_TAC [`3`;`3`;`s:A`;`used:num`] THEN
    MATCH_MP_TAC (el 9 (CONJUNCTS procedure_RULES)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `used <= b` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH (P:(((int64 list)list)list)list) <= pid` THENL
   [MAP_EVERY EXISTS_TAC [`3`;`3`;`s:A`;`used:num`] THEN
    MATCH_MP_TAC (el 10 (CONJUNCTS procedure_RULES)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pid < LENGTH (P:(((int64 list)list)list)list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC;ALL_TAC] THEN
  ASM_CASES_TAC `cap <= depth` THENL
   [MAP_EVERY EXISTS_TAC [`2`;`0`;`s:A`;`used:num`] THEN
    MATCH_MP_TAC (el 11 (CONJUNCTS procedure_RULES)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`4`;`4`;`s:A`;`used:num`] THEN
  MATCH_MP_TAC (el 12 (CONJUNCTS procedure_RULES)) THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let PROCEDURE_CALL_FROM_CHOOSE = prove
 (`!call_tag L P b cap depth.
     (!cls args (s:A) used. ?k pay s1 used1.
       procedure_choose call_tag L P b cap (depth + 1) cls args s used (k,pay,s1,used1))
     ==> !pid args s used. ?k pay s1 used1.
       procedure_call call_tag L P b cap depth pid args s used (k,pay,s1,used1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `cap <= depth \/ b <= used \/ LENGTH (P:(((int64 list)list)list)list) <= pid`
  THENL
   [MATCH_MP_TAC PROCEDURE_CALL_BOUNDARY THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `pid < LENGTH (P:(((int64 list)list)list)list) /\ depth < cap /\ used < b`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`EL (pid:num) (P:(((int64 list)list)list)list)`;
                                `args:num list`;`s:A`;`used + 1`] o
    check (fun th -> is_forall(concl th) && procedure_has "procedure_choose" th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `pay:num`
    (X_CHOOSE_THEN `s1:A` (X_CHOOSE_THEN `used1:num` ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`procedure_call_outcome k`;`pay:num`;`s1:A`;`used1:num`] THEN
  MATCH_MP_TAC (el 13 (CONJUNCTS procedure_RULES)) THEN ASM_REWRITE_TAC[]);;

let PROCEDURE_CALL_TOTAL_BOUND = prove
 (`!call_tag L. procedure_leaf_total L
       ==> !n P b cap depth. cap <= depth + n
           ==> !pid args (s:A) used. ?k pay s1 used1.
             procedure_call call_tag L P b cap depth pid args s used (k,pay,s1,used1)`,
  GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN
    REPEAT GEN_TAC THEN MATCH_MP_TAC PROCEDURE_CALL_BOUNDARY THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC PROCEDURE_CALL_FROM_CHOOSE THEN
    MATCH_MP_TAC PROCEDURE_CHOOSE_TOTAL THEN
    MATCH_MP_TAC PROCEDURE_EXEC_TOTAL THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`P:(((int64 list)list)list)list`;`b:num`;`cap:num`;`depth + 1`] o
      check (fun th -> is_forall(concl th) && procedure_has "procedure_call" th)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC;REWRITE_TAC[]]]);;

let PROCEDURE_CALL_TOTAL = prove
 (`!call_tag L. procedure_leaf_total L
       ==> !P b cap depth pid args (s:A) used. ?k pay s1 used1.
         procedure_call call_tag L P b cap depth pid args s used (k,pay,s1,used1)`,
  GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`call_tag:num`;`L:num->int64 list->(num->num)->A->num->num->num->A->num->bool`]
    PROCEDURE_CALL_TOTAL_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`cap:num`;`P:(((int64 list)list)list)list`;
                            `b:num`;`cap:num`;`depth:num`]) THEN
  ANTS_TAC THENL [ARITH_TAC;ALL_TAC] THEN
  DISCH_THEN(MATCH_ACCEPT_TAC o SPECL [`pid:num`;`args:num list`;`s:A`;`used:num`]));;

let procedure_sem_theorems =
 ["PROCEDURE_FRAME_CONSTANTS",PROCEDURE_FRAME_CONSTANTS;
  "PROCEDURE_FRAME_RESULT",PROCEDURE_FRAME_RESULT;
  "PROCEDURE_ARGS_LENGTH",PROCEDURE_ARGS_LENGTH;
  "PROCEDURE_CALL_NOT_REFUSED",PROCEDURE_CALL_NOT_REFUSED;
  "PROCEDURE_RECEIPTS",PROCEDURE_RECEIPTS;
  "PROCEDURE_WORLD_FRAME",PROCEDURE_WORLD_FRAME;
  "PROCEDURE_EXEC_TOTAL",PROCEDURE_EXEC_TOTAL;
  "PROCEDURE_CHOOSE_TOTAL",PROCEDURE_CHOOSE_TOTAL;
  "PROCEDURE_CALL_BOUNDARY",PROCEDURE_CALL_BOUNDARY;
  "PROCEDURE_CALL_FROM_CHOOSE",PROCEDURE_CALL_FROM_CHOOSE;
  "PROCEDURE_CALL_TOTAL_BOUND",PROCEDURE_CALL_TOTAL_BOUND;
  "PROCEDURE_CALL_TOTAL",PROCEDURE_CALL_TOTAL];;

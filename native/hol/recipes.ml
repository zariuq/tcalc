(* ========================================================================= *)
(* Recipes: record operations as guarded clauses that call each other, on   *)
(* the abstract plan machine of plans_abs.ml.                                *)
(*                                                                           *)
(* A clause is a plan: its steps run in order and the first outcome other  *)
(* than FIRED ends it (as pl_run). A recipe is a list of clauses over one   *)
(* entry frame: control words 0..6 hold 0..6, words 8..14 the seven         *)
(* arguments, word 7 the result. A call runs the clauses in turn until one *)
(* is not REFUSED; a recipe none of whose clauses applies is REFUSED, and   *)
(* the caller sees INVALID_INPUT (3): a recipe applied outside its domain   *)
(* is an error, never the failure of a record's guard.                      *)
(*                                                                           *)
(* Step 32 calls recipe EL (word 1) of the table P; words 10..16 name the  *)
(* control words passed as arguments, word 17 the one that receives the    *)
(* result, whatever the outcome (as a leaf's payload). Step 25 compares two *)
(* words (pl_relw). Clauses put their guards first; with exclusive guards  *)
(* the order of the clauses is the machine's, not the meaning's.           *)
(*                                                                           *)
(* RC_GROWS_CALL: a call grows only the tables its recipes may write (its   *)
(* footprint), by appending rows, and keeps distinct keys and the bounds.  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The machine.                                                              *)
(* ------------------------------------------------------------------------- *)

(* relw: FIRED with payload a when the order of a and b is one the mask m   *)
(* allows (1 below, 2 equal, 4 above; sums combine), else REFUSED.          *)
let pl_relw = new_definition
 `pl_relw (a:num) (b:num) (m:num) k (pay:num) <=>
    if a < b /\ ODD m \/ a = b /\ ODD(m DIV 2) \/ b < a /\ ODD(m DIV 4)
    then k = 1 /\ pay = a else k = 0`;;

let rc_leaf = new_definition
 `rc_leaf (st:int64 list) ((cw,ns,stk):pstate) k (pay:num) (ns':nstate) <=>
    pl_leaf st (cw,ns,stk) k pay ns' \/
    val(EL 0 st) = 25 /\
    pl_relw (cw(val(EL 10 st))) (cw(val(EL 11 st))) (cw(val(EL 12 st))) k pay /\ ns' = ns`;;

let rc_args = new_definition
 `rc_args (st:int64 list) (cw:num->num) =
    [cw(val(EL 10 st)); cw(val(EL 11 st)); cw(val(EL 12 st)); cw(val(EL 13 st));
     cw(val(EL 14 st)); cw(val(EL 15 st)); cw(val(EL 16 st))]`;;

let rc_frame = new_definition
 `rc_frame (cw:num->num) (args:num list) <=>
    (!n. n <= 6 ==> cw n = n) /\
    cw 8 = EL 0 args /\ cw 9 = EL 1 args /\ cw 10 = EL 2 args /\ cw 11 = EL 3 args /\
    cw 12 = EL 4 args /\ cw 13 = EL 5 args /\ cw 14 = EL 6 args`;;

let rc_outc = new_definition
 `rc_outc k = if k = 0 then 3 else k`;;

let rc_RULES,rc_INDUCT,rc_CASES = new_inductive_definition
 `(!P i s. rc_exec (P:(((int64 list)list)list)list) [] i (s:pstate) (1,i,s)) /\
  (!P st sts i cw ns stk pay ns' r.
      val(EL 0 st) < 32 /\ rc_leaf st (cw,ns,stk) 1 pay ns' /\
      rc_exec P sts (i + 1) (pl_set cw (val(EL 17 st)) pay,ns',stk) r
      ==> rc_exec P (CONS st sts) i (cw,ns,stk) r) /\
  (!P st sts i cw ns stk k pay ns'.
      val(EL 0 st) < 32 /\ rc_leaf st (cw,ns,stk) k pay ns' /\ ~(k = 1)
      ==> rc_exec P (CONS st sts) i (cw,ns,stk)
                  (k,i,(pl_set cw (val(EL 17 st)) pay,ns',stk))) /\
  (!P st sts i cw ns stk pay ns2 r.
      val(EL 0 st) = 32 /\ val(EL 1 st) < LENGTH P /\
      rc_call P (EL (val(EL 1 st)) P) (rc_args st cw) ns stk (1,pay,ns2) /\
      rc_exec P sts (i + 1) (pl_set cw (val(EL 17 st)) pay,ns2,stk) r
      ==> rc_exec P (CONS st sts) i (cw,ns,stk) r) /\
  (!P st sts i cw ns stk k pay ns2.
      val(EL 0 st) = 32 /\ val(EL 1 st) < LENGTH P /\
      rc_call P (EL (val(EL 1 st)) P) (rc_args st cw) ns stk (k,pay,ns2) /\ ~(k = 1)
      ==> rc_exec P (CONS st sts) i (cw,ns,stk)
                  (rc_outc k,i,(pl_set cw (val(EL 17 st)) pay,ns2,stk))) /\
  (!P args ns stk. rc_call P [] (args:num list) (ns:nstate) (stk:num list) (0,0,ns)) /\
  (!P c cs args ns stk cw0 i cw1 ns1 stk1 r.
      rc_frame cw0 args /\
      rc_exec P c 0 (cw0,ns,stk) (0,i,(cw1,ns1,stk1)) /\
      rc_call P cs args ns1 stk r
      ==> rc_call P (CONS c cs) args ns stk r) /\
  (!P c cs args ns stk cw0 k i cw1 ns1 stk1.
      rc_frame cw0 args /\
      rc_exec P c 0 (cw0,ns,stk) (k,i,(cw1,ns1,stk1)) /\ ~(k = 0)
      ==> rc_call P (CONS c cs) args ns stk (k,cw1 7,ns1))`;;

let RC_EXEC_CASES,RC_CALL_CASES = CONJ_PAIR rc_CASES;;

(* ------------------------------------------------------------------------- *)
(* Equations of the machine.                                                 *)
(* ------------------------------------------------------------------------- *)

let RC_SUBST_VARS_TAC =
  REPEAT(FIRST_X_ASSUM(fun th -> let c = concl th in
     if is_eq c && is_var(lhs c) && is_var(rhs c) then SUBST_ALL_TAC th else failwith ""));;

let RC_OUTC = prove
 (`(!k. ~(rc_outc k = 0)) /\ (!k. rc_outc k = 1 <=> k = 1) /\ (!k. 1 = rc_outc k <=> k = 1)`,
  REWRITE_TAC[rc_outc] THEN REPEAT CONJ_TAC THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC);;

let RC_EXEC_NIL = prove
 (`!P i s r. rc_exec P [] i s r <=> r = (1,i,s)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [RC_EXEC_CASES] THEN
  REWRITE_TAC[NOT_CONS_NIL; GSYM NOT_CONS_NIL] THEN MESON_TAC[]);;

let RC_CALL_NIL = prove
 (`!P args ns stk r. rc_call P [] args ns stk r <=> r = (0,0,ns)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [RC_CALL_CASES] THEN
  REWRITE_TAC[NOT_CONS_NIL; GSYM NOT_CONS_NIL]);;

let RC_EXEC_CONS = prove
 (`!P st sts i cw ns stk r.
   rc_exec P (CONS st sts) i (cw,ns,stk) r <=>
   (val(EL 0 st) < 32 /\
    ?pay ns'. rc_leaf st (cw,ns,stk) 1 pay ns' /\
              rc_exec P sts (i + 1) (pl_set cw (val(EL 17 st)) pay,ns',stk) r) \/
   (val(EL 0 st) < 32 /\
    ?k pay ns'. rc_leaf st (cw,ns,stk) k pay ns' /\ ~(k = 1) /\
                r = (k,i,(pl_set cw (val(EL 17 st)) pay,ns',stk))) \/
   (val(EL 0 st) = 32 /\ val(EL 1 st) < LENGTH P /\
    ?pay ns2.
       rc_call P (EL (val(EL 1 st)) P) (rc_args st cw) ns stk (1,pay,ns2) /\
       rc_exec P sts (i + 1) (pl_set cw (val(EL 17 st)) pay,ns2,stk) r) \/
   (val(EL 0 st) = 32 /\ val(EL 1 st) < LENGTH P /\
    ?k pay ns2.
       rc_call P (EL (val(EL 1 st)) P) (rc_args st cw) ns stk (k,pay,ns2) /\
       ~(k = 1) /\ r = (rc_outc k,i,(pl_set cw (val(EL 17 st)) pay,ns2,stk)))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [RC_EXEC_CASES] THEN
    REWRITE_TAC[NOT_CONS_NIL; CONS_11; PAIR_EQ] THEN STRIP_TAC THEN
    RC_SUBST_VARS_TAC THEN ASM_MESON_TAC[];
    MESON_TAC[rc_RULES]]);;

let RC_CALL_CONS = prove
 (`!P c cs args ns stk r.
     rc_call P (CONS c cs) args ns stk r <=>
     ?cw0 k i cw1 ns1 stk1.
        rc_frame cw0 args /\ rc_exec P c 0 (cw0,ns,stk) (k,i,(cw1,ns1,stk1)) /\
        (if k = 0 then rc_call P cs args ns1 stk r else r = (k,cw1 7,ns1))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [RC_CALL_CASES] THEN
    REWRITE_TAC[NOT_CONS_NIL; CONS_11; PAIR_EQ] THEN STRIP_TAC THEN RC_SUBST_VARS_TAC THENL
     [MAP_EVERY EXISTS_TAC [`cw0:num->num`; `0`; `i:num`; `cw1:num->num`; `ns1:nstate`; `stk1:num list`] THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`cw0:num->num`; `k:num`; `i:num`; `cw1:num->num`; `ns1:nstate`; `stk1:num list`] THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`cw0:num->num`; `k:num`; `i:num`; `cw1:num->num`; `ns1:nstate`; `stk1:num list`] THEN
    ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[rc_RULES]]);;

(* One step: a conditional on the step's first word, each branch in the     *)
(* shape of pl_run's step.                                                  *)
let RC_EXEC_STEP = prove
 (`!P st sts i cw ns stk r.
     rc_exec P (CONS st sts) i (cw,ns,stk) r <=>
     if val(EL 0 st) < 32 then
       ?k pay ns'. rc_leaf st (cw,ns,stk) k pay ns' /\
                   (if k = 1 then rc_exec P sts (i + 1) (pl_set cw (val(EL 17 st)) pay,ns',stk) r
                    else r = (k,i,(pl_set cw (val(EL 17 st)) pay,ns',stk)))
     else if val(EL 0 st) = 32 then
       val(EL 1 st) < LENGTH P /\
       ?k pay ns2.
          rc_call P (EL (val(EL 1 st)) P) (rc_args st cw) ns stk (k,pay,ns2) /\
          (if k = 1 then rc_exec P sts (i + 1) (pl_set cw (val(EL 17 st)) pay,ns2,stk) r
           else r = (rc_outc k,i,(pl_set cw (val(EL 17 st)) pay,ns2,stk)))
     else F`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [RC_EXEC_CONS] THEN
  ASM_CASES_TAC `val(EL 0 (st:int64 list)) < 32` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~(val(EL 0 (st:int64 list)) = 32)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    EQ_TAC THENL
     [STRIP_TAC THENL
       [MAP_EVERY EXISTS_TAC [`1`; `pay:num`; `ns':nstate`] THEN ASM_REWRITE_TAC[];
        MAP_EVERY EXISTS_TAC [`k:num`; `pay:num`; `ns':nstate`] THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `pay:num` (X_CHOOSE_THEN `ns':nstate` MP_TAC))) THEN
      ASM_CASES_TAC `k = 1` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ASM_CASES_TAC `val(EL 0 (st:int64 list)) = 32` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `val(EL 1 (st:int64 list)) < LENGTH (P:(((int64 list)list)list)list)` THEN
    ASM_REWRITE_TAC[] THEN
    EQ_TAC THENL
     [STRIP_TAC THENL
       [MAP_EVERY EXISTS_TAC [`1`; `pay:num`; `ns2:nstate`] THEN ASM_REWRITE_TAC[];
        MAP_EVERY EXISTS_TAC [`k:num`; `pay:num`; `ns2:nstate`] THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
      ASM_CASES_TAC `k = 1` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]]);;

(* A plan without comparison or call steps runs on the recipe machine as on *)
(* the plan machine.                                                         *)
let RC_EXEC_PL_RUN = prove
 (`!p P i s r. ALL (\st. val(EL 0 st) < 25) p ==> (rc_exec P p i s r <=> pl_run p i s r)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; RC_EXEC_NIL; pl_run] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[RC_EXEC_STEP; FST; SND] THEN
  SUBGOAL_THEN `!s k pay ns'. rc_leaf h s k pay ns' <=> pl_leaf h s k pay ns'`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FORALL_PAIR_THM; rc_leaf] THEN REPEAT GEN_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `x < 25 ==> ~(x = 25)`];
    ASM_SIMP_TAC[ARITH_RULE `x < 25 ==> x < 32`]]);;

(* ------------------------------------------------------------------------- *)
(* Footprints: a run appends rows only to the tables its steps write.       *)
(* ------------------------------------------------------------------------- *)

(* The tables a step writes: type rows (intern16 at slot 0), de Bruijn rows *)
(* (intern16 at slot 6, hyps_union), theorem rows (append_row).             *)
let rc_wty = new_definition
 `rc_wty (st:int64 list) <=> val(EL 0 st) = 0 /\ val(EL 1 st) = 0`;;
let rc_wdb = new_definition
 `rc_wdb (st:int64 list) <=> val(EL 0 st) = 0 /\ val(EL 1 st) = 6 \/ val(EL 0 st) = 7`;;
let rc_wth = new_definition
 `rc_wth (st:int64 list) <=> val(EL 0 st) = 6`;;

(* ns' is ns with rows appended to the tables the flags allow; distinct    *)
(* keys and the row bounds are kept.                                        *)
let rc_grows = new_definition
 `rc_grows ((wt,wd,wh):bool#bool#bool)
           ((ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate) (ns':nstate) <=>
    ?mt md mh.
      ns' = (ctx,nms,(if wt then APPEND tys mt else tys),ntms,
             (if wd then APPEND dbs md else dbs),(if wh then APPEND ths mh else ths),
             nmap,ymap,drops,pol) /\
      (keys_distinct tys ==> keys_distinct (APPEND tys mt)) /\
      (keys_distinct dbs ==> keys_distinct (APPEND dbs md)) /\
      (LENGTH tys < 2 EXP 60 ==> LENGTH (APPEND tys mt) < 2 EXP 60) /\
      (LENGTH dbs < 2 EXP 60 ==> LENGTH (APPEND dbs md) < 2 EXP 60) /\
      (LENGTH ths < 2 EXP 60 ==> LENGTH (APPEND ths mh) < 2 EXP 60)`;;

let rc_sub = new_definition
 `rc_sub ((wt,wd,wh):bool#bool#bool) ((wt',wd',wh'):bool#bool#bool) <=>
    (wt ==> wt') /\ (wd ==> wd') /\ (wh ==> wh')`;;

(* Case analysis on a flag, in the goal and in every assumption. *)
let RC_FLAG_CASES_TAC v =
  ASM_CASES_TAC v THEN POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ASM_REWRITE_TAC[];;

let RC_GROWS_REFL_X = prove
 (`!wt wd wh ctx nms tys ntms dbs ths nmap ymap drops pol.
     rc_grows (wt,wd,wh) (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
                         (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rc_grows] THEN
  MAP_EVERY EXISTS_TAC [`[]:(num#num#num)list`; `[]:(num#num#num)list`; `[]:(num#num)list`] THEN
  REWRITE_TAC[APPEND_NIL; COND_ID]);;

let RC_GROWS_TRANS_X = prove
 (`!wt wd wh ctx nms tys ntms dbs ths nmap ymap drops pol ns2 ns3.
     rc_grows (wt,wd,wh) (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) ns2 /\
     rc_grows (wt,wd,wh) ns2 ns3
     ==> rc_grows (wt,wd,wh) (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) ns3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rc_grows] THEN
  DISCH_THEN(fun th -> MP_TAC(CONJUNCT2 th) THEN MP_TAC(CONJUNCT1 th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `mt:(num#num#num)list` (X_CHOOSE_THEN `md:(num#num#num)list`
      (X_CHOOSE_THEN `mh:(num#num)list` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)))) THEN
  REWRITE_TAC[rc_grows] THEN
  DISCH_THEN(X_CHOOSE_THEN `mt':(num#num#num)list` (X_CHOOSE_THEN `md':(num#num#num)list`
      (X_CHOOSE_THEN `mh':(num#num)list` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC
   [`if wt then APPEND mt mt' else []:(num#num#num)list`;
    `if wd then APPEND md md' else []:(num#num#num)list`;
    `if wh then APPEND mh mh' else []:(num#num)list`] THEN
  MAP_EVERY RC_FLAG_CASES_TAC [`wt:bool`; `wd:bool`; `wh:bool`] THEN
  REWRITE_TAC[APPEND_NIL; APPEND_ASSOC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[APPEND_ASSOC]) THEN ASM_MESON_TAC[]);;

let RC_GROWS_SUB_X = prove
 (`!wt wd wh wt' wd' wh' ctx nms tys ntms dbs ths nmap ymap drops pol ns'.
     ((wt ==> wt') /\ (wd ==> wd') /\ (wh ==> wh')) /\
     rc_grows (wt,wd,wh) (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) ns'
     ==> rc_grows (wt',wd',wh') (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) ns'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rc_grows] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (X_CHOOSE_THEN `mt:(num#num#num)list` (X_CHOOSE_THEN `md:(num#num#num)list`
      (X_CHOOSE_THEN `mh:(num#num)list` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC))))) THEN
  MAP_EVERY EXISTS_TAC
   [`if wt then mt else []:(num#num#num)list`;
    `if wd then md else []:(num#num#num)list`;
    `if wh then mh else []:(num#num)list`] THEN
  MAP_EVERY RC_FLAG_CASES_TAC [`wt:bool`; `wd:bool`; `wh:bool`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN ASM_REWRITE_TAC[APPEND_NIL] THEN ASM_MESON_TAC[]);;

let RC_GROWS_REFL = prove
 (`!w ns. rc_grows w ns ns`,
  REWRITE_TAC[FORALL_PAIR_THM; RC_GROWS_REFL_X]);;

let RC_GROWS_TRANS = prove
 (`!w ns1 ns2 ns3. rc_grows w ns1 ns2 /\ rc_grows w ns2 ns3 ==> rc_grows w ns1 ns3`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN MESON_TAC[RC_GROWS_TRANS_X]);;

let RC_GROWS_SUB = prove
 (`!w w' ns ns'. rc_sub w w' /\ rc_grows w ns ns' ==> rc_grows w' ns ns'`,
  REWRITE_TAC[FORALL_PAIR_THM; rc_sub] THEN MESON_TAC[RC_GROWS_SUB_X]);;

(* ------------------------------------------------------------------------- *)
(* Interning: what one intern step keeps (also used by the cells below).    *)
(* ------------------------------------------------------------------------- *)

let PL_INTERNED_KEYS = prove
 (`!(D:(num#num#num)list) key pay md.
     keys_distinct D /\ pl_interned D key pay md ==> keys_distinct (APPEND D md)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_interned] THEN STRIP_TAC THEN ASM_REWRITE_TAC[APPEND_NIL] THEN
  MATCH_MP_TAC KEYS_DISTINCT_SNOC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MEM_EL]);;

let PL_INTERNED_LEN = prove
 (`!(D:(num#num#num)list) key pay md.
     LENGTH D < 2 EXP 60 /\ pl_interned D key pay md ==> LENGTH (APPEND D md) < 2 EXP 60`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_interned] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[APPEND_NIL; LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC);;

let PL_INTERNED_ROW = prove
 (`!(D:(num#num#num)list) key pay md.
     pl_interned D key pay md ==> pay < LENGTH (APPEND D md) /\ EL pay (APPEND D md) = key`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_interned] THEN STRIP_TAC THEN ASM_REWRITE_TAC[APPEND_NIL] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; EL_APPEND; LT_REFL; SUB_REFL; EL; HD] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The frame of one step, and of every run.                                  *)
(* ------------------------------------------------------------------------- *)

let PL_INTERN_GROWS = prove
 (`!rows a0 a1 k pay rows'.
     pl_intern rows a0 a1 k pay rows'
     ==> ?m. rows' = APPEND rows m /\ (keys_distinct rows ==> keys_distinct rows') /\
             (LENGTH rows < 2 EXP 60 ==> LENGTH rows' < 2 EXP 60)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_intern] THEN STRIP_TAC THENL
   [EXISTS_TAC `md:(num#num#num)list` THEN ASM_MESON_TAC[PL_INTERNED_KEYS; PL_INTERNED_LEN];
    EXISTS_TAC `[]:(num#num#num)list` THEN ASM_REWRITE_TAC[APPEND_NIL]]);;

let PL_APPEND_GROWS = prove
 (`!ths a b k pay ths'.
     pl_append_th ths 2 a b k pay ths'
     ==> ?m. ths' = APPEND ths m /\ (LENGTH ths < 2 EXP 60 ==> LENGTH ths' < 2 EXP 60)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_append_th] THEN STRIP_TAC THENL
   [EXISTS_TAC `[a,b]:(num#num)list` THEN ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC;
    EXISTS_TAC `[]:(num#num)list` THEN ASM_REWRITE_TAC[APPEND_NIL]]);;

let PL_UNION_GROWS = prove
 (`!dbs a b k pay dbs'.
     pl_union dbs a b k pay dbs'
     ==> ?m. dbs' = APPEND dbs m /\ (keys_distinct dbs ==> keys_distinct dbs') /\
             (LENGTH dbs < 2 EXP 60 ==> LENGTH dbs' < 2 EXP 60)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_union] THEN STRIP_TAC THEN
  EXISTS_TAC `md:(num#num#num)list` THEN ASM_MESON_TAC[]);;

(* The suffixes a goal  ?mt md mh. ns = (..) /\ ..  needs: the appended    *)
(* lists of its state's tables, [] for a table left as it was.             *)
let RC_GROWS_WITNESS_TAC (asl,w as g) =
  let _,b1 = dest_exists w in let _,b2 = dest_exists b1 in let _,b3 = dest_exists b2 in
  let nil ty = mk_const("NIL",[ty,`:A`]) in
  let ws =
    try let eq = find (fun c -> is_eq c && is_pair(lhs c)) (conjuncts b3) in
        let comps = striplist dest_pair (lhs eq) in
        let suffix c ty =
          match strip_comb c with
            (f,[_;m]) when is_const f && fst(dest_const f) = "APPEND" -> m
          | _ -> nil ty in
        [suffix (el 2 comps) `:num#num#num`; suffix (el 4 comps) `:num#num#num`;
         suffix (el 5 comps) `:num#num`]
    with Failure _ -> [nil `:num#num#num`; nil `:num#num#num`; nil `:num#num`] in
  MAP_EVERY EXISTS_TAC ws g;;

let RC_LEAF_GROWS_X = prove
 (`!st cw ctx nms tys ntms dbs ths nmap ymap drops pol stk k pay ns'.
     rc_leaf st (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) k pay ns' /\
     (val(EL 0 st) = 6 ==> cw(val(EL 12 st)) = 2)
     ==> rc_grows (rc_wty st,rc_wdb st,rc_wth st) (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) ns'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rc_leaf; pl_leaf; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) MP_TAC) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN TRY DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> W(fun (asl,_) ->
    let c = concl th in
    if is_const_app "pl_intern" c then MP_TAC(MATCH_MP PL_INTERN_GROWS th)
    else if is_const_app "pl_union" c then MP_TAC(MATCH_MP PL_UNION_GROWS th)
    else if is_const_app "pl_append_th" c then
      MP_TAC(MATCH_MP PL_APPEND_GROWS (REWRITE_RULE (map snd asl) th))
    else failwith "")) THEN
    DISCH_THEN(CHOOSE_THEN (fun th -> STRIP_ASSUME_TAC(CONJUNCT2 th) THEN
                                      SUBST_ALL_TAC(CONJUNCT1 th)))) THEN
  ASM_REWRITE_TAC[rc_wty; rc_wdb; rc_wth; ARITH_EQ; rc_grows] THEN
  RC_GROWS_WITNESS_TAC THEN ASM_REWRITE_TAC[APPEND_NIL]);;

let RC_LEAF_GROWS = prove
 (`!st cw ns stk k pay ns'.
     rc_leaf st (cw,ns,stk) k pay ns' /\ (val(EL 0 st) = 6 ==> cw(val(EL 12 st)) = 2)
     ==> rc_grows (rc_wty st,rc_wdb st,rc_wth st) ns ns'`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN MESON_TAC[RC_LEAF_GROWS_X]);;

(* A step allowed in recipes of the table: it writes a temporary (above the *)
(* constants), appends theorems with stride 2, writes only the tables the  *)
(* flags allow, and calls only recipes of the index set R.                  *)
let rc_step_in = new_definition
 `rc_step_in (R:num->bool) ((wt,wd,wh):bool#bool#bool) (st:int64 list) <=>
    6 < val(EL 17 st) /\ (val(EL 0 st) = 6 ==> val(EL 12 st) = 2) /\
    (rc_wty st ==> wt) /\ (rc_wdb st ==> wd) /\ (rc_wth st ==> wh) /\
    (val(EL 0 st) = 32 ==> R(val(EL 1 st)))`;;

(* R is closed: its recipes are in P and their steps are allowed. *)
let rc_closed = new_definition
 `rc_closed (P:(((int64 list)list)list)list) (R:num->bool) (w:bool#bool#bool) <=>
    !r. R r ==> r < LENGTH P /\ ALL (ALL (rc_step_in R w)) (EL r P)`;;

(* A step keeps control words 0..6. *)
let PL_SET_LOW_LEMMA = prove
 (`!f p v n. n <= 6 /\ 6 < p ==> pl_set f p v n = (f:num->num) n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_set] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let RC_STEP_GROWS = prove
 (`!R wt wd wh st cw ns stk k pay ns'.
     rc_step_in R (wt,wd,wh) st /\ (!n. n <= 6 ==> cw n = n) /\
     rc_leaf st (cw,ns,stk) k pay ns'
     ==> rc_grows (wt,wd,wh) ns ns' /\
         (!n. n <= 6 ==> pl_set cw (val(EL 17 st)) pay n = n)`,
  REWRITE_TAC[rc_step_in] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC RC_GROWS_SUB THEN
    EXISTS_TAC `(rc_wty st,rc_wdb st,rc_wth st)` THEN ASM_REWRITE_TAC[rc_sub] THEN
    MATCH_MP_TAC RC_LEAF_GROWS THEN
    MAP_EVERY EXISTS_TAC [`cw:num->num`; `stk:num list`; `k:num`; `pay:num`] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
      can (find_term ((=) `12`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[ARITH_RULE `2 <= 6`];
    ASM_SIMP_TAC[PL_SET_LOW_LEMMA]]);;

(* RC_GROWS_RUN: every run of a clause, and every call, of a closed set of *)
(* recipes grows the store within the set's footprint.                     *)
let RC_LOW_SET = prove
 (`!R w st cw pay. rc_step_in R w st /\ (!n. n <= 6 ==> cw n = n)
                   ==> !n. n <= 6 ==> pl_set cw (val(EL 17 st)) pay n = n`,
  REWRITE_TAC[FORALL_PAIR_THM; rc_step_in] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[PL_SET_LOW_LEMMA]);;

let RC_CLOSED_CALLEE = prove
 (`!P R wt wd wh st. rc_closed P R (wt,wd,wh) /\ rc_step_in R (wt,wd,wh) st /\ val(EL 0 st) = 32
                     ==> ALL (ALL (rc_step_in R (wt,wd,wh))) (EL (val(EL 1 st)) P)`,
  REWRITE_TAC[rc_closed] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `val(EL 1 (st:int64 list))`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[rc_step_in]) THEN ASM_MESON_TAC[]);;

let has_const name tm = can (find_term (fun t -> is_const t && fst(dest_const t) = name)) tm;;
let RC_RUN_LEAF_FIRED_TAC =
  MP_TAC(SPECL [`R:num->bool`; `wt:bool`; `wd:bool`; `wh:bool`; `st:int64 list`; `cw:num->num`;
                `ns:nstate`; `stk:num list`; `1`; `pay:num`; `ns':nstate`] RC_STEP_GROWS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC RC_GROWS_TRANS THEN EXISTS_TAC `ns':nstate` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];;
let RC_RUN_LEAF_STOPPED_TAC =
  MP_TAC(SPECL [`R:num->bool`; `wt:bool`; `wd:bool`; `wh:bool`; `st:int64 list`; `cw:num->num`;
                `ns:nstate`; `stk:num list`; `k:num`; `pay:num`; `ns':nstate`] RC_STEP_GROWS) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[];;
let RC_RUN_CALLEE_TAC =
  SUBGOAL_THEN `ALL (ALL (rc_step_in R (wt,wd,wh))) (EL (val (EL 1 (st:int64 list))) (P:(((int64 list)list)list)list))`
    ASSUME_TAC THENL [MATCH_MP_TAC RC_CLOSED_CALLEE THEN ASM_REWRITE_TAC[]; ALL_TAC];;
let RC_RUN_CALL_FIRED_TAC =
  RC_RUN_CALLEE_TAC THEN
  MATCH_MP_TAC RC_GROWS_TRANS THEN EXISTS_TAC `ns2:nstate` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp(concl th) && has_const "EL" (lhand(concl th)))) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp(concl th) && has_const "pl_set" (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RC_LOW_SET THEN ASM_MESON_TAC[]];;
let RC_RUN_CALL_STOPPED_TAC =
  RC_RUN_CALLEE_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];;
let RC_RUN_CLAUSE_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[rc_frame]) THEN
  (FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] ORELSE
   (MATCH_MP_TAC RC_GROWS_TRANS THEN EXISTS_TAC `ns1:nstate` THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]));;

let RC_GROWS_RUN = prove
 (`!P R wt wd wh.
     rc_closed P R (wt,wd,wh)
     ==> (!c i cw ns stk k i' cw' ns' stk'.
            rc_exec P c i (cw,ns,stk) (k,i',(cw',ns',stk')) /\
            ALL (rc_step_in R (wt,wd,wh)) c /\ (!n. n <= 6 ==> cw n = n)
            ==> rc_grows (wt,wd,wh) ns ns') /\
         (!cls args ns stk k pay ns'.
            rc_call P cls args ns stk (k,pay,ns') /\ ALL (ALL (rc_step_in R (wt,wd,wh))) cls
            ==> rc_grows (wt,wd,wh) ns ns')`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\P' (c:(int64 list)list) (i:num) (s:pstate) (r:num#num#pstate).
       P' = (P:(((int64 list)list)list)list) ==>
       ALL (rc_step_in R (wt,wd,wh)) c /\ (!n. n <= 6 ==> FST s n = n) ==>
       rc_grows (wt,wd,wh) (FST(SND s)) (FST(SND(SND(SND r))))`;
    `\P' (cls:((int64 list)list)list) (args:num list) (ns:nstate) (stk:num list) (r:num#num#nstate).
       P' = (P:(((int64 list)list)list)list) ==>
       ALL (ALL (rc_step_in R (wt,wd,wh))) cls ==> rc_grows (wt,wd,wh) ns (SND(SND r))`]
   rc_INDUCT) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND; ALL] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
    REPEAT(DISCH_THEN(fun th -> if is_eq(concl th) && is_var(lhs(concl th)) && is_var(rhs(concl th))
                                then SUBST_ALL_TAC th else STRIP_ASSUME_TAC th)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN REWRITE_TAC[RC_GROWS_REFL] THEN
    FIRST (map (fun t -> t THEN NO_TAC)
                [RC_RUN_LEAF_FIRED_TAC; RC_RUN_LEAF_STOPPED_TAC; RC_RUN_CALL_FIRED_TAC;
                 RC_RUN_CALL_STOPPED_TAC; RC_RUN_CLAUSE_TAC]);
    DISCH_THEN(fun th -> CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
      [MP_TAC(SPECL [`P:(((int64 list)list)list)list`; `c:(int64 list)list`; `i:num`;
                     `(cw,ns,stk):pstate`; `(k,i',(cw',ns',stk')):num#num#pstate`] (CONJUNCT1 th));
       MP_TAC(SPECL [`P:(((int64 list)list)list)list`; `cls:((int64 list)list)list`; `args:num list`;
                     `ns:nstate`; `stk:num list`; `(k,pay,ns'):num#num#nstate`] (CONJUNCT2 th))] THEN
      ASM_REWRITE_TAC[FST; SND])]);;

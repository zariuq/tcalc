(* ========================================================================= *)
(* The sorted union of two id lists as a recipe: recipe 1 of the table.     *)
(*                                                                           *)
(* RC_UNION_FRAME: a call appends only de Bruijn rows (keys kept distinct,   *)
(* the bound kept).                                                          *)
(* RC_UNION_LEAF: a FIRED call gives what the union leaf's contract          *)
(* (plans_abs.ml, pl_union) promises for any two sorted lists at its         *)
(* arguments: a sorted list row holding exactly their elements, and new rows *)
(* that are list cells over them.                                            *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* List cells.                                                               *)
(* ------------------------------------------------------------------------- *)

let PL_IDS_INTERNED = prove
 (`!D a r pay md ids.
     pl_interned D (6,a,r) pay md /\ pl_ids D r ids ==> pl_ids (APPEND D md) pay (CONS a ids)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_ids] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_INTERNED_ROW) THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `r:num` THEN REWRITE_TAC[] THEN MATCH_MP_TAC PL_IDS_APPEND THEN ASM_REWRITE_TAC[]);;

let PL_CELLS_NEW_REFL = prove
 (`!c D ok. pl_cells_new c (LENGTH D) D ok`,
  REWRITE_TAC[pl_cells_new] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

let PL_CELLS_NEW_MONO = prove
 (`!c n0 D ok ok'. pl_cells_new c n0 D ok /\ (!a. ok a ==> ok' a) ==> pl_cells_new c n0 D ok'`,
  REWRITE_TAC[pl_cells_new] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> rc_has "EL" (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `b:num` (X_CHOOSE_THEN `ids:num list` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`a:num`; `b:num`; `ids:num list`] THEN ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `ALL (ok:num->bool) ids` THEN REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[]);;

let PL_CELLS_NEW_INTERNED = prove
 (`!n0 D ok a r pay md ids.
     pl_cells_new 6 n0 D ok /\ pl_interned D (6,a,r) pay md /\
     a < LENGTH D /\ ok a /\ pl_ids D r ids /\ ALL ok ids
     ==> pl_cells_new 6 n0 (APPEND D md) ok`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_interned] THEN STRIP_TAC THEN ASM_REWRITE_TAC[APPEND_NIL] THEN
  REWRITE_TAC[pl_cells_new; LENGTH_APPEND; LENGTH] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `i < LENGTH (D:(num#num#num)list)` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o REWRITE_RULE[pl_cells_new] o
                  check (fun th -> is_const_app "pl_cells_new" (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a':num` (X_CHOOSE_THEN `b':num` (X_CHOOSE_THEN `ids':num list` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`a':num`; `b':num`; `ids':num list`] THEN
    ASM_SIMP_TAC[EL_APPEND; PL_IDS_APPEND];
    SUBGOAL_THEN `i = LENGTH (D:(num#num#num)list)` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`a:num`; `r:num`; `ids:num list`] THEN
    ASM_SIMP_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD; PL_IDS_APPEND] THEN
    ASM_MESON_TAC[PL_IDS_BOUND]]);;

let PL_SORTED_CONS = prove
 (`!a ids. PAIRWISE (<) ids /\ (!x. MEM x ids ==> a < x) ==> PAIRWISE (<) (CONS a ids)`,
  REWRITE_TAC[PAIRWISE; GSYM ALL_MEM] THEN MESON_TAC[]);;

(* One interned cell on top of a list the run has built. *)
let PL_CELL_CHAIN = prove
 (`!D a r pay md. pl_interned D (6,a,r) pay md
     ==> !ids. pl_ids D r ids
     ==> !n0 ok'. pl_cells_new 6 n0 D ok'
     ==> !ok. a < LENGTH D /\ ok a /\ (!x. ok' x ==> ok x) /\ (!x. MEM x ids ==> ok x)
              ==> pl_cells_new 6 n0 (APPEND D md) ok /\ pl_ids (APPEND D md) pay (CONS a ids)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC PL_CELLS_NEW_INTERNED THEN
    MAP_EVERY EXISTS_TAC [`a:num`; `r:num`; `pay:num`; `ids:num list`] THEN
    ASM_REWRITE_TAC[GSYM ALL_MEM] THEN MATCH_MP_TAC PL_CELLS_NEW_MONO THEN
    EXISTS_TAC `ok':num->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_IDS_INTERNED THEN EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Steps of recipes.                                                          *)
(* ------------------------------------------------------------------------- *)

let rc_UNION = 1;;
let rc_relw a b m res = pl_step 25 [] a b [m] res;;
let rc_callstep r args res =
  let rec pad l n x = if length l >= n then l else pad (l @ [x]) n x in
  let ws = [32; r] @ pad [] 8 pl_nul @ pad args 7 0 @ [res] in
  mk_list(map (fun n -> mk_comb(`word:num->int64`, mk_small_numeral n)) ws, `:int64`);;
let db_w0 l res = pl_step 4 [6;10] l 0 [2] res;;       (* word 0 of row l (FIRED iff l is a row) *)
let db_w1 l res = pl_step 4 [6;10] l 1 [2] res;;       (* word 1 of row l *)
let rc_unpack k tag res = pl_step 2 [] k tag [] res;;  (* the field of a word of that tag *)
let rc_move a res = pl_step 3 [] a a [] res;;
let rc_eqw a b res = pl_step 3 [] a b [] res;;
let rc_intern_db k0 k1 res = pl_step 0 [6;8;10] k0 k1 [] res;;
let rc_clause steps = mk_list(steps, `:int64 list`);;
let rc_recipe clauses = mk_list(clauses, `:(int64 list)list`);;

(* union l1 l2 (word 8, word 9), by cases on the heads: [] and l2; a::_ and *)
(* []; a::t1 and a::t2; a::t1 and b::_ with a < b; and with b < a. A head   *)
(* is checked to be a row (word 0 of it read) before a cell holds it.       *)
let rc_union = new_definition(mk_eq(`rc_union:((int64 list)list)list`, rc_recipe
 [rc_clause [db_w0 8 24; rc_unpack 24 5 25; rc_move 9 7];
  rc_clause [db_w0 8 24; rc_unpack 24 6 25; db_w0 9 26; rc_unpack 26 5 27; rc_move 8 7];
  rc_clause [db_w0 8 24; rc_unpack 24 6 25; db_w0 9 26; rc_unpack 26 6 27;
             rc_eqw 25 27 28; db_w0 25 32; db_w1 8 29; db_w1 9 30;
             rc_callstep rc_UNION [29; 30] 31; rc_intern_db 24 31 7];
  rc_clause [db_w0 8 24; rc_unpack 24 6 25; db_w0 9 26; rc_unpack 26 6 27;
             rc_relw 25 27 1 28; db_w0 25 32; db_w1 8 29;
             rc_callstep rc_UNION [29; 9] 31; rc_intern_db 24 31 7];
  rc_clause [db_w0 8 24; rc_unpack 24 6 25; db_w0 9 26; rc_unpack 26 6 27;
             rc_relw 25 27 4 28; db_w0 27 32; db_w1 9 30;
             rc_callstep rc_UNION [8; 30] 31; rc_intern_db 26 31 7]]));;

(* ------------------------------------------------------------------------- *)
(* The frame of a union call.                                                 *)
(* ------------------------------------------------------------------------- *)

let RC_STEPS_CONV =
  REWRITE_CONV[ALL; rc_step_in; rc_wty; rc_wdb; rc_wth] THENC DEPTH_CONV BETA_CONV THENC
  PL_NORM_CONV THENC REWRITE_CONV[] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[];;

let RC_UNION_IN = prove
 (`ALL (ALL (rc_step_in (\r. r = 1) (F,T,F))) rc_union`,
  CONV_TAC(REWRITE_CONV[rc_union] THENC RC_STEPS_CONV));;

let RC_UNION_CLOSED = prove
 (`!P. 1 < LENGTH P /\ EL 1 P = rc_union ==> rc_closed P (\r. r = 1) (F,T,F)`,
  REWRITE_TAC[rc_closed] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC[RC_UNION_IN]);;

let RC_UNION_FRAME = prove
 (`!P args ctx nms tys ntms dbs ths nmap ymap drops pol stk k pay ns'.
     1 < LENGTH P /\ EL 1 P = rc_union /\
     rc_call P rc_union args (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) stk (k,pay,ns')
     ==> ?md. ns' = (ctx,nms,tys,ntms,APPEND dbs md,ths,nmap,ymap,drops,pol) /\
              (keys_distinct dbs ==> keys_distinct (APPEND dbs md)) /\
              (LENGTH dbs < 2 EXP 60 ==> LENGTH (APPEND dbs md) < 2 EXP 60)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `rc_closed P (\r:num. r = 1) (F,T,F)` MP_TAC THENL
   [MATCH_MP_TAC RC_UNION_CLOSED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o MATCH_MP (SPECL [`P:(((int64 list)list)list)list`; `\r:num. r = 1`;
                                                  `F`; `T`; `F`] RC_GROWS_RUN)) THEN
  DISCH_THEN(MP_TAC o SPECL [`rc_union`; `args:num list`;
    `(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate`; `stk:num list`;
    `k:num`; `pay:num`; `ns':nstate`]) THEN
  ASM_REWRITE_TAC[RC_UNION_IN; rc_grows] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The contract of a FIRED union call.                                       *)
(* ------------------------------------------------------------------------- *)

let RC_SET_TAC (asl,w as g) =
  let rel th = let c = concl th in
       not(is_const_app "rc_hide" c) && not(rc_has "pl_cells_new" c) &&
       (rc_has "MEM" c || rc_is_order_lit c) in
  let ths = filter rel (map snd asl) in
  (CONV_TAC(DEPTH_CONV BETA_CONV) THEN MAP_EVERY MP_TAC ths THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[MEM] THEN MESON_TAC[LT_TRANS]) g;;
let RC_EARLIER_TAC =
  REWRITE_TAC[LENGTH_APPEND] THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (MATCH_MP_TAC(ARITH_RULE `a < l ==> a < l + m`) THEN FIRST_ASSUM ACCEPT_TAC) ORELSE
   (MATCH_MP_TAC(ARITH_RULE `a < l ==> a < l + m + n`) THEN FIRST_ASSUM ACCEPT_TAC));;
(* A branch that ends by interning a cell (6,a,r) onto a list the run built. *)
let RC_CELL_TAC =
  FIRST_ASSUM(fun i -> if is_const_app "pl_interned" (concl i) then
    FIRST_ASSUM(fun d -> FIRST_ASSUM(fun c ->
       MP_TAC(MATCH_MP (MATCH_MP (MATCH_MP PL_CELL_CHAIN i) d) c)))
    else failwith "RC_CELL_TAC") THEN
  W(fun (_,w) -> let ok = rand(find_term (fun t -> is_const_app "pl_cells_new" t &&
                                                     length(snd(strip_comb t)) = 4) (rand w)) in
                 DISCH_THEN(MP_TAC o SPEC ok)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RC_EARLIER_TAC ORELSE RC_SET_TAC);
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> if is_const_app "pl_ids" (concl th) && is_cons(rand(concl th)) &&
                             rc_has "APPEND" (concl th)
                          then EXISTS_TAC (rand(concl th)) else failwith "ids") THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_SORTED_CONS THEN ASM_REWRITE_TAC[] THEN RC_SET_TAC; RC_SET_TAC]];;
let RC_IDS_WITNESS_TAC (asl,w as g) =
  let _,body = dest_exists w in
  let pargs = snd(strip_comb(hd(conjuncts body))) in
  let th = find (fun th -> let c = concl th in is_const_app "pl_ids" c &&
                           (let args = snd(strip_comb c) in
                            length args = 3 && el 0 args = el 0 pargs && el 1 args = el 1 pargs))
                (map snd asl) in
  EXISTS_TAC (rand(concl th)) g;;
(* A branch of a list-building recipe: an interned cell, or a list given. *)
let RC_LIST_CLOSE_TAC =
  RC_CELL_TAC ORELSE
  (CONJ_TAC THENL
    [RC_IDS_WITNESS_TAC THEN ASM_REWRITE_TAC[MEM] THEN TRY RC_SET_TAC;
     REWRITE_TAC[PL_CELLS_NEW_REFL]]);;

let rc_union_goal =
 `!n I1 I2 P ctx nms tys ntms dbs ths nmap ymap drops pol stk l1 l2 a2 a3 a4 a5 a6 pay
     ctx' nms' tys' ntms' dbs' ths' nmap' ymap' drops' pol'.
   LENGTH I1 + LENGTH I2 = n /\ 1 < LENGTH P /\ EL 1 P = rc_union /\
   pl_ids dbs l1 I1 /\ pl_ids dbs l2 I2 /\ PAIRWISE (<) I1 /\ PAIRWISE (<) I2 /\
   rc_call P rc_union [l1; l2; a2; a3; a4; a5; a6] (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) stk
           (1,pay,(ctx',nms',tys',ntms',dbs',ths',nmap',ymap',drops',pol'))
   ==> (?ids. pl_ids dbs' pay ids /\ PAIRWISE (<) ids /\ (!x. MEM x ids <=> MEM x I1 \/ MEM x I2)) /\
       pl_cells_new 6 (LENGTH dbs) dbs' (\a. MEM a I1 \/ MEM a I2)`;;

let RC_UNION = prove(rc_union_goal,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC [`a:num`; `t1:num list`] THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
     [ALL_TAC; MAP_EVERY X_GEN_TAC [`b:num`; `t2:num list`] THEN DISCH_THEN(K ALL_TAC)]] THEN
  RC_CERT_START_TAC rc_union [pl_ids; PAIRWISE; LENGTH; GSYM ALL_MEM] THEN
  RC_RUN_TAC [RC_UNION_FRAME] [] THEN RC_LIST_CLOSE_TAC);;

(* The contract, as the union leaf's: for any two sorted lists at the       *)
(* arguments, a sorted list row of exactly their elements, new rows cells.  *)
let rc_union_post = new_definition
 `rc_union_post (dbs:(num#num#num)list) l1 l2 pay (dbs':(num#num#num)list) <=>
    !I1 I2. pl_ids dbs l1 I1 /\ pl_ids dbs l2 I2 /\ PAIRWISE (<) I1 /\ PAIRWISE (<) I2
            ==> (?ids. pl_ids dbs' pay ids /\ PAIRWISE (<) ids /\
                       (!x. MEM x ids <=> MEM x I1 \/ MEM x I2)) /\
                pl_cells_new 6 (LENGTH dbs) dbs' (\a. MEM a I1 \/ MEM a I2)`;;

let RC_UNION_LEAF = prove
 (`!P l1 l2 a2 a3 a4 a5 a6 ctx nms tys ntms dbs ths nmap ymap drops pol stk pay
     ctx' nms' tys' ntms' dbs' ths' nmap' ymap' drops' pol'.
     1 < LENGTH P /\ EL 1 P = rc_union /\
     rc_call P rc_union [l1; l2; a2; a3; a4; a5; a6] (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) stk
             (1,pay,(ctx',nms',tys',ntms',dbs',ths',nmap',ymap',drops',pol'))
     ==> rc_union_post dbs l1 l2 pay dbs'`,
  REWRITE_TAC[rc_union_post] THEN REPEAT(GEN_TAC ORELSE DISCH_TAC) THEN
  MP_TAC(SPEC_ALL(SPECL [`LENGTH (I1:num list) + LENGTH (I2:num list)`; `I1:num list`; `I2:num list`]
                        RC_UNION)) THEN
  ASM_REWRITE_TAC[]);;

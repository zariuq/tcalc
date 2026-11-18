(* Closure of the binding walk's interned row constructors. *)
needs "native/hol/holfibre_rows.ml";;

let bw_key_ok = new_definition
 `bw_key_ok i ((tag,a,b):num#num#num) <=>
    tag = 0 \/ tag = 1 /\ b = 0 \/ tag = 2 \/
    tag = 3 /\ a < i /\ b < i \/ tag = 4 /\ b < i \/
    tag = 5 /\ a = 0 /\ b = 0 \/ tag = 6 /\ a < i /\ b < i`;;

let bw_rows_valid = new_definition
 `bw_rows_valid nms tys (D:(num#num#num)list) <=>
    (!i. i < LENGTH D ==> bw_key_ok i (EL i D)) /\
    (!i. i < LENGTH D ==> (?t. fddb nms tys D i t) \/ (?l. fddbs nms tys D i l))`;;

let bw_row_admissible = new_definition
 `bw_row_admissible nms tys (D:(num#num#num)list) row <=>
    bw_key_ok (LENGTH D) row /\
    ?t. fddb nms tys (APPEND D [row]) (LENGTH D) t`;;

let BW_STORE_FDDB_BOUND = prove
 (`!nms tys D i t. fddb nms tys D i t ==> i < LENGTH D`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[fddb_CASES] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let BW_LIST_GROW_ONE = prove
 (`!(D:A list) D' row pay.
     (LENGTH D' = LENGTH D \/ LENGTH D' = LENGTH D + 1) /\
     (!i. i < LENGTH D ==> EL i D' = EL i D) /\
     pay < LENGTH D' /\ EL pay D' = row /\
     (LENGTH D' = LENGTH D \/ pay = LENGTH D)
     ==> D' = D \/ D' = APPEND D [row]`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `LENGTH(D':A list) = LENGTH(D:A list)` THENL
   [DISJ1_TAC THEN REWRITE_TAC[LIST_EQ] THEN ASM_MESON_TAC[];
    DISJ2_TAC THEN
    SUBGOAL_THEN `LENGTH(D':A list) = LENGTH(D:A list) + 1 /\ pay = LENGTH D`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN
    REWRITE_TAC[LIST_EQ] THEN CONJ_TAC THENL
     [REWRITE_TAC[LENGTH_APPEND;LENGTH] THEN ASM_ARITH_TAC;
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND;LENGTH]) THEN
      ASM_CASES_TAC `i < LENGTH(D:A list)` THENL
       [ASM_SIMP_TAC[EL_APPEND];
        SUBGOAL_THEN `i = LENGTH(D:A list)` SUBST1_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
        ASM_REWRITE_TAC[EL_APPEND;LT_REFL;SUB_REFL;EL;HD] THEN ASM_MESON_TAC[]]]]);;

let BW_ROWS_VALID_APPEND = prove
 (`!nms tys D row.
     bw_rows_valid nms tys D /\ bw_row_admissible nms tys D row
     ==> bw_rows_valid nms tys (APPEND D [row])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bw_rows_valid;bw_row_admissible] THEN
  STRIP_TAC THEN CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `i < LENGTH(D:(num#num#num)list)` THENL
   [ASM_SIMP_TAC[EL_APPEND];
    SUBGOAL_THEN `i = LENGTH(D:(num#num#num)list)` SUBST_ALL_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND;LENGTH]) THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[EL_APPEND;LT_REFL;SUB_REFL;EL;HD]];
    MP_TAC(SPECL [`nms:string list`;`tys:(num#num#num)list`;`D:(num#num#num)list`;
                  `[]:string list`;`[]:(num#num#num)list`;`[row:num#num#num]`] FDDB_EXTEND) THEN
    REWRITE_TAC[APPEND_NIL] THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `i = LENGTH(D:(num#num#num)list)` SUBST_ALL_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND;LENGTH]) THEN ASM_ARITH_TAC;
      ASM_MESON_TAC[]]]);;

let BW_ROWS_VALID_INTERNED = prove
 (`!nms tys D D' row pay.
     bw_rows_valid nms tys D /\ bw_row_admissible nms tys D row /\
     (LENGTH D' = LENGTH D \/ LENGTH D' = LENGTH D + 1) /\
     (!i. i < LENGTH D ==> EL i D' = EL i D) /\
     pay < LENGTH D' /\ EL pay D' = row /\
     (LENGTH D' = LENGTH D \/ pay = LENGTH D)
     ==> bw_rows_valid nms tys D'`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`D:(num#num#num)list`;`D':(num#num#num)list`;
                `row:num#num#num`;`pay:num`] BW_LIST_GROW_ONE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  ASM_SIMP_TAC[BW_ROWS_VALID_APPEND]);;

let BW_ADMISSIBLE_BOUND = prove
 (`!nms tys D n. bw_row_admissible nms tys D (1,n,0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bw_row_admissible;bw_key_ok;ARITH_EQ] THEN
  EXISTS_TAC `hdbBound n` THEN
  MATCH_MP_TAC(el 1 (CONJUNCTS(SPEC_ALL fddb_RULES))) THEN
  EXISTS_TAC `0` THEN
  REWRITE_TAC[LENGTH_APPEND;LENGTH;EL_APPEND;LT_REFL;SUB_REFL;EL;HD] THEN ARITH_TAC);;

let BW_ADMISSIBLE_COMB = prove
 (`!nms tys D a b A B.
     fddb nms tys D a A /\ fddb nms tys D b B
     ==> bw_row_admissible nms tys D (3,a,b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `a < LENGTH(D:(num#num#num)list) /\ b < LENGTH D` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[BW_STORE_FDDB_BOUND];ALL_TAC] THEN
  REWRITE_TAC[bw_row_admissible;bw_key_ok;ARITH_EQ] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `hdbComb A B` THEN
  MATCH_MP_TAC(el 3 (CONJUNCTS(SPEC_ALL fddb_RULES))) THEN
  MAP_EVERY EXISTS_TAC [`a:num`;`b:num`] THEN
  REWRITE_TAC[LENGTH_APPEND;LENGTH;EL_APPEND;LT_REFL;SUB_REFL;EL;HD] THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    MP_TAC(SPECL [`nms:string list`;`tys:(num#num#num)list`;`D:(num#num#num)list`;
                  `[]:string list`;`[]:(num#num#num)list`;`[(3,a:num,b:num)]`] FDDB_EXTEND) THEN
    REWRITE_TAC[APPEND_NIL] THEN ASM_MESON_TAC[];
    MP_TAC(SPECL [`nms:string list`;`tys:(num#num#num)list`;`D:(num#num#num)list`;
                  `[]:string list`;`[]:(num#num#num)list`;`[(3,a:num,b:num)]`] FDDB_EXTEND) THEN
    REWRITE_TAC[APPEND_NIL] THEN ASM_MESON_TAC[]]);;

let BW_ADMISSIBLE_ABS = prove
 (`!nms tys D a b TY B.
     fdty nms tys a TY /\ fddb nms tys D b B
     ==> bw_row_admissible nms tys D (4,a,b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `b < LENGTH(D:(num#num#num)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[BW_STORE_FDDB_BOUND];ALL_TAC] THEN
  REWRITE_TAC[bw_row_admissible;bw_key_ok;ARITH_EQ] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `hdbAbs TY B` THEN
  MATCH_MP_TAC(el 4 (CONJUNCTS(SPEC_ALL fddb_RULES))) THEN
  MAP_EVERY EXISTS_TAC [`a:num`;`b:num`] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND;LENGTH;EL_APPEND;LT_REFL;SUB_REFL;EL;HD] THEN
  CONJ_TAC THENL
   [ARITH_TAC;
    MP_TAC(SPECL [`nms:string list`;`tys:(num#num#num)list`;`D:(num#num#num)list`;
                  `[]:string list`;`[]:(num#num#num)list`;`[(4,a:num,b:num)]`] FDDB_EXTEND) THEN
    REWRITE_TAC[APPEND_NIL] THEN ASM_MESON_TAC[]]);;

let BW_ROWS_VALID_SOURCE_COMB = prove
 (`!nms tys D i a b.
     bw_rows_valid nms tys D /\ i < LENGTH D /\ EL i D = (3,a,b)
     ==> (?A. fddb nms tys D a A) /\ (?B. fddb nms tys D b B)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bw_rows_valid] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    is_forall(concl th) && can(find_term ((=) `fddb`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(DISJ_CASES_THEN (CHOOSE_THEN MP_TAC)) THEN
  GEN_REWRITE_TAC LAND_CONV [fddb_CASES] THEN
  ASM_REWRITE_TAC[PAIR_EQ;ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[]);;

let BW_ROWS_VALID_SOURCE_ABS = prove
 (`!nms tys D i a b.
     bw_rows_valid nms tys D /\ i < LENGTH D /\ EL i D = (4,a,b)
     ==> (?TY. fdty nms tys a TY) /\ (?B. fddb nms tys D b B)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bw_rows_valid] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    is_forall(concl th) && can(find_term ((=) `fddb`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(DISJ_CASES_THEN (CHOOSE_THEN MP_TAC)) THEN
  GEN_REWRITE_TAC LAND_CONV [fddb_CASES] THEN
  ASM_REWRITE_TAC[PAIR_EQ;ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[]);;

let BW_TERM_CONSTRUCTOR_ACYCLIC = prove
 (`!x. (!y. ~(x = hdbComb x y) /\ ~(x = hdbComb y x)) /\
       (!ty. ~(x = hdbAbs ty x))`,
  MATCH_MP_TAC hdbterm_INDUCT THEN
  REWRITE_TAC[hdbterm_DISTINCT;hdbterm_INJ] THEN MESON_TAC[]);;

(* A newly appended term whose decoding is inhabited cannot refer to itself:
   functional decoding would equate a term to one of its own constructors.
   The reserved second word of Bound still needs its separate machine fact. *)
let BW_LAST_TERM_ADMISSIBLE = prove
 (`!nms tys (D:(num#num#num)list) row t.
     fddb nms tys (APPEND D [row]) (LENGTH D) t /\
     (FST row = 1 ==> SND(SND row) = 0)
     ==> bw_row_admissible nms tys D row`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[bw_row_admissible] THEN CONJ_TAC THENL
   [ALL_TAC;EXISTS_TAC `t:hdbterm` THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `EL (LENGTH D) (APPEND D [row:num#num#num]) = row` ASSUME_TAC THENL
   [REWRITE_TAC[EL_APPEND;LT_REFL;SUB_REFL;EL;HD];ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o ONCE_REWRITE_RULE[fddb_CASES] o
     check (fun th -> fst(strip_comb(concl th)) = `fddb`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `row:num#num#num`)) THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `t:hdbterm`))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST;SND;ARITH_EQ]) THEN
  ASM_REWRITE_TAC[bw_key_ok;ARITH_EQ] THEN
  REPEAT CONJ_TAC THEN W(fun (asl,w) ->
    let i = lhand w in
    let child = snd(find (fun (_,th) -> fst(strip_comb(concl th)) = `fddb` &&
      rand(rator(concl th)) = i) asl) in
    let root = snd(find (fun (_,th) -> fst(strip_comb(concl th)) = `fddb` &&
      rand(rator(concl th)) = `LENGTH(D:(num#num#num)list)`) asl) in
    let func = CONJUNCT1(SPECL [`nms:string list`;`tys:(num#num#num)list`;
      el 2 (snd(strip_comb(concl root)))] FDDB_FUNCTIONAL) in
    let at_root = mk_eq(i,`LENGTH(D:(num#num#num)list)`) in
    let child_at_root = EQ_MP
      (AP_THM (AP_TERM (rator(rator(concl child))) (ASSUME at_root))
              (rand(concl child))) child in
    let same = MP (SPEC (rand(concl child_at_root))
      (MATCH_MP (SPECL [rand(rator(concl root));rand(concl root)] func) root))
      child_at_root in
    (MP_TAC(REWRITE_RULE[LENGTH_APPEND;LENGTH] (MATCH_MP FDDB_LT child)) THEN
     ASM_CASES_TAC at_root THENL
     [MESON_TAC[same;SPEC (rand(concl child)) BW_TERM_CONSTRUCTOR_ACYCLIC];
      MP_TAC(ASSUME(mk_neg at_root)) THEN ARITH_TAC])));;

let BW_ROWS_VALID_POSITIVE = prove
 (`bw_rows_valid [] [] [(1,0,0)]`,
  REWRITE_TAC[bw_rows_valid;LENGTH;ARITH_RULE `i < SUC 0 <=> i = 0`] THEN
  REWRITE_TAC[FORALL_UNWIND_THM2;EL;HD;bw_key_ok;ARITH_EQ] THEN
  DISJ1_TAC THEN EXISTS_TAC `hdbBound 0` THEN
  MATCH_MP_TAC(el 1 (CONJUNCTS(SPEC_ALL fddb_RULES))) THEN EXISTS_TAC `0` THEN
  REWRITE_TAC[LENGTH;EL;HD;ARITH]);;

let BW_ROWS_VALID_NEGATIVE = prove
 (`~bw_rows_valid [] [] [(3,0,0)] /\ ~bw_rows_valid [] [] [(1,0,1)]`,
  REWRITE_TAC[bw_rows_valid] THEN CONJ_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `0` o CONJUNCT1) THEN
  REWRITE_TAC[LENGTH;EL;HD;bw_key_ok;ARITH]);;

let bind_walk_store_theorems =
 ["BW_LIST_GROW_ONE",BW_LIST_GROW_ONE;
  "BW_ROWS_VALID_APPEND",BW_ROWS_VALID_APPEND;"BW_ROWS_VALID_INTERNED",BW_ROWS_VALID_INTERNED;
  "BW_ADMISSIBLE_BOUND",BW_ADMISSIBLE_BOUND;
  "BW_ADMISSIBLE_COMB",BW_ADMISSIBLE_COMB;
  "BW_ADMISSIBLE_ABS",BW_ADMISSIBLE_ABS;
  "BW_LAST_TERM_ADMISSIBLE",BW_LAST_TERM_ADMISSIBLE;
  "BW_ROWS_VALID_SOURCE_COMB",BW_ROWS_VALID_SOURCE_COMB;
  "BW_ROWS_VALID_SOURCE_ABS",BW_ROWS_VALID_SOURCE_ABS;
  "BW_ROWS_VALID_POSITIVE",BW_ROWS_VALID_POSITIVE;
  "BW_ROWS_VALID_NEGATIVE",BW_ROWS_VALID_NEGATIVE];;

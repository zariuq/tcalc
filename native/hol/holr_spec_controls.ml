(* ========================================================================= *)
(* Controls of the specification's names (holr_accepts_spec, holr_spec.ml).   *)
(*                                                                           *)
(* Two streams define T and deliver |- T: one with HOL's definition,        *)
(* T = ((\p. p) = (\p. p)), one with T = ((\p q. p) = (\p q. p)). Each    *)
(* runs through holr_step from HOL's initial context (the runs are built    *)
(* record by record, every premise decided by evaluation; the RULE record  *)
(* appends |- T, derived from the definition as HOL Light derives TRUTH).   *)
(*                                                                           *)
(* HOLR_SPEC_STD_T: against the specification [] |- T with no declarations *)
(* (T must be HOL's T), the first stream is accepted.                       *)
(* HOLR_BAD_T_DELIVERS: the second stream runs and delivers its |- T.       *)
(* HOLR_SPEC_BAD_T_REFUSED: against the same specification it is refused,  *)
(* under every host floor and header policy.                                *)
(* HOLR_SPEC_BAD_T_DECLARED: a specification that declares that T accepts  *)
(* it.                                                                       *)
(*                                                                           *)
(* Loaded after holr_native.ml.                                             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Controls of the names condition. Two streams define T and deliver |- T:  *)
(* one with HOL's definition, T = ((\p. p) = (\p. p)), one with             *)
(* T = ((\p q. p) = (\p q. p)). Against the specification [] |- T with no   *)
(* declarations (T to be HOL's T), the first is accepted and the second is  *)
(* not, though it runs and delivers its |- T; declaring the second's T in  *)
(* the specification accepts it.                                            *)
(* ------------------------------------------------------------------------- *)

(* From a definition c := x = x, the theorem |- c (HOL Light's TRUTH).      *)
let HOLR_DEF_TRUTH = prove
 (`!ctx c ty x.
      htheory_ok (hthyof ctx) /\ hterm_ok (hsigof ctx) (TmVar c ty =:= (x =:= x)) /\
      hlookup (hconst_list ctx) c = NONE /\ HCLOSED (x =:= x) /\
      (!v. MEM v (htvars (x =:= x)) ==> MEM v (htyvars ty))
      ==> hproves (hthyof (CONS (HConstSpec [c,x =:= x] (TmVar c ty =:= (x =:= x))) ctx)) []
                  (TmConst c ty)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ctx:hupdate list`; `c:string`; `ty:holtype`; `x =:= x`]
               HOL_NEW_BASIC_DEFINITION) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`CONS (HConstSpec [c,x =:= x] (TmVar c ty =:= (x =:= x))) ctx`,`ctx1:hupdate list`) THEN
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HPROVES_TERM_OK) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HTHEORY_OK_STD_SIG) THEN
  SUBGOAL_THEN `hterm_ok (FST(hthyof ctx1)) x` ASSUME_TAC THENL
   [UNDISCH_TAC `hterm_ok (FST(hthyof ctx1)) (TmConst c ty =:= (x =:= x))` THEN
    ASM_SIMP_TAC[HTERM_OK_EQUATION]; ALL_TAC] THEN
  SUBGOAL_THEN `hproves (hthyof ctx1) [] (x =:= x)` ASSUME_TAC THENL
   [MATCH_MP_TAC HPROVES_REFL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `hproves (hthyof ctx1) [] ((x =:= x) =:= TmConst c ty)` ASSUME_TAC THENL
   [MATCH_MP_TAC HPROVES_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hthyof ctx1`; `[]:holterm list`; `[]:holterm list`; `x =:= x`;
                 `TmConst c ty`; `x =:= x`] HPROVES_EQ_MP) THEN
  ASM_REWRITE_TAC[HACONV_REFL; HTERM_UNION]);;

(* Inverting the remaining construction and theory steps. *)
let HOLR_INV_COMB = prove
 (`!ctx nms tys tms ths drops pol s t u.
      holr_step (ctx,nms,tys,tms,ths,drops,pol) (RComb s t) u
      ==> u = (ctx,nms,tys,APPEND tms [TmComb (EL s tms) (EL t tms)],ths,drops,pol)`,
  HOLR_INVERT_TAC);;

let HOLR_INV_ABS = prove
 (`!ctx nms tys tms ths drops pol v t u.
      holr_step (ctx,nms,tys,tms,ths,drops,pol) (RAbs v t) u
      ==> u = (ctx,nms,tys,APPEND tms [TmAbs (EL v tms) (EL t tms)],ths,drops,pol)`,
  HOLR_INVERT_TAC);;

let HOLR_INV_NEW_DEFINITION = prove
 (`!ctx nms tys tms ths drops pol t u.
      holr_step (ctx,nms,tys,tms,ths,drops,pol) (RNewDefinition t) u
      ==> ?c ty r. EL t tms = (TmVar c ty =:= r) /\
                   u = (CONS (HConstSpec [c,r] (TmVar c ty =:= r)) ctx,nms,tys,tms,
                        APPEND ths [([],TmConst c ty =:= r)],drops,pol)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[holr_step_CASES] THEN
  REWRITE_TAC[HOLR_RECORD_DISTINCT; HOLR_RECORD_INJ; holr_is_rule; PAIR_EQ] THEN
  MESON_TAC[]);;

let HOLR_INV_REFL_CTX = prove
 (`!ctx nms tys tms ths drops pol t u.
      holr_step (ctx,nms,tys,tms,ths,drops,pol) (RRefl t) u
      ==> ?th. u = (ctx,nms,tys,tms,APPEND ths [th],drops,pol)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[holr_step_CASES] THEN
  REWRITE_TAC[HOLR_RECORD_DISTINCT; HOLR_RECORD_INJ; holr_is_rule; PAIR_EQ] THEN
  MESON_TAC[]);;

let HOLR_INV_EMIT = prove
 (`!ctx nms tys tms ths drops pol h u.
      holr_step (ctx,nms,tys,tms,ths,drops,pol) (REmit h) u
      ==> u = (ctx,nms,tys,tms,ths,drops,pol)`,
  HOLR_INVERT_TAC);;

let holr_std_t = new_definition
 `holr_std_t =
    [RName [84]; RName [98;111;111;108]; RName [102;117;110]; RName [61]; RName [112];
     RTyApp 1 []; RTyApp 2 [0;0]; RTyApp 2 [0;1]; RTyApp 2 [1;0]; RTyApp 2 [1;3];
     RVar 4 0; RAbs 0 0; RConst 3 4; RComb 2 1; RComb 3 1;
     RVar 0 0; RConst 3 2; RComb 6 5; RComb 7 4;
     RNewDefinition 8; RRefl 1; REmit 1]`;;

let holr_bad_t = new_definition
 `holr_bad_t =
    [RName [84]; RName [98;111;111;108]; RName [102;117;110]; RName [61]; RName [112];
     RName [113];
     RTyApp 1 []; RTyApp 2 [0;0]; RTyApp 2 [0;1]; RTyApp 2 [2;0]; RTyApp 2 [2;3];
     RVar 4 0; RVar 5 0; RAbs 1 0; RAbs 0 2; RConst 3 4; RComb 4 3; RComb 5 3;
     RVar 0 0; RConst 3 2; RComb 8 7; RComb 9 6;
     RNewDefinition 10; RRefl 3; REmit 1]`;;

(* ------------------------------------------------------------------------- *)
(* Running a stream of explicit records through holr_step: each rule of     *)
(* holr_step instantiated at the state and the step's values, its premises  *)
(* decided by evaluation.                                                    *)
(* ------------------------------------------------------------------------- *)

let HOLR_STATE_CONV =
  REWRITE_CONV[APPEND; MAP; holr_name; hchar_of] THENC FIBRE_EVAL_CONV THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV[HFun; HBool];;

let HOLR_EVAL_TAC pre =
  REWRITE_TAC pre THEN
  REWRITE_TAC[holr_ops_live; holr_operands; holr_live; holr_is_rule; ALL; MEM; LENGTH;
              APPEND; MAP] THEN
  CONV_TAC FIBRE_EVAL_CONV THEN
  REWRITE_TAC[hlookup; htype_list; hconst_list; hinit_ctxt; hflat; MAP; htypes_of_upd;
              hconsts_of_upd; APPEND; HFun; HBool; htypeof; hcodomain; HTYPE_SUBST;
              HREV_ASSOCD; hequation; HEqual] THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC(pre @ [option_INJ; option_DISTINCT; holtype_INJ; CONS_11; PAIR_EQ]) THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[];;

let holr_run_step rule st extra pre =
  let th = SPECL (st @ extra) rule in
  let th' = if is_imp(concl th)
            then MP th (prove(lhand(concl th), HOLR_EVAL_TAC pre)) else th in
  let sth = CONV_RULE (RAND_CONV HOLR_STATE_CONV) th' in
  sth, strip_tuple(rand(concl sth));;

let holr_run init plan =
  let rec run st = function
      [] -> ISPECL [`holr_step`; end_itlist (curry mk_pair) st] (prove
              (`!(step:S->E->S->bool) s. tc_path step [] s s`, REWRITE_TAC[tc_path]))
    | (rule,extra,pre)::rest ->
        let sth,st' = holr_run_step rule st extra pre in
        let pth = run st' rest in
        MATCH_MP (ISPEC `holr_step` TC_PATH_CONS_STEP) (CONJ sth pth) in
  run init plan;;

let ctl_bool_ty = `TyApp "bool" []`;;
let ctl_fun a b = mk_comb(mk_comb(`TyApp`,`"fun"`),mk_list([a;b],`:holtype`));;
let ctl_bb = ctl_fun ctl_bool_ty ctl_bool_ty;;
let ctl_eq_generic = `TyApp "fun" [TyVar "A"; TyApp "fun" [TyVar "A"; TyApp "bool" []]]`;;
let ctl_tyin ty = mk_list([mk_pair(ty,`TyVar "A"`)],`:holtype#holtype`);;
let ctl_var x ty = mk_comb(mk_comb(`TmVar`,x),ty);;
let ctl_abs v t = mk_comb(mk_comb(`TmAbs`,v),t);;
let ctl_eqtm x = mk_comb(mk_comb(`(=:=)`,x),x);;
let HOLR_EQ_UNFOLD tm = (REWRITE_CONV[hequation; HEqual; htypeof; HFun; HBool]) tm;;

let holr_def_facts x =
  let eqx = HOLR_EQ_UNFOLD (ctl_eqtm x) in
  let body = rhs(concl eqx) in
  let defterm = mk_comb(mk_comb(`(=:=)`,`TmVar "T" (TyApp "bool" [])`),body) in
  let sigok = REWRITE_RULE[HTHYOF_SIG] (MATCH_MP HTHEORY_OK_STD_SIG HINIT_THEORY_OK) in
  let tmok = prove(mk_comb(`hterm_ok (hsigof hinit_ctxt)`,defterm),
    REWRITE_TAC[GSYM eqx] THEN SIMP_TAC[HTERM_OK_EQUATION; sigok] THEN
    REWRITE_TAC[hterm_ok; htypeof; HFun; HBool; hsigof; hinit_ctxt; htype_list; hflat; MAP;
                htypes_of_upd; APPEND; HTYPE_OK; ALL; LENGTH; hlookup; holterm_INJ;
                hequation; HEqual] THEN
    CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[hcodomain; GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    REWRITE_TAC[HTYPE_OK; ALL; LENGTH; hlookup] THEN
    CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[]) in
  let closed = prove(mk_comb(`HCLOSED`,body),
    REWRITE_TAC[HCLOSED; HVFREE_IN; holterm_INJ; holterm_DISTINCT] THEN MESON_TAC[]) in
  let tvs = prove(mk_forall(`v:string`,
                    mk_imp(mk_comb(mk_comb(`MEM:string->string list->bool`,`v:string`),
                                   mk_comb(`htvars`,body)),
                           `MEM (v:string) (htyvars (TyApp "bool" []))`)),
    REWRITE_TAC[htvars; HTYVARS_DEF; HLIST_UNION; ITLIST; HLIST_INSERT; MEM] THEN
    REWRITE_TAC[MEM]) in
  let truth = REWRITE_RULE[eqx]
    (MATCH_MP (SPECL [`hinit_ctxt`; `"T"`; `TyApp "bool" []`; x] HOLR_DEF_TRUTH)
              (end_itlist CONJ [HINIT_THEORY_OK; REWRITE_RULE[GSYM eqx] tmok;
                                prove(`hlookup (hconst_list hinit_ctxt) "T" = NONE`,
                                  REWRITE_TAC[hconst_list; hinit_ctxt; hflat; MAP;
                                    hconsts_of_upd; APPEND; hlookup] THEN
                                  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[]);
                                REWRITE_RULE[GSYM eqx] closed; REWRITE_RULE[GSYM eqx] tvs])) in
  body, tmok, closed, tvs, truth;;

let std_x = ctl_abs (ctl_var `"p"` ctl_bool_ty) (ctl_var `"p"` ctl_bool_ty);;
let std_body, std_tmok, std_closed, std_tvs, std_truth = holr_def_facts std_x;;

let holr_init = [`hinit_ctxt`; `[]:string list`; `[]:holtype list`; `[]:holterm list`;
                 `[]:(holterm list#holterm)list`; `[]:(num#num)list`; `p:num`];;
let ctl_bool_bool_to_bool = ctl_fun ctl_bb ctl_bool_ty;;
let std_plan =
  [HOLR_STEP_NAME, [`[84]`], [];
   HOLR_STEP_NAME, [`[98;111;111;108]`], [];
   HOLR_STEP_NAME, [`[102;117;110]`], [];
   HOLR_STEP_NAME, [`[61]`], [];
   HOLR_STEP_NAME, [`[112]`], [];
   HOLR_STEP_TYAPP, [`1`; `[]:num list`], [];
   HOLR_STEP_TYAPP, [`2`; `[0;0]`], [];
   HOLR_STEP_TYAPP, [`2`; `[0;1]`], [];
   HOLR_STEP_TYAPP, [`2`; `[1;0]`], [];
   HOLR_STEP_TYAPP, [`2`; `[1;3]`], [];
   HOLR_STEP_VAR, [`4`; `0`], [];
   HOLR_STEP_ABS, [`0`; `0`; `"p"`; ctl_bool_ty], [];
   HOLR_STEP_CONST, [`3`; `4`; ctl_eq_generic; ctl_tyin ctl_bb], [];
   HOLR_STEP_COMB, [`2`; `1`; ctl_bool_bool_to_bool], [];
   HOLR_STEP_COMB, [`3`; `1`; ctl_bool_ty], [];
   HOLR_STEP_VAR, [`0`; `0`], [];
   HOLR_STEP_CONST, [`3`; `2`; ctl_eq_generic; ctl_tyin ctl_bool_ty], [];
   HOLR_STEP_COMB, [`6`; `5`; ctl_bb], [];
   HOLR_STEP_COMB, [`7`; `4`; ctl_bool_ty], [];
   HOLR_STEP_NEW_DEFINITION, [`8`; `"T"`; ctl_bool_ty; std_body],
     [HINIT_THEORY_OK; std_tmok; std_closed; std_tvs];
   HOLR_STEP_RULE, [`RRefl 1`; `[]:holterm list`; `TmConst "T" (TyApp "bool" [])`], [std_truth];
   HOLR_STEP_EMIT, [`1`], []];;
let std_path = holr_run holr_init std_plan;;

let HOLR_EMIT_FILTER = prove
 (`!h. (?k. REmit h = REmit k) <=> T`,
  REWRITE_TAC[HOLR_RECORD_INJ] THEN MESON_TAC[]);;

let HOLR_EMITS_CLAUSES = prove
 (`holr_emits [] = [] /\
   (!h rs. holr_emits (CONS (REmit h) rs) = CONS h (holr_emits rs)) /\
   (!r rs. (!h. ~(r = REmit h)) ==> holr_emits (CONS r rs) = holr_emits rs)`,
  REWRITE_TAC[holr_emits; FILTER; MAP] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[HOLR_EMIT_FILTER; MAP; HOLR_EMIT_SEL];
    DISCH_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[]]);;

let HOLR_DELIVERED_TAC defs =
  REWRITE_TAC(defs @ [holr_delivered]) THEN
  SIMP_TAC[HOLR_EMITS_CLAUSES; HOLR_RECORD_DISTINCT] THEN
  REWRITE_TAC[MAP; hr_ths] THEN CONV_TAC FIBRE_EVAL_CONV THEN
  REWRITE_TAC[ALL2; holr_entails; HACONV_REFL; MEM];;


(* Names standard in an explicit context, through hstd_seq. *)
let holr_std_names ctx =
  let norm = REWRITE_CONV[hinit_ctxt; HFun; HBool] ctx in
  let upds = dest_list(rhs(concl norm)) in
  let seq = itlist (fun u th -> hstd_seq_step th u) upds
                   (prove(`hstd_seq []`, REWRITE_TAC[hstd_seq])) in
  let dc,dt = CONJ_PAIR(MATCH_MP HSTD_SEQ_DECLS seq) in
  norm, dc, dt;;

let std_final = rand(concl std_path);;
let std_ctx1 = hd(strip_tuple std_final);;
let std_norm, std_dc, std_dt = holr_std_names std_ctx1;;

(* A context with no axioms allows any list of axioms. *)
let HOLR_NO_AXIOMS_TAC =
  REWRITE_TAC[holr_axioms_allowed; ALL; hr_ctx] THEN
  REWRITE_TAC[MEM; hinit_ctxt; hupdate_DISTINCT];;

let HOLR_SPEC_STD_T = prove
 (`!hpol pol. pol <= 2
      ==> holr_accepts_spec hpol [] [] [[],TmConst "T" (TyApp "bool" [])]
                            (holr_stream pol 0 holr_std_t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[holr_accepts_spec] THEN
  MAP_EVERY EXISTS_TAC [`pol:num`; `holr_std_t`;
                        subst [`MAX hpol pol`,`p:num`] std_final] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[holr_std_t] THEN ACCEPT_TAC(INST [`MAX hpol pol`,`p:num`] std_path);
    HOLR_DELIVERED_TAC [holr_std_t];
    REWRITE_TAC[ALL; holr_spec_ok; hr_ctx] THEN
    MP_TAC(CONJUNCT1(CONJUNCT2(MATCH_MP HPROVES_TERM_OK std_truth))) THEN
    REWRITE_TAC[HTHYOF_SIG];
    REWRITE_TAC[holr_spec_pinned; ALL; holr_pinned; htm_consts; htm_tyops; HTYNAMES_DEF;
                APPEND; hr_ctx] THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[ALL; holr_pinned; htm_consts; htm_tyops; HTYNAMES_DEF; APPEND;
                holr_cpinned; holr_tpinned; MEM] THEN
    REWRITE_TAC[std_norm] THEN CONJ_TAC THEN HSTD_NAME_TAC std_dc std_dt;
    HOLR_NO_AXIOMS_TAC]);;

let ctl_bbb = ctl_fun ctl_bool_ty ctl_bb;;
let bad_x = ctl_abs (ctl_var `"p"` ctl_bool_ty)
                    (ctl_abs (ctl_var `"q"` ctl_bool_ty) (ctl_var `"p"` ctl_bool_ty));;
let bad_body, bad_tmok, bad_closed, bad_tvs, bad_truth = holr_def_facts bad_x;;
let bad_plan =
  [HOLR_STEP_NAME, [`[84]`], [];
   HOLR_STEP_NAME, [`[98;111;111;108]`], [];
   HOLR_STEP_NAME, [`[102;117;110]`], [];
   HOLR_STEP_NAME, [`[61]`], [];
   HOLR_STEP_NAME, [`[112]`], [];
   HOLR_STEP_NAME, [`[113]`], [];
   HOLR_STEP_TYAPP, [`1`; `[]:num list`], [];
   HOLR_STEP_TYAPP, [`2`; `[0;0]`], [];
   HOLR_STEP_TYAPP, [`2`; `[0;1]`], [];
   HOLR_STEP_TYAPP, [`2`; `[2;0]`], [];
   HOLR_STEP_TYAPP, [`2`; `[2;3]`], [];
   HOLR_STEP_VAR, [`4`; `0`], [];
   HOLR_STEP_VAR, [`5`; `0`], [];
   HOLR_STEP_ABS, [`1`; `0`; `"q"`; ctl_bool_ty], [];
   HOLR_STEP_ABS, [`0`; `2`; `"p"`; ctl_bool_ty], [];
   HOLR_STEP_CONST, [`3`; `4`; ctl_eq_generic; ctl_tyin ctl_bbb], [];
   HOLR_STEP_COMB, [`4`; `3`; ctl_fun ctl_bbb ctl_bool_ty], [];
   HOLR_STEP_COMB, [`5`; `3`; ctl_bool_ty], [];
   HOLR_STEP_VAR, [`0`; `0`], [];
   HOLR_STEP_CONST, [`3`; `2`; ctl_eq_generic; ctl_tyin ctl_bool_ty], [];
   HOLR_STEP_COMB, [`8`; `7`; ctl_bb], [];
   HOLR_STEP_COMB, [`9`; `6`; ctl_bool_ty], [];
   HOLR_STEP_NEW_DEFINITION, [`10`; `"T"`; ctl_bool_ty; bad_body],
     [HINIT_THEORY_OK; bad_tmok; bad_closed; bad_tvs];
   HOLR_STEP_RULE, [`RRefl 3`; `[]:holterm list`; `TmConst "T" (TyApp "bool" [])`], [bad_truth];
   HOLR_STEP_EMIT, [`1`], []];;
let bad_path = holr_run holr_init bad_plan;;
let bad_final = rand(concl bad_path);;
let bad_ctx1 = hd(strip_tuple bad_final);;

(* The stream runs and delivers |- T, with its own T. *)
let HOLR_BAD_T_DELIVERS = prove
 (`!hpol pol. ?s. tc_path holr_step holr_bad_t (hinit_ctxt,[],[],[],[],[],MAX hpol pol) s /\
                  holr_delivered holr_bad_t s = [[],TmConst "T" (TyApp "bool" [])]`,
  REPEAT GEN_TAC THEN EXISTS_TAC (subst [`MAX hpol pol`,`p:num`] bad_final) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[holr_bad_t] THEN ACCEPT_TAC(INST [`MAX hpol pol`,`p:num`] bad_path);
    REWRITE_TAC[holr_bad_t; holr_delivered] THEN
    SIMP_TAC[HOLR_EMITS_CLAUSES; HOLR_RECORD_DISTINCT] THEN
    REWRITE_TAC[MAP; hr_ths] THEN CONV_TAC FIBRE_EVAL_CONV]);;



(* A context whose last event defines c is standard at c only if the body is *)
(* a standard body of c, up to alpha.                                        *)
let HSTD_DECLS_DEF_HEAD = prove
 (`!c ty r ctx. FST(hstd_decls (CONS (HConstSpec [c,r] (TmVar c ty =:= r)) ctx)) c
                ==> ?b. MEM (c,htypeof r,b) hstd_defs /\ HACONV r b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hstd_decls; FST; hconsts_of_upd; MAP; MEM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST; MEM; hstd_upd_c] THEN
  REWRITE_TAC[CONS_11; PAIR_EQ] THEN MESON_TAC[]);;

(* Walk an explicit run: replace each successor state by what its record    *)
(* makes, evaluating the states as it goes.                                  *)
let HOLR_WALK2_TAC =
  let invs = [HOLR_INV_NAME; HOLR_INV_TYAPP; HOLR_INV_CONST; HOLR_INV_VAR; HOLR_INV_COMB;
              HOLR_INV_ABS; HOLR_INV_EMIT] in
  let det = FIRST_X_ASSUM(fun th -> tryfind (fun inv -> SUBST_ALL_TAC(MATCH_MP inv th)) invs)
  and refl = FIRST_X_ASSUM(fun th -> CHOOSE_THEN SUBST_ALL_TAC (MATCH_MP HOLR_INV_REFL_CTX th))
  and def = FIRST_X_ASSUM(fun th ->
              REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)
                (MATCH_MP HOLR_INV_NEW_DEFINITION th)) in
  REPEAT((det ORELSE refl ORELSE def) THEN RULE_ASSUM_TAC(CONV_RULE HOLR_STATE_CONV));;

let holr_bad_t_body = new_definition
 (mk_eq(`holr_bad_t_body:holterm`, bad_body));;

(* Against the specification [] |- T, with no declarations (T is HOL's T),  *)
(* the stream is refused under every host floor and header policy.          *)
let HOLR_SPEC_BAD_T_REFUSED = prove
 (`!hpol pol. ~holr_accepts_spec hpol [] [] [[],TmConst "T" (TyApp "bool" [])]
                                 (holr_stream pol 0 holr_bad_t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[holr_accepts_spec; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`pol':num`; `recs:holr_record list`; `s:hrstate`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOLR_STREAM_INJ o
                check (fun th -> can (term_match [] `holr_stream a b c = d`) (concl th))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var(rand(concl th))))) THEN
  FIRST_X_ASSUM(MP_TAC o check (holr_mentions "holr_spec_pinned")) THEN
  FIRST_X_ASSUM(MP_TAC o check (holr_mentions "tc_path")) THEN
  REWRITE_TAC[holr_bad_t; tc_path] THEN STRIP_TAC THEN
  HOLR_WALK2_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
                                can (find_term ((=) `(=:=)`)) (rand(concl th)))) THEN
  REWRITE_TAC[hequation; HEqual; htypeof; HFun; HBool; holterm_INJ] THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[holtype_INJ; CONS_11]) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
                       check (fun th -> is_eq(concl th) && is_var(rand(concl th))))) THEN
  REWRITE_TAC[holr_spec_pinned; ALL; hr_ctx] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[ALL; holr_pinned; htm_consts; htm_tyops; HTYNAMES_DEF; APPEND;
              holr_cpinned; MEM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HSTD_DECLS_DEF_HEAD o CONJUNCT1) THEN
  REWRITE_TAC[hstd_defs; MEM; PAIR_EQ] THEN CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN
  REWRITE_TAC[htypeof; HFun; HBool; hcodomain; LEFT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2] THEN
  REWRITE_TAC[HACONV; HRACONV; holterm_INJ; holterm_DISTINCT; holtype_INJ; CONS_11] THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[]);;

(* A context's last event leaves the standardness of the names it does not   *)
(* declare as it was.                                                         *)
let HSTD_DECLS_SKIP = prove
 (`!u rest x.
      (~MEM x (MAP FST (hconsts_of_upd u))
       ==> (FST(hstd_decls (CONS u rest)) x <=> FST(hstd_decls rest) x)) /\
      (~MEM x (MAP FST (htypes_of_upd u))
       ==> (SND(hstd_decls (CONS u rest)) x <=> SND(hstd_decls rest) x))`,
  REWRITE_TAC[hstd_decls; FST; SND] THEN SIMP_TAC[]);;

let hinit_norm, hinit_dc, hinit_dt = holr_std_names `hinit_ctxt`;;

(* A name standard in HOL's initial context stays standard under an event   *)
(* that does not declare it.                                                  *)
let HSTD_SKIP_TAC =
  W(fun (asl,w) ->
    let ctx = rand(rand(rator w)) in
    let u = rand(rator ctx) and rest = rand ctx and x = rand w in
    let th = SPECL [u; rest; x] HSTD_DECLS_SKIP in
    MP_TAC th THEN
    REWRITE_TAC[hconsts_of_upd; htypes_of_upd; MAP] THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST; MEM] THEN
    CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[hinit_norm] THEN HSTD_NAME_TAC hinit_dc hinit_dt);;

(* Declaring that T in the specification accepts the stream. *)
let HOLR_SPEC_BAD_T_DECLARED = prove
 (`!hpol pol. pol <= 2
      ==> holr_accepts_spec hpol
            [HConstSpec ["T",holr_bad_t_body]
                        (TmVar "T" (TyApp "bool" []) =:= holr_bad_t_body)] []
            [[],TmConst "T" (TyApp "bool" [])] (holr_stream pol 0 holr_bad_t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[holr_accepts_spec] THEN
  MAP_EVERY EXISTS_TAC [`pol:num`; `holr_bad_t`;
                        subst [`MAX hpol pol`,`p:num`] bad_final] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[holr_bad_t] THEN ACCEPT_TAC(INST [`MAX hpol pol`,`p:num`] bad_path);
    HOLR_DELIVERED_TAC [holr_bad_t];
    REWRITE_TAC[ALL; holr_spec_ok; hr_ctx] THEN
    MP_TAC(CONJUNCT1(CONJUNCT2(MATCH_MP HPROVES_TERM_OK bad_truth))) THEN
    REWRITE_TAC[HTHYOF_SIG];
    REWRITE_TAC[holr_spec_pinned; ALL; hr_ctx; hdecl_terms; MAP] THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[ALL; holr_pinned; holr_bad_t_body; htm_consts; htm_tyops; HTYNAMES_DEF;
                APPEND; holr_cpinned; holr_tpinned] THEN
    REPEAT CONJ_TAC THEN
    FIRST [DISJ1_TAC THEN HSTD_SKIP_TAC THEN NO_TAC;
           DISJ2_TAC THEN
           MAP_EVERY EXISTS_TAC
            [subst [bad_body,`holr_bad_t_body`]
               `HConstSpec ["T",holr_bad_t_body] (TmVar "T" (TyApp "bool" []) =:= holr_bad_t_body)`;
             rand(rator bad_ctx1)] THEN
           REWRITE_TAC[MEM; hconsts_of_upd; MAP] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
           REWRITE_TAC[FST; MEM; hdecl_match] THEN
           MAP_EVERY EXISTS_TAC [`"T"`; bad_body; bad_body] THEN
           REWRITE_TAC[HACONV_REFL] THEN
           REWRITE_TAC[htypeof; hcodomain; HFun; HBool]];
    HOLR_NO_AXIOMS_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Controls of the allowed axioms. A stream declares a constant c:bool,     *)
(* asserts c as an axiom and delivers |- c. Against the specification       *)
(* [] |- c, which declares c as an opaque constant: with no axioms allowed  *)
(* it is refused under every host floor and header policy; with c allowed   *)
(* it is accepted, under OPEN.                                              *)
(* ------------------------------------------------------------------------- *)

let holr_ax_c = new_definition
 `holr_ax_c = [RName [99]; RName [98;111;111;108]; RTyApp 1 []; RNewConstant 0 0;
               RConst 0 0; RNewAxiom 0; REmit 0]`;;

let HOLR_INV_NEW_AXIOM_STATE = prove
 (`!ctx nms tys tms ths drops pol t u.
      holr_step (ctx,nms,tys,tms,ths,drops,pol) (RNewAxiom t) u
      ==> u = (CONS (HNewAxiom (EL t tms)) ctx,nms,tys,tms,APPEND ths [([],EL t tms)],
               drops,pol)`,
  HOLR_INVERT_TAC);;

let ax_ctx1 = `CONS (HNewConst "c" (TyApp "bool" [])) hinit_ctxt`;;
let ax_c = `TmConst "c" (TyApp "bool" [])`;;

(* The facts the axiom step needs, as stated and with HOL's initial context *)
(* unfolded (the step's evaluation unfolds it).                             *)
let HOLR_AX_THEORY_OK = prove
 (`htheory_ok (hthyof (CONS (HNewConst "c" (TyApp "bool" [])) hinit_ctxt))`,
  MATCH_MP_TAC HUPDATES_THEORY_OK THEN REWRITE_TAC[HINIT_THEORY_OK] THEN
  MATCH_MP_TAC HOL_NEW_CONSTANT THEN
  REWRITE_TAC[hconst_list; htype_list; hinit_ctxt; hflat; MAP; hconsts_of_upd; htypes_of_upd;
              APPEND; hlookup; HTYPE_OK; ALL; LENGTH; HFun; HBool] THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let HOLR_AX_TERM_OK = prove
 (`hterm_ok (hsigof (CONS (HNewConst "c" (TyApp "bool" [])) hinit_ctxt))
            (TmConst "c" (TyApp "bool" []))`,
  REWRITE_TAC[hterm_ok; hsigof; hconst_list; htype_list; hinit_ctxt; hflat; MAP;
              hconsts_of_upd; htypes_of_upd; APPEND; hlookup; HTYPE_OK; ALL; LENGTH;
              HFun; HBool] THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[option_INJ; UNWIND_THM1; RIGHT_EXISTS_AND_THM] THEN
  EXISTS_TAC `[]:(holtype#holtype)list` THEN REWRITE_TAC[HTYPE_SUBST_NIL]);;

let HOLR_AX_TYPED = prove
 (`TmConst "c" (TyApp "bool" []) hhas_type HBool`,
  REWRITE_TAC[HBool; hhas_type_RULES]);;

let HOLR_AX_OPEN = prove
 (`holr_axiom_ok 0 (CONS (HNewConst "c" (TyApp "bool" [])) hinit_ctxt)
                   (TmConst "c" (TyApp "bool" []))`,
  REWRITE_TAC[holr_axiom_ok]);;

let ax_facts =
  let unf = REWRITE_RULE[hinit_ctxt; HFun; HBool] in
  let ths = [HOLR_AX_THEORY_OK; HOLR_AX_TERM_OK; HOLR_AX_TYPED; HOLR_AX_OPEN] in
  ths @ map unf ths;;

let ax_plan =
  [HOLR_STEP_NAME, [`[99]`], [];
   HOLR_STEP_NAME, [`[98;111;111;108]`], [];
   HOLR_STEP_TYAPP, [`1`; `[]:num list`], [];
   HOLR_STEP_NEW_CONSTANT, [`0`; `0`], [HTYPE_OK; ALL; LENGTH; hlookup];
   HOLR_STEP_CONST, [`0`; `0`; ctl_bool_ty; `[]:(holtype#holtype)list`], [HTYPE_SUBST_NIL];
   HOLR_STEP_NEW_AXIOM, [`0`], ax_facts;
   HOLR_STEP_EMIT, [`0`], []];;

let ax_init = [`hinit_ctxt`; `[]:string list`; `[]:holtype list`; `[]:holterm list`;
               `[]:(holterm list#holterm)list`; `[]:(num#num)list`; `0`];;
let ax_path = holr_run ax_init ax_plan;;
let ax_final = rand(concl ax_path);;

(* Names standard in HOL's initial context stay standard under events that *)
(* do not declare them.                                                     *)
let HSTD_SKIPS_TAC =
  let skip = W(fun (_,w) ->
    let ctx = rand(rand(rator w)) in
    let u = rand(rator ctx) and rest = rand ctx and x = rand w in
    let part = if fst(dest_const(rator(rator w))) = "FST" then CONJUNCT1 else CONJUNCT2 in
    CHANGED_TAC
     (MP_TAC(part(SPECL [u; rest; x] HSTD_DECLS_SKIP)) THEN
      REWRITE_TAC[hconsts_of_upd; htypes_of_upd; MAP] THEN
      CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST; MEM] THEN
      CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]))) in
  REPEAT skip THEN REWRITE_TAC[hinit_norm] THEN HSTD_NAME_TAC hinit_dc hinit_dt;;

(* c is declared by the specification as the stream declares it; bool is   *)
(* standard.                                                                 *)
let AX_PINNED_TAC =
  REWRITE_TAC[ALL; holr_pinned; hdecl_terms; htm_consts; htm_tyops; HTYNAMES_DEF; APPEND;
              holr_cpinned; holr_tpinned] THEN
  REPEAT CONJ_TAC THEN
  FIRST [DISJ1_TAC THEN HSTD_SKIPS_TAC THEN NO_TAC;
         DISJ2_TAC THEN
         MAP_EVERY EXISTS_TAC [`HNewConst "c" (TyApp "bool" [])`;
                               `HNewConst "c" (TyApp "bool" [])`] THEN
         REWRITE_TAC[MEM; hconsts_of_upd; MAP; FST; hdecl_match; hupdate_DISTINCT]];;

(* With c allowed, the stream is accepted against [] |- c under OPEN. *)
let HOLR_SPEC_AXIOM_LISTED = prove
 (`holr_accepts_spec 0 [HNewConst "c" (TyApp "bool" [])] [TmConst "c" (TyApp "bool" [])]
                     [[],TmConst "c" (TyApp "bool" [])] (holr_stream 0 0 holr_ax_c)`,
  REWRITE_TAC[holr_accepts_spec] THEN
  MAP_EVERY EXISTS_TAC [`0`; `holr_ax_c`; ax_final] THEN
  REWRITE_TAC[ARITH_RULE `0 <= 2 /\ MAX 0 0 = 0`] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[holr_ax_c] THEN ACCEPT_TAC ax_path;
    HOLR_DELIVERED_TAC [holr_ax_c];
    REWRITE_TAC[ALL; holr_spec_ok; hr_ctx] THEN
    MP_TAC HOLR_AX_TERM_OK THEN
    REWRITE_TAC[hsigof; hconst_list; htype_list; hflat; MAP; hconsts_of_upd; htypes_of_upd;
                APPEND];
    REWRITE_TAC[holr_spec_pinned; ALL; hr_ctx] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
    AX_PINNED_TAC;
    REWRITE_TAC[holr_axioms_allowed; hr_ctx] THEN CONJ_TAC THENL
     [REWRITE_TAC[MEM; hinit_ctxt; hupdate_DISTINCT; hupdate_INJ] THEN
      GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN EXISTS_TAC ax_c THEN REWRITE_TAC[HACONV_REFL];
      AX_PINNED_TAC]]);;

(* With no axioms allowed, the stream is refused, under every floor. *)
let HOLR_WALK3_TAC =
  let invs = [HOLR_INV_NAME; HOLR_INV_TYAPP; HOLR_INV_NEW_CONSTANT; HOLR_INV_CONST;
              HOLR_INV_NEW_AXIOM_STATE; HOLR_INV_EMIT] in
  REPEAT(FIRST_X_ASSUM(fun th -> tryfind (fun inv -> SUBST_ALL_TAC(MATCH_MP inv th)) invs) THEN
         RULE_ASSUM_TAC(CONV_RULE HOLR_STATE_CONV));;

let HOLR_SPEC_AXIOM_UNLISTED = prove
 (`!hpol pol. ~holr_accepts_spec hpol [HNewConst "c" (TyApp "bool" [])] []
                                 [[],TmConst "c" (TyApp "bool" [])] (holr_stream pol 0 holr_ax_c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[holr_accepts_spec; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`pol':num`; `recs:holr_record list`; `s:hrstate`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOLR_STREAM_INJ o
                check (fun th -> can (term_match [] `holr_stream a b c = d`) (concl th))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var(rand(concl th))))) THEN
  FIRST_X_ASSUM(MP_TAC o check (holr_mentions "holr_axioms_allowed")) THEN
  FIRST_X_ASSUM(MP_TAC o check (holr_mentions "tc_path")) THEN
  REWRITE_TAC[holr_ax_c; tc_path] THEN STRIP_TAC THEN
  HOLR_WALK3_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
                       check (fun th -> is_eq(concl th) && is_var(rand(concl th))))) THEN
  REWRITE_TAC[holr_axioms_allowed; hr_ctx; MEM; EXISTS_SIMP; hupdate_INJ] THEN
  DISCH_THEN(MP_TAC o SPEC ax_c o CONJUNCT1) THEN REWRITE_TAC[]);;

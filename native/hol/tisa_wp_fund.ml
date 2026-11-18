(* Explicit fuel payment in the weakest-precondition library. *)
needs "native/hol/tisa_wp.ml";;
needs "native/driver/driver_fuel.ml";;

let TISA_FAILST_FINST = prove
 (`!k t. tisa_failst k t = tisa_finst k (word k) t`,
  REWRITE_TAC[tisa_failst;tisa_finst]);;

let TISA_TREGS_SETFWORD = prove
 (`!i v t. tregs(tisa_setfword i v t) = tregs t`,
  REWRITE_TAC[tisa_setfword;TISA_TREGS_STORE]);;

let TISA_WP_FUND = prove
 (`!n Q R t. tisa_wp (TFund n) Q R t <=>
     if val(word_sub (tisa_fword t 20) (tisa_fword t 21)) < n
     then R 4 (tisa_failst 4 t)
     else Q (tisa_setfword 21 (word_add (tisa_fword t 21) (word n)) t)`,
  REWRITE_TAC[tisa_wp;tisa_exec;tisa_fund;TISA_RWP_COND;
              TISA_FAIL_STOP;TISA_RWP_STOP;TISA_RWP_CONT]);;

(* Continue the existing generator when it reaches an explicit payment. *)
let rec TISA_FUND_VCG_TAC : tactic = fun goal ->
  (TISA_VCG_TAC THEN
   W(fun (_,w) ->
     let h,args = strip_comb w in
     if h = `tisa_wp` && fst(strip_comb(hd args)) = `TFund`
     then GEN_REWRITE_TAC I [TISA_WP_FUND] THEN TISA_STATE_NORM_TAC THEN
          TISA_COND_TAC THEN TISA_FUND_VCG_TAC
     else ALL_TAC)) goal;;

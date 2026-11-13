(* ========================================================================= *)
(* The record plans over an abstract machine (tcalc/native/PLANS.txt).       *)
(*                                                                           *)
(* A plan is data: a list of 18-word steps exactly as the driver reads them *)
(* (driver.ml: word 0 the leaf, 1..9 binding slots, 10 and 11 the control   *)
(* words of arg0 and arg1, 12..16 those of v1..v5, 17 the payload's). The   *)
(* abstract machine runs it as drv_sem does, over a state of control words  *)
(* (as numbers: the values of the driver's 64-bit words), the native state  *)
(* (nstate, holr_native.ml) and the operand stack: each leaf's effect is    *)
(* its abstract semantics (pl_leaf), the payload goes to the step's control *)
(* word, and the first outcome other than FIRED ends the plan (pl_run). The *)
(* leaf an abstract step stands for is fixed by its leaf index and the      *)
(* binding slot of its region 0 (the table it works on).                    *)
(*                                                                           *)
(* Per record kind: a plan, and its theorem PL_<KIND>: from a state         *)
(* satisfying pl_inv with the record's operands in their control words, a   *)
(* FIRED run is the record's nat_step and keeps pl_inv, and the run is      *)
(* REFUSED exactly when the clause's guards fail.                            *)
(*                                                                           *)
(* The concrete side (plans_drv.ml) relates drv_sem's runs of the same       *)
(* plans to pl_run, through the leaves' specifications (plans_leaves.ml).   *)
(* ========================================================================= *)

new_type_abbrev("pstate", `:(num->num) # nstate # num list`);;

(* ------------------------------------------------------------------------- *)
(* Rows as the words the tables hold (word w of a row), keys, list rows.     *)
(* A type or de Bruijn row (tag,a,b) is held as the two words tag + 8a and  *)
(* b; a term row as its five fields; a theorem row as its two.              *)
(* ------------------------------------------------------------------------- *)

let pl_f3 = new_definition
 `pl_f3 (r:num#num#num) w = if w = 0 then FST r + 8 * FST(SND r) else SND(SND r)`;;

let pl_f2 = new_definition
 `pl_f2 (r:num#num) w = if w = 0 then FST r else SND r`;;

let pl_f5 = new_definition
 `pl_f5 (r:num#num#num#num#num) w =
    if w = 0 then FST r else if w = 1 then FST(SND r) else if w = 2 then FST(SND(SND r))
    else if w = 3 then ntm_ty r else ntm_db r`;;

(* The row a packed key stands for. *)
let pl_key = new_definition
 `pl_key k0 (k1:num) = (k0 MOD 8, k0 DIV 8, k1)`;;

(* l is a de Bruijn list row of D whose elements' ids are ids (cells (6,a,b),  *)
(* nil (5,0,0)); pl_tyids the same for type lists (cells (3,a,b), nil       *)
(* (2,0,0)).                                                                 *)
let pl_ids = define
 `(pl_ids (D:(num#num#num)list) l [] <=> l < LENGTH D /\ EL l D = (5,0,0)) /\
  (pl_ids D l (CONS a ids) <=> l < LENGTH D /\ ?b. EL l D = (6,a,b) /\ pl_ids D b ids)`;;

let pl_tyids = define
 `(pl_tyids (D:(num#num#num)list) l [] <=> l < LENGTH D /\ EL l D = (2,0,0)) /\
  (pl_tyids D l (CONS a ids) <=> l < LENGTH D /\ ?b. EL l D = (3,a,b) /\ pl_tyids D b ids)`;;

(* The rows of D' from n0 on are list cells of tag c over earlier rows: each *)
(* (c,a,b) with a satisfying ok and b a list row whose elements satisfy ok. *)
let pl_cells_new = new_definition
 `pl_cells_new c n0 (D':(num#num#num)list) (ok:num->bool) <=>
    !i. n0 <= i /\ i < LENGTH D'
        ==> ?a b ids. EL i D' = (c,a,b) /\ a < i /\ b < i /\ ok a /\
                      pl_ids D' b ids /\ ALL ok ids`;;

(* ------------------------------------------------------------------------- *)
(* The leaves' abstract semantics. k is the outcome (FIRED 1, REFUSED 0,     *)
(* UNSUPPORTED 2), pay the payload.                                          *)
(* ------------------------------------------------------------------------- *)

let pl_pack = new_definition
 `pl_pack a tag k (pay:num) <=>
    if a < 2 EXP 60 /\ tag < 8 then k = 1 /\ pay = tag + 8 * a else k = 2`;;

let pl_unpack = new_definition
 `pl_unpack k0 tag k (pay:num) <=>
    if k0 MOD 8 = tag then k = 1 /\ pay = k0 DIV 8 else k = 0`;;

let pl_eqw = new_definition
 `pl_eqw (a:num) b k (pay:num) <=> if a = b then k = 1 /\ pay = a else k = 0`;;

(* row_word over a table of len rows whose word w of row i is fw i w, each  *)
(* of wd words; s the stride.                                               *)
let pl_roww = new_definition
 `pl_roww (fw:num->num->num) len wd i w s k (pay:num) <=>
    s = wd ==> if i < len /\ w < wd then k = 1 /\ pay = fw i w else k = 2`;;

let pl_live = new_definition
 `pl_live (sp:num) len (drops:(num#num)list) i k (pay:num) <=>
    if holr_live sp i len drops then k = 1 /\ pay = i else k = 0`;;

(* intern: the key's row found (md = []), or appended when absent (md = [key]); *)
(* the FIRED outcomes are one fact, so a chain of interns does not multiply  *)
(* the branches of a symbolic run. Any other outcome (UNSUPPORTED when the   *)
(* table is full, or a fault code) is never REFUSED and keeps the rows.      *)
let pl_interned = new_definition
 `pl_interned (rows:(num#num#num)list) key pay md <=>
    md = [] /\ pay < LENGTH rows /\ EL pay rows = key \/
    md = [key] /\ pay = LENGTH rows /\ ~MEM key rows /\ LENGTH rows + 1 < 2 EXP 60`;;

let pl_intern = new_definition
 `pl_intern (rows:(num#num#num)list) k0 k1 k pay rows' <=>
    (k = 1 /\ pay < 2 EXP 60 /\ ?md. pl_interned rows (pl_key k0 k1) pay md /\ rows' = APPEND rows md) \/
    (~(k = 0) /\ ~(k = 1) /\ rows' = rows)`;;

(* append_row to the theorem rows (width w = 2). *)
let pl_append_th = new_definition
 `pl_append_th (ths:(num#num)list) w a b k pay ths' <=>
    w = 2
    ==> (k = 1 /\ LENGTH ths + 1 < 2 EXP 60 /\ pay = LENGTH ths /\ ths' = APPEND ths [(a,b)]) \/
        (k = 2 /\ ths' = ths)`;;

(* hyps_union: the sorted union of two sorted lists; rows appended only     *)
(* when FIRED, all cells over earlier rows.                                  *)
let pl_union = new_definition
 `pl_union (dbs:(num#num#num)list) l1 l2 k (pay:num) dbs' <=>
    (k = 1 \/ k = 2) /\ (?md. dbs' = APPEND dbs md) /\ (~(k = 1) ==> dbs' = dbs) /\
    LENGTH dbs' < 2 EXP 60 /\ (keys_distinct dbs ==> keys_distinct dbs') /\
    (k = 1 ==> !I1 I2. pl_ids dbs l1 I1 /\ pl_ids dbs l2 I2 /\
                       PAIRWISE (<) I1 /\ PAIRWISE (<) I2
                       ==> (?ids. pl_ids dbs' pay ids /\ PAIRWISE (<) ids /\
                                (!x. MEM x ids <=> MEM x I1 \/ MEM x I2)) /\
                           pl_cells_new 6 (LENGTH dbs) dbs' (\a. MEM a I1 \/ MEM a I2))`;;

(* hyps_find: the sorted list of the listed terms' images, when it is a row *)
(* and every listed term is live and of type bool.                           *)
let pl_findl = new_definition
 `pl_findl (ntms:(num#num#num#num#num)list) (drops:(num#num)list) (dbs:(num#num#num)list)
           (stk:num list) ls nl k (pay:num) <=>
    ls + nl <= LENGTH stk
    ==> let ts = list_of_seq (\j. EL (ls + j) stk) nl in
        if ALL (\x. holr_live 2 x (LENGTH ntms) drops /\ ntm_ty (EL x ntms) = 1) ts /\
           (?L ids. pl_ids dbs L ids /\ PAIRWISE (<) ids /\
                  (!x. MEM x ids <=> MEM x (MAP (\x. ntm_db (EL x ntms)) ts)))
        then k = 1 /\ (?ids. pl_ids dbs pay ids /\ PAIRWISE (<) ids /\
                           (!x. MEM x ids <=> MEM x (MAP (\x. ntm_db (EL x ntms)) ts)))
        else k = 0`;;

(* ------------------------------------------------------------------------- *)
(* The leaf table and the binding slots (PLANS.txt, section 2).              *)
(*   leaves  0 intern16  1 pack  2 unpack  3 eqw  4 row_word  5 live         *)
(*           6 append_row  7 hyps_union  8 hyps_find                         *)
(*   slots   0 type rows  6 de Bruijn rows  12 term rows  14 term count      *)
(*           18 theorem rows  20 theorem count  26 Y count                   *)
(* ------------------------------------------------------------------------- *)

let pl_leaf = new_definition
 `pl_leaf (st:int64 list)
          ((cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk):pstate) k (pay:num)
          (ns':nstate) <=>
    let a0 = cw(val(EL 10 st)) and a1 = cw(val(EL 11 st)) and v1 = cw(val(EL 12 st)) in
    (val(EL 0 st) = 0 /\ val(EL 1 st) = 0 /\
     ?tys'. pl_intern tys a0 a1 k pay tys' /\
            ns' = (ctx,nms,tys',ntms,dbs,ths,nmap,ymap,drops,pol)) \/
    (val(EL 0 st) = 0 /\ val(EL 1 st) = 6 /\
     ?dbs'. pl_intern dbs a0 a1 k pay dbs' /\
            ns' = (ctx,nms,tys,ntms,dbs',ths,nmap,ymap,drops,pol)) \/
    (val(EL 0 st) = 1 /\ pl_pack a0 a1 k pay /\
     ns' = (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)) \/
    (val(EL 0 st) = 2 /\ pl_unpack a0 a1 k pay /\
     ns' = (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)) \/
    (val(EL 0 st) = 3 /\ pl_eqw a0 a1 k pay /\
     ns' = (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)) \/
    (val(EL 0 st) = 4 /\ val(EL 1 st) = 0 /\
     pl_roww (\i w. pl_f3 (EL i tys) w) (LENGTH tys) 2 a0 a1 v1 k pay /\
     ns' = (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)) \/
    (val(EL 0 st) = 4 /\ val(EL 1 st) = 6 /\
     pl_roww (\i w. pl_f3 (EL i dbs) w) (LENGTH dbs) 2 a0 a1 v1 k pay /\
     ns' = (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)) \/
    (val(EL 0 st) = 4 /\ val(EL 1 st) = 12 /\
     pl_roww (\i w. pl_f5 (EL i ntms) w) (LENGTH ntms) 5 a0 a1 v1 k pay /\
     ns' = (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)) \/
    (val(EL 0 st) = 4 /\ val(EL 1 st) = 18 /\
     pl_roww (\i w. pl_f2 (EL i ths) w) (LENGTH ths) 2 a0 a1 v1 k pay /\
     ns' = (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)) \/
    (val(EL 0 st) = 5 /\ val(EL 1 st) = 14 /\ pl_live 2 (LENGTH ntms) drops a0 k pay /\
     ns' = (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)) \/
    (val(EL 0 st) = 5 /\ val(EL 1 st) = 20 /\ pl_live 3 (LENGTH ths) drops a0 k pay /\
     ns' = (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)) \/
    (val(EL 0 st) = 5 /\ val(EL 1 st) = 26 /\ pl_live 1 (LENGTH ymap) drops a0 k pay /\
     ns' = (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)) \/
    (val(EL 0 st) = 6 /\ val(EL 1 st) = 18 /\
     ?ths'. pl_append_th ths v1 a0 a1 k pay ths' /\
            ns' = (ctx,nms,tys,ntms,dbs,ths',nmap,ymap,drops,pol)) \/
    (val(EL 0 st) = 7 /\ val(EL 1 st) = 6 /\
     ?dbs'. pl_union dbs a0 a1 k pay dbs' /\
            ns' = (ctx,nms,tys,ntms,dbs',ths,nmap,ymap,drops,pol)) \/
    (val(EL 0 st) = 8 /\ val(EL 1 st) = 6 /\ pl_findl ntms drops dbs stk a0 a1 k pay /\
     ns' = (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol))`;;

(* The control words after a step: the payload at the step's word. *)
let pl_set = new_definition
 `pl_set (cw:num->num) n (v:num) = \x. if x = n then v else cw x`;;

(* A run of the steps from index i: (outcome, index of the step that ended  *)
(* the plan, final state), as drv_sem.                                       *)
let pl_run = define
 `(pl_run [] i (s:pstate) (r:num#num#pstate) <=> r = (1,i,s)) /\
  (pl_run (CONS st sts) i s r <=>
     ?k pay ns'. pl_leaf st s k pay ns' /\
                 (if k = 1 then pl_run sts (i + 1) (pl_set (FST s) (val(EL 17 st)) pay,ns',SND(SND s)) r
                  else r = (k,i,(pl_set (FST s) (val(EL 17 st)) pay,ns',SND(SND s)))))`;;

(* ------------------------------------------------------------------------- *)
(* The invariant the plans keep: the native invariant and a HOLR state it   *)
(* simulates (so NAT_STEP_SIM keeps both); control words 0..6               *)
(* hold 0..6; the bootstrap rows the plans name (names bool, fun, =; type    *)
(* rows nil, bool, [bool]; the de Bruijn nil); canonical keys, no duplicate  *)
(* rows; the tables below 2^60 rows; every theorem's hypotheses a sorted    *)
(* list row.                                                                 *)
(* ------------------------------------------------------------------------- *)

let pl_inv = new_definition
 `pl_inv ((cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk):pstate) <=>
    nat_ok (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\
    (?hr. nat_sim (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) hr) /\
    (!n. n <= 6 ==> cw n = n) /\
    3 <= LENGTH nms /\ EL 0 nms = "bool" /\ EL 1 nms = "fun" /\ EL 2 nms = "=" /\
    4 <= LENGTH tys /\ EL 0 tys = (2,0,0) /\ EL 1 tys = (1,0,0) /\ EL 3 tys = (3,1,0) /\
    1 <= LENGTH dbs /\ EL 0 dbs = (5,0,0) /\
    nat_keys tys dbs /\ keys_distinct tys /\ keys_distinct dbs /\
    LENGTH nms < 2 EXP 60 /\ LENGTH tys < 2 EXP 60 /\ LENGTH ntms < 2 EXP 60 /\
    LENGTH dbs < 2 EXP 60 /\ LENGTH ths < 2 EXP 60 /\
    (!h. h < LENGTH ths ==> SND(EL h ths) < LENGTH dbs /\
                            ?ids. pl_ids dbs (FST(EL h ths)) ids /\ PAIRWISE (<) ids)`;;

(* ------------------------------------------------------------------------- *)
(* Steps as data, and the plans' fragments (PLANS.txt, sections 2 and 4).    *)
(* ------------------------------------------------------------------------- *)

let pl_nul = 56;;
let pl_step leaf bs a0 a1 vs res =
  let rec pad l n x = if length l >= n then l else pad (l @ [x]) n x in
  let ws = [leaf] @ pad bs 9 pl_nul @ [a0; a1] @ pad vs 5 0 @ [res] in
  mk_list(map (fun n -> mk_comb(`word:num->int64`, mk_small_numeral n)) ws, `:int64`);;

(* Leaves and binding lists. *)
let pl_INTERN = 0 and pl_PACK = 1 and pl_UNPACK = 2 and pl_EQW = 3 and pl_ROWW = 4
and pl_LIVE = 5 and pl_APPEND = 6 and pl_UNION = 7 and pl_FINDL = 8;;
let pl_TY = [0; 2; 4] and pl_DB = [6; 8; 10]               (* intern16: rows, slots, count *)
and pl_TYRW = [0; 4] and pl_DBRW = [6; 10] and pl_TM = [12; 14] and pl_TH = [18; 20]
                                                          (* row_word: rows, count *)
and pl_TMLIVE = [14; 16] and pl_THLIVE = [20; 22]          (* live: count, marks *)
and pl_UNIONB = [6; 8; 10; 42]                             (* hyps_union: interner, work *)
and pl_FINDB = [6; 8; 10; 12; 14; 16; 40; 42];;            (* hyps_find *)
(* Control words: K0..K6 = 0..6, OP0..OP3 = 8..11, NL 12, LS 13; 17..22 the      *)
(* reader's (PLANS.txt, section 10); 24.. temporaries.                       *)
let pl_OP0 = 8 and pl_OP1 = 9 and pl_OP2 = 10 and pl_NL = 12 and pl_LS = 13;;

(* A plan under construction: each step's payload goes to a fresh temporary. *)
let pl_buf = ref ([]:term list) and pl_next = ref 24;;
let pl_begin () = pl_buf := []; pl_next := 24;;
let pl_emit leaf bs a0 a1 vs =
  let r = !pl_next in pl_next := r + 1; pl_buf := !pl_buf @ [pl_step leaf bs a0 a1 vs r]; r;;
let pl_plan () = mk_list(!pl_buf, `:int64 list`);;

let pl_live_tm i = pl_emit pl_LIVE pl_TMLIVE i 0 [];;
let pl_live_th i = pl_emit pl_LIVE pl_THLIVE i 0 [];;
let pl_f_ty i w = pl_emit pl_ROWW pl_TYRW i w [2];;
let pl_f_db i w = pl_emit pl_ROWW pl_DBRW i w [2];;
let pl_f_tm i w = pl_emit pl_ROWW pl_TM i w [5];;
let pl_f_th i w = pl_emit pl_ROWW pl_TH i w [2];;
let pl_eqw_c a b = pl_emit pl_EQW [] a b [];;
let pl_split_db c tag =
  let x = pl_f_db c 0 in let a = pl_emit pl_UNPACK [] x tag [] in let b = pl_f_db c 1 in (a,b);;
let pl_split_ty c tag =
  let x = pl_f_ty c 0 in let a = pl_emit pl_UNPACK [] x tag [] in let b = pl_f_ty c 1 in (a,b);;
let pl_ity tag a b = let x = pl_emit pl_PACK [] a tag [] in pl_emit pl_INTERN pl_TY x b [];;
let pl_idb tag a b = let x = pl_emit pl_PACK [] a tag [] in pl_emit pl_INTERN pl_DB x b [];;
(* EQPARTS: c is (=) l r, (=) at type ty; returns (e, l, r, ty), e the row of (=) l. *)
let pl_eqparts c =
  let (e,r) = pl_split_db c 3 in let (q,l) = pl_split_db e 3 in
  let (nm,ty) = pl_split_db q 2 in let _ = pl_eqw_c nm 2 in (e,l,r,ty);;
(* FUNARGS: y is d -> c. *)
let pl_funargs y =
  let (nm,ls) = pl_split_ty y 1 in let _ = pl_eqw_c nm 1 in
  let (d,rs) = pl_split_ty ls 3 in let (c,tl) = pl_split_ty rs 3 in
  let _ = pl_eqw_c tl 0 in (d,c);;
(* EQTY: y -> y -> bool. *)
let pl_eqty y =
  let l1 = pl_ity 3 y 3 in let f1 = pl_ity 1 1 l1 in let l2 = pl_ity 3 f1 0 in
  let l3 = pl_ity 3 y l2 in pl_ity 1 1 l3;;
(* EQBUILD: the row of l = r at type y. *)
let pl_eqbuild y l r =
  let e = pl_eqty y in let q = pl_idb 2 2 e in let x = pl_idb 3 q l in pl_idb 3 x r;;
let pl_append_c hk c = pl_emit pl_APPEND pl_TH hk c [2];;
let pl_union_c a b = pl_emit pl_UNION pl_UNIONB a b [];;
let pl_findl_c () = pl_emit pl_FINDL pl_FINDB pl_LS pl_NL [];;

(* ASSUME t (OP0 = t): live t [REFUSED]; its type row; eqw bool [REFUSED];  *)
(* its image p; intern the list [p]; append ([p], p).                        *)
pl_begin();;
let _ = let _ = pl_live_tm pl_OP0 in let y = pl_f_tm pl_OP0 3 in let _ = pl_eqw_c y 1 in
        let p = pl_f_tm pl_OP0 4 in let hk = pl_idb 6 p 0 in pl_append_c hk p;;
let pl_plan_assume = new_definition(mk_eq(`pl_plan_assume:(int64 list)list`, pl_plan()));;

(* REFL t (OP0 = t): live t [REFUSED]; its type y and image d; the row of   *)
(* d = d at y; append ([], that row).                                        *)
pl_begin();;
let _ = let _ = pl_live_tm pl_OP0 in let y = pl_f_tm pl_OP0 3 in let d = pl_f_tm pl_OP0 4 in
        let k = pl_eqbuild y d d in pl_append_c 0 k;;
let pl_plan_refl = new_definition(mk_eq(`pl_plan_refl:(int64 list)list`, pl_plan()));;

(* EQ_MP h1 h2 (OP0, OP1): both live [REFUSED]; h1's conclusion p = q      *)
(* [REFUSED otherwise]; h2's conclusion p [REFUSED otherwise]; the union of *)
(* their hypotheses; append (union, q).                                      *)
pl_begin();;
let _ = let _ = pl_live_th pl_OP0 in let _ = pl_live_th pl_OP1 in
        let c = pl_f_th pl_OP0 1 in let (_,p,q,_) = pl_eqparts c in
        let c2 = pl_f_th pl_OP1 1 in let _ = pl_eqw_c p c2 in
        let h1 = pl_f_th pl_OP0 0 in let h2 = pl_f_th pl_OP1 0 in
        let hk = pl_union_c h1 h2 in pl_append_c hk q;;
let pl_plan_eqmp = new_definition(mk_eq(`pl_plan_eqmp:(int64 list)list`, pl_plan()));;

(* TRANS h1 h2: both live; l = m and m' = r [REFUSED otherwise]; m = m'     *)
(* [REFUSED otherwise]; the row of ((=) l) r; union; append.                 *)
pl_begin();;
let _ = let _ = pl_live_th pl_OP0 in let _ = pl_live_th pl_OP1 in
        let c1 = pl_f_th pl_OP0 1 in let (e1,_,m1,_) = pl_eqparts c1 in
        let c2 = pl_f_th pl_OP1 1 in let (_,m2,r,_) = pl_eqparts c2 in
        let _ = pl_eqw_c m1 m2 in let k = pl_idb 3 e1 r in
        let h1 = pl_f_th pl_OP0 0 in let h2 = pl_f_th pl_OP1 0 in
        let hk = pl_union_c h1 h2 in pl_append_c hk k;;
let pl_plan_trans = new_definition(mk_eq(`pl_plan_trans:(int64 list)list`, pl_plan()));;

(* MK_COMB h1 h2: both live; f = g at (tx->ty)->(tx->ty)->bool and a = b at *)
(* tx->tx->bool [REFUSED otherwise]; the row of f a = g b at ty; union;      *)
(* append.                                                                   *)
pl_begin();;
let _ = let _ = pl_live_th pl_OP0 in let _ = pl_live_th pl_OP1 in
        let c1 = pl_f_th pl_OP0 1 in let (_,f,g,t1) = pl_eqparts c1 in
        let c2 = pl_f_th pl_OP1 1 in let (_,a,b,t2) = pl_eqparts c2 in
        let (fy,r1) = pl_funargs t1 in let (fy',b1) = pl_funargs r1 in
        let _ = pl_eqw_c fy' fy in let _ = pl_eqw_c b1 1 in
        let (tx,ty) = pl_funargs fy in
        let (tx2,r2) = pl_funargs t2 in let _ = pl_eqw_c tx2 tx in
        let (tx3,b2) = pl_funargs r2 in let _ = pl_eqw_c tx3 tx in let _ = pl_eqw_c b2 1 in
        let fa = pl_idb 3 f a in let gb = pl_idb 3 g b in
        let k = pl_eqbuild ty fa gb in
        let h1 = pl_f_th pl_OP0 0 in let h2 = pl_f_th pl_OP1 0 in
        let hk = pl_union_c h1 h2 in pl_append_c hk k;;
let pl_plan_mkcomb = new_definition(mk_eq(`pl_plan_mkcomb:(int64 list)list`, pl_plan()));;

(* EXPECT_ALPHA h hl c (OP0 = h, OP2 = c, hl in the stack at LS, NL): h and *)
(* c live; h's conclusion is c's image; the listed terms are live and of    *)
(* type bool and the sorted list of their images is a row, h's hypotheses.  *)
(* No row is written.                                                        *)
pl_begin();;
let _ = let _ = pl_live_th pl_OP0 in let _ = pl_live_tm pl_OP2 in
        let k = pl_f_th pl_OP0 1 in let i = pl_f_tm pl_OP2 4 in let _ = pl_eqw_c k i in
        let l = pl_findl_c () in let hs = pl_f_th pl_OP0 0 in pl_eqw_c l hs;;
let pl_plan_expect_alpha = new_definition(mk_eq(`pl_plan_expect_alpha:(int64 list)list`, pl_plan()));;

(* ------------------------------------------------------------------------- *)
(* Arithmetic of keys.                                                       *)
(* ------------------------------------------------------------------------- *)

let PL_TAG_MODDIV = prove
 (`!t a. t < 8 ==> (t + 8 * a) MOD 8 = t /\ (t + 8 * a) DIV 8 = a`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ARITH_EQ; ADD_CLAUSES]);;

let PL_SMALL = ARITH_RULE
 `0 < 8 /\ 1 < 8 /\ 2 < 8 /\ 3 < 8 /\ 4 < 8 /\ 5 < 8 /\ 6 < 8 /\ 7 < 8`;;

let PL_KEY_PACK = prove
 (`!tag a b. tag < 8 ==> pl_key (tag + 8 * a) b = (tag,a,b)`,
  SIMP_TAC[pl_key; PL_TAG_MODDIV]);;

let PL_VAL_WORD = prove
 (`!n. n < 2 EXP 60 ==> val(word n:int64) = n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;

let PL_WORD_EQ = prove
 (`!m n. m < 2 EXP 60 /\ n < 2 EXP 60 ==> (word m:int64 = word n <=> m = n)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN ASM_SIMP_TAC[PL_VAL_WORD]);;

(* ------------------------------------------------------------------------- *)
(* The symbolic executor: pl_run over a concrete plan, step by step. Each    *)
(* leaf's effect is simplified with the facts of the branch (and the        *)
(* invariant's facts about rows, PL_INV_ROWS, when they are assumptions), so *)
(* outcomes those facts exclude never become branches.                       *)
(* ------------------------------------------------------------------------- *)

let is_const_app name tm = try fst(dest_const(fst(strip_comb tm))) = name with Failure _ -> false;;
let PL_LEAF_TERM t = is_const_app "pl_leaf" t;;
let PL_LEAF_CONV =
  REWRITE_CONV[pl_leaf; LET_DEF; LET_END_DEF; pl_set] THENC DEPTH_CONV BETA_CONV THENC
  DEPTH_CONV EL_CONV THENC DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV THENC REWRITE_CONV[];;
let PL_NORM_CONV = DEPTH_CONV EL_CONV THENC DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV;;
let PL_SEMS = [pl_live; pl_eqw; pl_pack; pl_unpack; pl_roww; pl_intern; pl_append_th; pl_union; pl_findl;
               LET_DEF; LET_END_DEF];;
let PL_SIMPS = ref [pl_f2; pl_f3; pl_f5; pl_key; PL_TAG_MODDIV; PL_SMALL];;
let PL_COND_DISJ = prove
 (`!b x y. (if b then x else y) <=> b /\ x \/ ~b /\ y`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;
let PL_FACT_CONV asl =
  REWRITE_CONV PL_SEMS THENC PL_NORM_CONV THENC
  SIMP_CONV (!PL_SIMPS @ map snd asl) THENC PL_NORM_CONV THENC REWRITE_CONV[PL_COND_DISJ];;
let is_var_eq tm = is_eq tm && is_var(lhs tm) && not(free_in (lhs tm) (rhs tm));;
let rec PL_ASM_TCL th =
  let c = concl th in
  if is_conj c then CONJUNCTS_THEN PL_ASM_TCL th
  else if is_disj c then DISJ_CASES_THEN PL_ASM_TCL th
  else if is_exists c then CHOOSE_THEN PL_ASM_TCL th
  else if is_const_app "holr_live" c then
    ASSUME_TAC th THEN ASSUME_TAC(CONJUNCT1(REWRITE_RULE[holr_live] th))
  else ASSUME_TAC th;;
let PL_SUBST_ALL_TAC =
  REPEAT(FIRST_X_ASSUM(fun th -> if is_var_eq(concl th)
           then (SUBST_ALL_TAC th ORELSE (REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])))
           else failwith "PL_SUBST_ALL_TAC"));;
let PL_BOUND_TERMS tm =
  find_terms (fun t -> try let (op,args) = strip_comb t in
                           fst(dest_const op) = "<" && length args = 2 &&
                           is_const_app "LENGTH" (el 1 args)
                       with Failure _ -> false) tm;;
let PL_BOUNDS_TAC tm (asl,w) =
  let asms = map snd asl in
  let add b =
    let b' = rhs(concl(REWRITE_CONV asms b)) in
    if b' = `T` || exists (fun th -> concl th = b') asms then failwith "known" else
    let eq = SIMP_CONV (!PL_SIMPS @ asms) b' in
    if rand(concl eq) = `T` then EQT_ELIM eq else failwith "unproved" in
  MAP_EVERY ASSUME_TAC (mapfilter add (PL_BOUND_TERMS tm)) (asl,w);;
(* An outcome known only to be neither FIRED nor REFUSED decides pl_run's  *)
(* conditional through the branch's negated equations.                     *)
let PL_NEG_EQ_TAC (asl,w) =
  let negs = filter (fun th -> let c = concl th in
                       is_neg c && is_eq(dest_neg c) && is_var(lhs(dest_neg c)) &&
                       is_numeral(rhs(dest_neg c))) (map snd asl) in
  REWRITE_TAC negs (asl,w);;
let PL_STEP_TAC =
  GEN_REWRITE_TAC LAND_CONV [CONJUNCT2 pl_run] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV(fun t -> if PL_LEAF_TERM t then PL_LEAF_CONV t else failwith "PL_HEAD"))) THEN
  CONV_TAC(LAND_CONV PL_NORM_CONV) THEN
  REWRITE_TAC[FST; SND; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let raw = CONV_RULE (REWRITE_CONV PL_SEMS THENC PL_NORM_CONV) (CONJUNCT1 th) in
    PL_BOUNDS_TAC (concl raw) THEN
    W(fun (asl,_) ->
      let leaf = CONV_RULE (SIMP_CONV (!PL_SIMPS @ map snd asl) THENC PL_NORM_CONV THENC
                            REWRITE_CONV[PL_COND_DISJ]) raw in
      MP_TAC(CONJUNCT2 th) THEN PL_ASM_TCL leaf)) THEN
  PL_SUBST_ALL_TAC THEN REWRITE_TAC[ARITH_EQ] THEN PL_NEG_EQ_TAC;;
let PL_END_TAC = REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN PL_ASM_TCL THEN PL_SUBST_ALL_TAC;;
let rec PL_RUN_TAC g =
  let w = snd g in
  if not (is_imp w) then ALL_TAC g else
  let a = lhand w in
  let hname = try fst(dest_const(fst(strip_comb a))) with Failure _ -> "" in
  if hname = "pl_run" then
    let sts = List.hd(snd(strip_comb a)) in
    if is_const sts && fst(dest_const sts) = "NIL" then (GEN_REWRITE_TAC LAND_CONV [CONJUNCT1 pl_run] THEN PL_END_TAC) g
    else (PL_STEP_TAC THEN PL_RUN_TAC) g
  else if is_eq a then PL_END_TAC g
  else ALL_TAC g;;

(* ------------------------------------------------------------------------- *)
(* Facts about the invariant and the rows.                                   *)
(* ------------------------------------------------------------------------- *)

let PL_K = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
     ==> cw 0 = 0 /\ cw 1 = 1 /\ cw 2 = 2 /\ cw 3 = 3 /\ cw 4 = 4 /\ cw 5 = 5 /\ cw 6 = 6`,
  REWRITE_TAC[pl_inv] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;

let PL_INV_NAT = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
     ==> nat_ok (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\
         nat_rows_ok (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\
         nat_canon nms tys dbs`,
  REWRITE_TAC[pl_inv; nat_ok] THEN MESON_TAC[]);;

let PL_TM_ROW = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk t.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ t < LENGTH ntms
     ==> ?p. fdtm nms tys ntms t p /\ fdty nms tys (ntm_ty (EL t ntms)) (htypeof p) /\
             fddb nms tys dbs (ntm_db (EL t ntms)) (hdb p)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o MATCH_MP PL_INV_NAT) THEN
  REWRITE_TAC[nat_rows_ok; fibre_inv] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:num` o check (fun th -> can (find_term ((=) `fibre_tm_ok`)) (concl th))) THEN
  ASM_REWRITE_TAC[fibre_tm_ok] THEN MESON_TAC[]);;

let PL_CANON = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
     ==> (!i j ty. fdty nms tys i ty /\ fdty nms tys j ty ==> i = j) /\
         (!i j t. fddb nms tys dbs i t /\ fddb nms tys dbs j t ==> i = j) /\
         (!i j l. fddbs nms tys dbs i l /\ fddbs nms tys dbs j l ==> i = j)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o MATCH_MP PL_INV_NAT) THEN
  REWRITE_TAC[nat_canon; fdty_same; fddb_same] THEN MESON_TAC[]);;

let PL_BOOL = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
     ==> fdty nms tys 1 HBool /\ fddbs nms tys dbs 0 []`,
  REWRITE_TAC[pl_inv; HBool] THEN REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `TyApp "bool" [] = TyApp (EL 0 nms) []` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(el 1 (CONJUNCTS(SPEC_ALL fdty_RULES))) THEN
    MAP_EVERY EXISTS_TAC [`0`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(el 2 (CONJUNCTS(SPEC_ALL fdty_RULES))) THEN
    MAP_EVERY EXISTS_TAC [`0`; `0`] THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC(el 5 (CONJUNCTS(SPEC_ALL fddb_RULES))) THEN
    MAP_EVERY EXISTS_TAC [`0`; `0`] THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let PL_IDS_APPEND = prove
 (`!ids D E l. pl_ids D l ids ==> pl_ids (APPEND D E) l ids`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[pl_ids] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LENGTH_APPEND; EL_APPEND; ARITH_RULE `l < a ==> l < a + b`] THEN
  ASM_MESON_TAC[]);;

let PL_IDS_BOUND = prove
 (`!ids D l. pl_ids D l ids ==> l < LENGTH D`,
  LIST_INDUCT_TAC THEN SIMP_TAC[pl_ids]);;

(* A row of either table decodes: its tag and the fields a decoding needs.  *)
let PL_DB_DECODES = prove
 (`!nms tys dbs c.
     (?t. fddb nms tys dbs c t) \/ (?l. fddbs nms tys dbs c l)
     ==> c < LENGTH dbs /\
         (FST(EL c dbs) = 0 \/ FST(EL c dbs) = 2
          ==> FST(SND(EL c dbs)) < LENGTH nms /\ SND(SND(EL c dbs)) < LENGTH tys) /\
         (FST(EL c dbs) = 4 ==> FST(SND(EL c dbs)) < LENGTH tys)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[fddb_CASES] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_MESON_TAC[FDTY_BOUND]);;

let PL_TY_DECODES = prove
 (`!nms tys y.
     (?t. fdty nms tys y t) \/ (?l. fdtys nms tys y l)
     ==> y < LENGTH tys /\ (FST(EL y tys) = 0 \/ FST(EL y tys) = 1 ==> FST(SND(EL y tys)) < LENGTH nms)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[fdty_CASES] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let PL_KEYBOUND_TAC v tbl key =
  X_GEN_TAC v THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC v o check (fun th -> can (find_term ((=) key)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if can (find_term ((=) (mk_comb(mk_comb(`EL:num->(num#num#num)list->num#num#num`, v), tbl)))) (concl th) ||
                                    (is_comb(concl th) && can (find_term ((=) v)) (concl th) && not(is_forall(concl th)))
                                 then MP_TAC th else failwith "")) THEN
  SPEC_TAC(mk_comb(mk_comb(`EL:num->(num#num#num)list->num#num#num`, v), tbl),`r:num#num#num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; ty_key_ok; db_key_ok] THEN ARITH_TAC;;

(* The facts about rows the executor's simplification uses. *)
let PL_INV_ROWS = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
     ==> (!c. c < LENGTH dbs ==> FST(EL c dbs) < 8) /\
         (!c. c < LENGTH tys ==> FST(EL c tys) < 8) /\
         (!c. c < LENGTH dbs ==> c < 2 EXP 60) /\
         (!c. c < LENGTH tys ==> c < 2 EXP 60) /\
         (!c. c < LENGTH nms ==> c < 2 EXP 60) /\
         (!h. h < LENGTH ths ==> FST(EL h ths) < LENGTH dbs /\ SND(EL h ths) < LENGTH dbs) /\
         (!t. t < LENGTH ntms ==> ntm_ty (EL t ntms) < LENGTH tys /\ ntm_db (EL t ntms) < LENGTH dbs) /\
         (!c. c < LENGTH dbs /\ (FST(EL c dbs) = 3 \/ FST(EL c dbs) = 6)
              ==> FST(SND(EL c dbs)) < LENGTH dbs /\ SND(SND(EL c dbs)) < LENGTH dbs) /\
         (!c. c < LENGTH dbs /\ (FST(EL c dbs) = 0 \/ FST(EL c dbs) = 2)
              ==> FST(SND(EL c dbs)) < LENGTH nms /\ SND(SND(EL c dbs)) < LENGTH tys) /\
         (!y. y < LENGTH tys /\ FST(EL y tys) = 3
              ==> FST(SND(EL y tys)) < LENGTH tys /\ SND(SND(EL y tys)) < LENGTH tys) /\
         (!y. y < LENGTH tys /\ FST(EL y tys) = 1
              ==> FST(SND(EL y tys)) < LENGTH nms /\ SND(SND(EL y tys)) < LENGTH tys)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[nat_ok; nat_canon; nat_rows_ok; fibre_inv] o
              CONJUNCT1 o MATCH_MP PL_INV_NAT) THEN
  FIRST_ASSUM(fun th -> if is_const_app "pl_inv" (concl th)
                        then STRIP_ASSUME_TAC(REWRITE_RULE[pl_inv; nat_keys] th) else failwith "") THEN
  REPEAT CONJ_TAC THENL
   [PL_KEYBOUND_TAC `c:num` `dbs:(num#num#num)list` `db_key_ok`;
    PL_KEYBOUND_TAC `c:num` `tys:(num#num#num)list` `ty_key_ok`;
    ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    X_GEN_TAC `h:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `h:num` o check (fun th -> can (find_term ((=) `pl_ids`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[PL_IDS_BOUND];
    X_GEN_TAC `t:num` THEN DISCH_TAC THEN MP_TAC(SPEC_ALL PL_TM_ROW) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[FDTY_BOUND; FDDB_BOUND];
    PL_KEYBOUND_TAC `c:num` `dbs:(num#num#num)list` `db_key_ok`;
    X_GEN_TAC `c:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`; `c:num`] PL_DB_DECODES) THEN
    (ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_SIMP_TAC[]]);
    PL_KEYBOUND_TAC `y:num` `tys:(num#num#num)list` `ty_key_ok`;
    X_GEN_TAC `y:num` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `y:num`] PL_TY_DECODES) THEN
      ANTS_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:num` o check (fun th -> can (find_term ((=) `fibre_ty_ok`)) (concl th))) THEN
      ASM_REWRITE_TAC[fibre_ty_ok] THEN MESON_TAC[];
      UNDISCH_TAC `FST(EL y (tys:(num#num#num)list)) = 1` THEN
      UNDISCH_TAC `y < LENGTH (tys:(num#num#num)list)` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:num` o check (fun th -> can (find_term ((=) `ty_key_ok`)) (concl th))) THEN
      MATCH_MP_TAC(TAUT `(a ==> b ==> c ==> d) ==> (b ==> a) ==> b ==> c ==> d`) THEN
      SPEC_TAC(`EL y (tys:(num#num#num)list)`,`r:num#num#num`) THEN
      REWRITE_TAC[FORALL_PAIR_THM; ty_key_ok] THEN ARITH_TAC]]);;

let PL_TYPE_BOOL = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk y ty.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ fdty nms tys y ty
     ==> (y = 1 <=> ty = HBool)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_BOOL) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_CANON) THEN
  EQ_TAC THEN DISCH_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[FDTY_FUNCTIONAL];
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[]]);;

let pl_inv_thm_goal = `!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk cw' r mt md hk k.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) r
              (ctx,nms,APPEND tys mt,ntms,APPEND dbs md,APPEND ths [(hk,k)],nmap,ymap,drops,pol) /\
     (!n. n <= 6 ==> cw' n = cw n) /\
     nat_keys (APPEND tys mt) (APPEND dbs md) /\
     keys_distinct (APPEND tys mt) /\ keys_distinct (APPEND dbs md) /\
     LENGTH tys + LENGTH mt < 2 EXP 60 /\ LENGTH dbs + LENGTH md < 2 EXP 60 /\
     LENGTH ths + 1 < 2 EXP 60 /\ k < LENGTH dbs + LENGTH md /\
     (?ids. pl_ids (APPEND dbs md) hk ids /\ PAIRWISE (<) ids)
     ==> pl_inv (cw',(ctx,nms,APPEND tys mt,ntms,APPEND dbs md,APPEND ths [(hk,k)],nmap,ymap,drops,pol),stk)`;;
let PL_INV_THM_STEP = prove(pl_inv_thm_goal,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_inv] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate`; `r:holr_record`;
                `(ctx,nms,APPEND tys mt,ntms,APPEND dbs md,APPEND ths [(hk,k)],nmap,ymap,drops,pol):nstate`;
                `hr:hrstate`] NAT_STEP_SIM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `hr':hrstate` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[EL_APPEND; ARITH_RULE `4 <= l ==> 0 < l`];
    ASM_SIMP_TAC[EL_APPEND; ARITH_RULE `4 <= l ==> 1 < l`];
    ASM_SIMP_TAC[EL_APPEND; ARITH_RULE `4 <= l ==> 3 < l`];
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[EL_APPEND; ARITH_RULE `1 <= l ==> 0 < l`];
    ASM_ARITH_TAC;
    X_GEN_TAC `h:num` THEN DISCH_TAC THEN REWRITE_TAC[EL_APPEND] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `h:num` o check (fun th -> can (find_term ((=) `pl_ids`)) (concl th) &&
                                                       is_forall(concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_MESON_TAC[PL_IDS_APPEND];
      SUBGOAL_THEN `h - LENGTH (ths:(num#num)list) = 0` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[EL; HD; FST; SND] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]]);;

let PL_DB_SNOC = prove
 (`!tys dbs row. nat_keys tys dbs /\ keys_distinct dbs /\ ~MEM row dbs /\ db_key_ok (LENGTH dbs) row
                 ==> nat_keys tys (APPEND dbs [row]) /\ keys_distinct (APPEND dbs [row])`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`tys:(num#num#num)list`; `dbs:(num#num#num)list`; `[]:(num#num#num)list`;
                   `[row]:(num#num#num)list`] NAT_KEYS_APPEND) THEN
    REWRITE_TAC[APPEND_NIL; LENGTH; CONJUNCT1 LT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `d:num` THEN
    REWRITE_TAC[ARITH_RULE `d < SUC 0 <=> d = 0`] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[EL; HD; ADD_CLAUSES];
    MATCH_MP_TAC KEYS_DISTINCT_SNOC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MEM_EL]]);;

let PL_NAMES_INJ = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) ==> NAMES_INJ nms`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o MATCH_MP PL_INV_NAT) THEN
  REWRITE_TAC[nat_canon; NAMES_INJ] THEN MESON_TAC[]);;

let PL_FDDB_APPEND = prove
 (`!nms tys dbs md. (!i t. fddb nms tys dbs i t ==> fddb nms tys (APPEND dbs md) i t) /\
                    (!i l. fddbs nms tys dbs i l ==> fddbs nms tys (APPEND dbs md) i l)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
                `[]:string list`; `[]:(num#num#num)list`; `md:(num#num#num)list`] FDDB_EXTEND) THEN
  REWRITE_TAC[APPEND_NIL]);;

let FDDBS_CONS = el 6 (CONJUNCTS(SPEC_ALL fddb_RULES));;
let is_pl_inv tm = is_const_app "pl_inv" tm;;
let PL_INV_ASM ttac = FIRST_ASSUM(fun th -> if is_pl_inv(concl th) then ttac th else failwith "PL_INV_ASM");;
let PL_INV_FACTS_TAC = PL_INV_ASM(fun inv -> STRIP_ASSUME_TAC(REWRITE_RULE[pl_inv] inv));;
let PL_ROWS_TAC = PL_INV_ASM(fun inv -> STRIP_ASSUME_TAC(CONV_RULE NUM_REDUCE_CONV (MATCH_MP PL_INV_ROWS inv)));;
let PL_SET_LOW_TAC =
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[pl_set] THEN
  REPEAT(COND_CASES_TAC THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_ARITH_TAC; ALL_TAC]) THEN REFL_TAC;;
let PL_STRIP_INV_TAC =
  ASSUM_LIST(fun ths -> STRIP_ASSUME_TAC(REWRITE_RULE[pl_inv]
    (find (fun th -> is_pl_inv(concl th)) ths)));;

(* The start of every plan's proof: the operands, K0..K6 and the row facts. *)
let PL_START_TAC plan =
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  REPEAT(W(fun (_,w) -> if is_imp w && not(is_const_app "pl_run" (lhand w)) then DISCH_TAC else NO_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_K) THEN PL_ROWS_TAC THEN
  REWRITE_TAC[plan] THEN PL_RUN_TAC;;


(* ------------------------------------------------------------------------- *)
(* Equations and hypothesis lists: rows read back as terms.                  *)
(* ------------------------------------------------------------------------- *)

let FDDB_COMB_INV = prove
 (`!nms tys dbs c s t.
     fddb nms tys dbs c (hdbComb s t) <=>
     c < LENGTH dbs /\ FST(EL c dbs) = 3 /\
     fddb nms tys dbs (FST(SND(EL c dbs))) s /\ fddb nms tys dbs (SND(SND(EL c dbs))) t`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [CONJUNCT1(SPEC_ALL fddb_CASES)] THEN
  REWRITE_TAC[hdbterm_DISTINCT; hdbterm_INJ] THEN
  SPEC_TAC(`EL c (dbs:(num#num#num)list)`,`r:num#num#num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; FST; SND] THEN MESON_TAC[]);;

let FDDB_CONST_INV = prove
 (`!nms tys dbs c nm ty.
     fddb nms tys dbs c (hdbConst nm ty) <=>
     c < LENGTH dbs /\ FST(EL c dbs) = 2 /\ FST(SND(EL c dbs)) < LENGTH nms /\
     EL (FST(SND(EL c dbs))) nms = nm /\ fdty nms tys (SND(SND(EL c dbs))) ty`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [CONJUNCT1(SPEC_ALL fddb_CASES)] THEN
  REWRITE_TAC[hdbterm_DISTINCT; hdbterm_INJ] THEN
  SPEC_TAC(`EL c (dbs:(num#num#num)list)`,`r:num#num#num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; FST; SND] THEN MESON_TAC[]);;

let FDDB_TAG_INV = prove
 (`!nms tys dbs c X.
     fddb nms tys dbs c X
     ==> (FST(EL c dbs) = 3 ==> ?s t. X = hdbComb s t) /\
         (FST(EL c dbs) = 2 ==> ?nm ty. X = hdbConst nm ty)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [CONJUNCT1(SPEC_ALL fddb_CASES)] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[hdbterm_DISTINCT; hdbterm_INJ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[]);;

(* Row c holds an equation (=) l r at type ty: a combination of a         *)
(* combination whose head is the constant of name row 2 ("=").            *)
let pl_eq_ok = new_definition
 `pl_eq_ok (dbs:(num#num#num)list) c <=>
    FST(EL c dbs) = 3 /\ FST(EL (FST(SND(EL c dbs))) dbs) = 3 /\
    FST(EL (FST(SND(EL (FST(SND(EL c dbs))) dbs))) dbs) = 2 /\
    FST(SND(EL (FST(SND(EL (FST(SND(EL c dbs))) dbs))) dbs)) = 2`;;
let pl_eq_lhs = new_definition
 `pl_eq_lhs (dbs:(num#num#num)list) c = SND(SND(EL (FST(SND(EL c dbs))) dbs))`;;
let pl_eq_rhs = new_definition
 `pl_eq_rhs (dbs:(num#num#num)list) c = SND(SND(EL c dbs))`;;
let pl_eq_ty = new_definition
 `pl_eq_ty (dbs:(num#num#num)list) c = SND(SND(EL (FST(SND(EL (FST(SND(EL c dbs))) dbs))) dbs))`;;

let PL_EQ_DEC = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk c X.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ fddb nms tys dbs c X
     ==> ((?ty l r. X = hdbComb (hdbComb (hdbConst "=" ty) l) r) <=> pl_eq_ok dbs c) /\
         (!ty l r. X = hdbComb (hdbComb (hdbConst "=" ty) l) r
                   ==> fddb nms tys dbs (pl_eq_lhs dbs c) l /\ fddb nms tys dbs (pl_eq_rhs dbs c) r /\
                       fdty nms tys (pl_eq_ty dbs c) ty)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_NAMES_INJ) THEN
  PL_INV_FACTS_TAC THEN
  SUBGOAL_THEN `!ty l r. X = hdbComb (hdbComb (hdbConst "=" ty) l) r
                ==> pl_eq_ok dbs c /\ fddb nms tys dbs (pl_eq_lhs dbs c) l /\
                    fddb nms tys dbs (pl_eq_rhs dbs c) r /\ fdty nms tys (pl_eq_ty dbs c) ty`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "fddb" (concl th))) THEN
    REWRITE_TAC[FDDB_COMB_INV; FDDB_CONST_INV; pl_eq_ok; pl_eq_lhs; pl_eq_rhs; pl_eq_ty] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[NAMES_INJ] o
                  check (fun th -> is_const_app "NAMES_INJ" (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  EQ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[pl_eq_ok] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`; `c:num`; `X:hdbterm`]
               FDDB_TAG_INV) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN DISCH_THEN(X_CHOOSE_THEN `A:hdbterm` (X_CHOOSE_THEN `B:hdbterm` SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[FDDB_COMB_INV] o
                check (fun th -> is_const_app "fddb" (concl th))) THEN
  MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
                `FST(SND(EL c (dbs:(num#num#num)list)))`; `A:hdbterm`] FDDB_TAG_INV) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN DISCH_THEN(X_CHOOSE_THEN `A1:hdbterm` (X_CHOOSE_THEN `A2:hdbterm` SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[FDDB_COMB_INV] o
                check (fun th -> is_const_app "fddb" (concl th) &&
                                 can (find_term ((=) `hdbComb A1 A2`)) (concl th))) THEN
  MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
                `FST(SND(EL (FST(SND(EL c (dbs:(num#num#num)list)))) dbs))`; `A1:hdbterm`] FDDB_TAG_INV) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN DISCH_THEN(X_CHOOSE_THEN `nm:string` (X_CHOOSE_THEN `ty:holtype` SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[FDDB_CONST_INV] o
                check (fun th -> is_const_app "fddb" (concl th) &&
                                 can (find_term ((=) `hdbConst nm ty`)) (concl th))) THEN
  MAP_EVERY EXISTS_TAC [`ty:holtype`; `A2:hdbterm`; `B:hdbterm`] THEN
  REWRITE_TAC[hdbterm_INJ] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) && rhs(concl th) = `nm:string`)) THEN
  ASM_REWRITE_TAC[]);;


let PL_THM_DEC = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ h < LENGTH ths
     ==> (?C. fddb nms tys dbs (SND(EL h ths)) C) /\ (?hs. fddbs nms tys dbs (FST(EL h ths)) hs)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[nat_rows_ok; fibre_inv] o CONJUNCT1 o CONJUNCT2 o MATCH_MP PL_INV_NAT) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `EL h (ths:(num#num)list)` o
                check (fun th -> can (find_term ((=) `fibre_thm_ok`)) (concl th))) THEN
  SUBGOAL_THEN `MEM (EL h (ths:(num#num)list)) ths` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[MEM_EL]; ALL_TAC] THEN
  REWRITE_TAC[fibre_thm_ok] THEN MESON_TAC[]);;
let PL_VARS = [`cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
               `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
               `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`];;
let PL_SPEC extra th = SPECL (PL_VARS @ extra) th;;
let FDDB_FUN = prove
 (`!nms tys dbs i t u. fddb nms tys dbs i t /\ fddb nms tys dbs i u ==> t = u`,
  MESON_TAC[FDDB_FUNCTIONAL]);;
let pl_dec = new_definition
 `pl_dec nms tys (D:(num#num#num)list) x = @t. fddb nms tys D x t`;;

let PL_DEC = prove
 (`!nms tys D x t. fddb nms tys D x t ==> pl_dec nms tys D x = t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_dec] THEN
  SUBGOAL_THEN `fddb nms tys D x (@t. fddb nms tys D x t)` ASSUME_TAC THENL
   [CONV_TAC SELECT_CONV THEN ASM_MESON_TAC[]; ASM_MESON_TAC[FDDB_FUN]]);;

let PL_IDS_MAP = prove
 (`!ids nms tys D l. pl_ids D l ids /\ ALL (\x. ?t. fddb nms tys D x t) ids
                     ==> fddbs nms tys D l (MAP (pl_dec nms tys D) ids)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[pl_ids; ALL; MAP] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC(el 5 (CONJUNCTS(SPEC_ALL fddb_RULES))) THEN
    MAP_EVERY EXISTS_TAC [`0`; `0`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FDDBS_CONS THEN MAP_EVERY EXISTS_TAC [`h:num`; `b:num`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[PL_DEC]]);;

let PL_FDDBS_IDS = prove
 (`!ids nms tys D l hs. pl_ids D l ids /\ fddbs nms tys D l hs
                        ==> hs = MAP (pl_dec nms tys D) ids /\ ALL (\x. ?t. fddb nms tys D x t) ids`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[pl_ids; ALL; MAP] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[CONJUNCT2(SPEC_ALL fddb_CASES)] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_const_app "EL" (lhs(concl th)) then SUBST_ALL_TAC th
                          else failwith "") THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV o REWRITE_RULE[PAIR_EQ]) THEN
  ASM_MESON_TAC[PL_DEC]);;

let PL_UNION_STEP = prove
 (`!nms tys D md l1 l2 hk I1 I2 hs1 hs2.
     nat_keys tys D /\
     pl_ids D l1 I1 /\ pl_ids D l2 I2 /\ fddbs nms tys D l1 hs1 /\ fddbs nms tys D l2 hs2 /\
     (?ids. pl_ids (APPEND D md) hk ids /\ (!x. MEM x ids <=> MEM x I1 \/ MEM x I2)) /\
     pl_cells_new 6 (LENGTH D) (APPEND D md) (\a. MEM a I1 \/ MEM a I2)
     ==> nat_keys tys (APPEND D md) /\
         (!k. k < LENGTH D + LENGTH md /\ LENGTH D <= k ==> ?l. fddbs nms tys (APPEND D md) k l) /\
         (?hs. fddbs nms tys (APPEND D md) hk hs /\ (!z. MEM z hs1 \/ MEM z hs2 ==> MEM z hs))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. MEM x I1 \/ MEM x I2 ==> fddb nms tys (APPEND D md) x (pl_dec nms tys D x) /\
                                              pl_dec nms tys (APPEND D md) x = pl_dec nms tys D x`
    ASSUME_TAC THENL
   [X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?t. fddb nms tys D x t` (X_CHOOSE_TAC `t:hdbterm`) THENL
     [MP_TAC(SPECL [`I1:num list`; `nms:string list`; `tys:(num#num#num)list`; `D:(num#num#num)list`;
                    `l1:num`; `hs1:hdbterm list`] PL_FDDBS_IDS) THEN
      MP_TAC(SPECL [`I2:num list`; `nms:string list`; `tys:(num#num#num)list`; `D:(num#num#num)list`;
                    `l2:num`; `hs2:hdbterm list`] PL_FDDBS_IDS) THEN
      ASM_REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `fddb nms tys (APPEND D md) x t` ASSUME_TAC THENL
     [ASM_MESON_TAC[PL_FDDB_APPEND]; ALL_TAC] THEN
    ASM_MESON_TAC[PL_DEC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`tys:(num#num#num)list`; `D:(num#num#num)list`; `[]:(num#num#num)list`;
                   `md:(num#num#num)list`] NAT_KEYS_APPEND) THEN
    REWRITE_TAC[APPEND_NIL; LENGTH; CONJUNCT1 LT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `d:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `LENGTH (D:(num#num#num)list) + d` o REWRITE_RULE[pl_cells_new] o
                  check (fun th -> is_const_app "pl_cells_new" (concl th))) THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; LE_ADD; LT_ADD_LCANCEL; EL_APPEND; ARITH_RULE `~(a + d < a)`; ADD_SUB2] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[db_key_ok] THEN ASM_ARITH_TAC;
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `k:num` o REWRITE_RULE[pl_cells_new] o
                check (fun th -> is_const_app "pl_cells_new" (concl th))) THEN
    ASM_REWRITE_TAC[LENGTH_APPEND] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `b:num` (X_CHOOSE_THEN `bids:num list` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `CONS (pl_dec nms tys D a) (MAP (pl_dec nms tys (APPEND D md)) bids)` THEN
    MATCH_MP_TAC FDDBS_CONS THEN MAP_EVERY EXISTS_TAC [`a:num`; `b:num`] THEN
    ASM_SIMP_TAC[LENGTH_APPEND] THEN
    MATCH_MP_TAC PL_IDS_MAP THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "ALL" (concl th))) THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[];
    EXISTS_TAC `MAP (pl_dec nms tys (APPEND D md)) ids` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_IDS_MAP THEN ASM_REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[];
      MP_TAC(SPECL [`I1:num list`; `nms:string list`; `tys:(num#num#num)list`; `D:(num#num#num)list`;
                    `l1:num`; `hs1:hdbterm list`] PL_FDDBS_IDS) THEN
      MP_TAC(SPECL [`I2:num list`; `nms:string list`; `tys:(num#num#num)list`; `D:(num#num#num)list`;
                    `l2:num`; `hs2:hdbterm list`] PL_FDDBS_IDS) THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[MEM_MAP] THEN
      ASM_MESON_TAC[MEM_MAP]]]);;

let NAT_STEP_EQMP = el 13 (CONJUNCTS nat_step_RULES);;
let NAT_STEP_TRANS = el 8 (CONJUNCTS nat_step_RULES);;
let NAT_STEP_REFL = el 7 (CONJUNCTS nat_step_RULES);;
let NAT_STEP_MKCOMB = el 9 (CONJUNCTS nat_step_RULES);;
let NAT_STEP_EXPECT_ALPHA = el 17 (CONJUNCTS nat_step_RULES);;
(* A FIRED branch closed by the record's FIRED lemma: its intermediate      *)
(* payloads (variables of the lemma's premises only) are found by matching  *)
(* the premises against the branch's facts.                                 *)
let PL_WITNESS_TAC (asl,w) =
  let vs,body = strip_exists w in
  if vs = [] then ALL_TAC (asl,w) else
  let asms = map (concl o snd) asl in
  let rec solve inst cs =
    match cs with
      [] -> inst
    | c::rest ->
        let c' = vsubst inst c in
        if intersect (frees c') vs = [] then solve inst rest else
        (try let i = tryfind (fun a -> let (_,ins,_) = term_match [] c' a in
                                    if forall (fun (_,v) -> mem v vs) ins then ins else failwith "") asms in
             solve (i @ inst) rest
         with Failure _ -> solve inst rest) in
  let inst = solve [] (conjuncts body) in
  MAP_EVERY (fun v -> EXISTS_TAC (try rev_assoc v inst with Failure _ -> v)) vs (asl,w);;
let PL_FIRED_TAC th =
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_EQ]) THEN
  MATCH_MP_TAC(REWRITE_RULE[pl_eq_rhs; pl_eq_lhs] th) THEN CONV_TAC NUM_REDUCE_CONV THEN
  PL_WITNESS_TAC THEN ASM_REWRITE_TAC[pl_eq_ok] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_ARITH_TAC THEN NO_TAC) THEN
  TRY(PL_WITNESS_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN TRY PL_SET_LOW_TAC;;


(* ------------------------------------------------------------------------- *)
(* Tables after interning; sorted list rows.                                 *)
(* ------------------------------------------------------------------------- *)

(* What interning keeps of the tables: canonical keys, no duplicate rows,   *)
(* every type row valid in the context, every de Bruijn row decoding, and   *)
(* the bounds.                                                               *)
let pl_tabs_ok = new_definition
 `pl_tabs_ok ctx nms (tys:(num#num#num)list) (dbs:(num#num#num)list) <=>
    nat_keys tys dbs /\ keys_distinct tys /\ keys_distinct dbs /\
    (!i. i < LENGTH tys ==> fibre_ty_ok ctx nms tys i) /\
    (!i. i < LENGTH dbs ==> (?t. fddb nms tys dbs i t) \/ (?l. fddbs nms tys dbs i l)) /\
    LENGTH tys < 2 EXP 60 /\ LENGTH dbs < 2 EXP 60`;;

let PL_TABS_OK = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) ==> pl_tabs_ok ctx nms tys dbs`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[nat_ok; nat_canon; nat_rows_ok; fibre_inv] o
              CONJUNCT1 o MATCH_MP PL_INV_NAT) THEN
  PL_INV_FACTS_TAC THEN ASM_REWRITE_TAC[pl_tabs_ok]);;

let PL_EXPAND_ASM name defs =
  FIRST_X_ASSUM(fun th -> if is_const_app name (concl th) then STRIP_ASSUME_TAC(REWRITE_RULE defs th)
                          else failwith "PL_EXPAND_ASM");;
let PL_SUBST_TABLE_TAC =
  FIRST_X_ASSUM(fun th -> let c = concl th in
    if is_eq c && is_var(lhs c) && type_of(lhs c) = `:(num#num#num)list` then SUBST_ALL_TAC th
    else failwith "PL_SUBST_TABLE_TAC");;

let FIBRE_TY_OK_EXTEND = prove
 (`!ctx nms tys mt i. fibre_ty_ok ctx nms tys i ==> fibre_ty_ok ctx nms (APPEND tys mt) i`,
  REWRITE_TAC[fibre_ty_ok] THEN
  MESON_TAC[REWRITE_RULE[APPEND_NIL] (SPECL [`nms:string list`; `tys:(num#num#num)list`;
                                              `[]:string list`] FDTY_EXTEND)]);;

let PL_FDTY_APPEND = prove
 (`!nms tys mt. (!i t. fdty nms tys i t ==> fdty nms (APPEND tys mt) i t) /\
                (!i l. fdtys nms tys i l ==> fdtys nms (APPEND tys mt) i l)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `[]:string list`; `mt:(num#num#num)list`]
               FDTY_EXTEND) THEN REWRITE_TAC[APPEND_NIL]);;

let PL_FDDB_TYS_APPEND = prove
 (`!nms tys dbs mt. (!i t. fddb nms tys dbs i t ==> fddb nms (APPEND tys mt) dbs i t) /\
                    (!i l. fddbs nms tys dbs i l ==> fddbs nms (APPEND tys mt) dbs i l)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
                `[]:string list`; `mt:(num#num#num)list`; `[]:(num#num#num)list`] FDDB_EXTEND) THEN
  REWRITE_TAC[APPEND_NIL]);;

(* One type row interned: found, or appended (then valid and new). *)
let PL_TY_STEP = prove
 (`!ctx nms tys dbs key pay mt.
     pl_tabs_ok ctx nms tys dbs /\ pl_interned tys key pay mt /\ ty_key_ok (LENGTH tys) key /\
     fibre_ty_ok ctx nms (APPEND tys [key]) (LENGTH tys)
     ==> pl_tabs_ok ctx nms (APPEND tys mt) dbs /\ nat_tys_ok ctx nms tys mt /\
         pay < LENGTH (APPEND tys mt) /\ EL pay (APPEND tys mt) = key /\
         (!i X. fdty nms tys i X ==> fdty nms (APPEND tys mt) i X) /\
         (!i l. fdtys nms tys i l ==> fdtys nms (APPEND tys mt) i l) /\
         (!i t. fddb nms tys dbs i t ==> fddb nms (APPEND tys mt) dbs i t) /\
         (!i l. fddbs nms tys dbs i l ==> fddbs nms (APPEND tys mt) dbs i l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_interned] THEN STRIP_TAC THEN
  PL_SUBST_TABLE_TAC THEN
  ASM_REWRITE_TAC[APPEND_NIL; NAT_TYS_OK_NIL; PL_FDTY_APPEND; PL_FDDB_TYS_APPEND] THEN
  PL_EXPAND_ASM "pl_tabs_ok" [pl_tabs_ok] THEN
  ASM_SIMP_TAC[NAT_TYS_OK_ONE; LENGTH_APPEND; LENGTH; EL_APPEND; LT_REFL; SUB_REFL; EL; HD;
               ARITH_RULE `l < l + SUC 0`] THEN
  REWRITE_TAC[pl_tabs_ok; LENGTH_APPEND; LENGTH] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`tys:(num#num#num)list`; `dbs:(num#num#num)list`; `[key]:(num#num#num)list`;
                   `[]:(num#num#num)list`] NAT_KEYS_APPEND) THEN
    REWRITE_TAC[APPEND_NIL; LENGTH; CONJUNCT1 LT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `d:num` THEN
    REWRITE_TAC[ARITH_RULE `d < SUC 0 <=> d = 0`] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[EL; HD; ADD_CLAUSES];
    MATCH_MP_TAC KEYS_DISTINCT_SNOC THEN ASM_MESON_TAC[MEM_EL];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i < LENGTH (tys:(num#num#num)list)` THENL
     [ASM_MESON_TAC[FIBRE_TY_OK_EXTEND];
      SUBGOAL_THEN `i = LENGTH (tys:(num#num#num)list)` SUBST1_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ASM_MESON_TAC[PL_FDDB_TYS_APPEND];
    ASM_ARITH_TAC]);;

(* One de Bruijn row interned: found, or appended (then decoding and new). *)
let PL_DB_STEP = prove
 (`!ctx nms tys dbs key pay md.
     pl_tabs_ok ctx nms tys dbs /\ pl_interned dbs key pay md /\ db_key_ok (LENGTH dbs) key /\
     ((?t. fddb nms tys (APPEND dbs [key]) (LENGTH dbs) t) \/
      (?l. fddbs nms tys (APPEND dbs [key]) (LENGTH dbs) l))
     ==> pl_tabs_ok ctx nms tys (APPEND dbs md) /\
         pay < LENGTH (APPEND dbs md) /\ EL pay (APPEND dbs md) = key /\
         (!i t. fddb nms tys dbs i t ==> fddb nms tys (APPEND dbs md) i t) /\
         (!i l. fddbs nms tys dbs i l ==> fddbs nms tys (APPEND dbs md) i l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_interned] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (DISJ_CASES_THEN STRIP_ASSUME_TAC)
               (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  PL_SUBST_TABLE_TAC THEN
  ASM_REWRITE_TAC[APPEND_NIL; PL_FDDB_APPEND] THEN
  PL_EXPAND_ASM "pl_tabs_ok" [pl_tabs_ok] THEN
  ASM_SIMP_TAC[LENGTH_APPEND; LENGTH; EL_APPEND; LT_REFL; SUB_REFL; EL; HD;
               ARITH_RULE `l < l + SUC 0`] THEN
  REWRITE_TAC[pl_tabs_ok; LENGTH_APPEND; LENGTH] THEN
  SUBGOAL_THEN `nat_keys tys (APPEND dbs [key]) /\ keys_distinct (APPEND (dbs:(num#num#num)list) [key])`
    STRIP_ASSUME_TAC THENL [MATCH_MP_TAC PL_DB_SNOC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i < LENGTH (dbs:(num#num#num)list)` THENL
     [ASM_MESON_TAC[PL_FDDB_APPEND];
      SUBGOAL_THEN `i = LENGTH (dbs:(num#num#num)list)` SUBST1_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ASM_ARITH_TAC]);;

(* The context's signature is the standard one: fun, bool, =. *)
let PL_STD_SIG = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) ==> his_std_sig (hsigof ctx)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[nat_rows_ok; fibre_inv] o CONJUNCT1 o CONJUNCT2 o MATCH_MP PL_INV_NAT) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `htheory_ok (hthyof ctx)` MP_TAC THENL
   [ASM_MESON_TAC[HEXTENDS_THEORY_OK; HINIT_THEORY_OK]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HTHEORY_OK_STD_SIG) THEN REWRITE_TAC[hthyof; FST]);;

(* The bootstrap lists the plans name: 0 is [], 3 is [bool]. *)
let PL_BOOT_LISTS = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
     ==> fdtys nms tys 0 [] /\ fdtys nms tys 3 [HBool]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_BOOL) THEN
  PL_INV_FACTS_TAC THEN
  SUBGOAL_THEN `fdtys nms tys 0 []` ASSUME_TAC THENL
   [MATCH_MP_TAC(el 2 (CONJUNCTS(SPEC_ALL fdty_RULES))) THEN
    MAP_EVERY EXISTS_TAC [`0`; `0`] THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(el 3 (CONJUNCTS(SPEC_ALL fdty_RULES))) THEN
  MAP_EVERY EXISTS_TAC [`1`; `0`] THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let ALL2_MAP_SELF = prove
 (`!(R:A->B->bool) f l. ALL (\x. R x (f x)) l ==> ALL2 R l (MAP f l)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_SIMP_TAC[ALL; ALL2; MAP]);;

let PL_SORTED_EQ = prove
 (`!xs ys:num list. PAIRWISE (<) xs /\ PAIRWISE (<) ys /\ (!x. MEM x xs <=> MEM x ys) ==> xs = ys`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; NOT_CONS_NIL; PAIRWISE; CONS_11] THENL
   [MESON_TAC[]; MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `h:num = h'` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[LT_ANTISYM]; ALL_TAC] THEN
  REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[LT_REFL]);;

let PL_IDS_UNIQUE = prove
 (`!ids D l l'. keys_distinct D /\ pl_ids D l ids /\ pl_ids D l' ids ==> l = l'`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[pl_ids] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[keys_distinct];
    SUBGOAL_THEN `b:num = b'` SUBST_ALL_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[keys_distinct]]);;

(* Two sorted list rows with the same elements are one row. *)
let PL_FINDL_UNIQUE = prove
 (`!D L ids L' ids'. keys_distinct D /\ pl_ids D L ids /\ PAIRWISE (<) ids /\
                     pl_ids D L' ids' /\ PAIRWISE (<) ids' /\ (!x. MEM x ids <=> MEM x ids')
                     ==> L = L'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ids:num list = ids'` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC PL_SORTED_EQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[PL_IDS_UNIQUE]);;

(* A decoded term row: its image decodes to the term's image, its type row  *)
(* to its type.                                                              *)
let PL_TM_DEC = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk t p.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ fdtm nms tys ntms t p
     ==> fddb nms tys dbs (ntm_db (EL t ntms)) (hdb p) /\ fdty nms tys (ntm_ty (EL t ntms)) (htypeof p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `t < LENGTH (ntms:(num#num#num#num#num)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FDTM_BOUND]; ALL_TAC] THEN
  MP_TAC(SPEC_ALL PL_TM_ROW) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:holterm` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `q:holterm = p` (fun th -> ASM_MESON_TAC[th]) THEN
  ASM_MESON_TAC[FDTM_FUNCTIONAL]);;

(* The control words a plan writes are temporaries: pl_inv does not see them. *)
let PL_INV_CW = prove
 (`!cw cw' ns stk. pl_inv (cw,ns,stk) /\ (!n. n <= 6 ==> cw' n = cw n) ==> pl_inv (cw',ns,stk)`,
  REWRITE_TAC[FORALL_PAIR_THM; pl_inv] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* ASSUME.                                                                   *)
(* ------------------------------------------------------------------------- *)

let NAT_STEP_ASSUME = el 12 (CONJUNCTS nat_step_RULES);;

let PL_ASSUME_GUARDS = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk t.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
     ==> ((nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RAssume t) /\
           ?p. fdtm nms tys ntms t p /\ htypeof p = HBool) <=>
          holr_live 2 t (LENGTH ntms) drops /\ ntm_ty (EL t ntms) = 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nat_ops_live; holr_operands; ALL; FST; SND] THEN
  ASM_CASES_TAC `holr_live 2 t (LENGTH (ntms:(num#num#num#num#num)list)) drops` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `t < LENGTH (ntms:(num#num#num#num#num)list)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[holr_live] o check (fun th -> is_const_app "holr_live" (concl th))) THEN
    SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC_ALL PL_TM_ROW) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`;
                `ntm_ty (EL t (ntms:(num#num#num#num#num)list))`; `htypeof p`] PL_TYPE_BOOL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `q:holterm` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `q:holterm = p` (fun th -> ASM_REWRITE_TAC[SYM th]) THEN
    MP_TAC(SPECL [`t:num`; `q:holterm`] (SPECL [`nms:string list`; `tys:(num#num#num)list`;
                                              `ntms:(num#num#num#num#num)list`] FDTM_FUNCTIONAL)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `p:holterm`) THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN EXISTS_TAC `p:holterm` THEN ASM_REWRITE_TAC[]]);;

let PL_STEP_ASSUME_SPEC md hk =
  SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
         `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
         `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `t:num`;
         `p:holterm`; `[]:(num#num#num)list`; md; hk; `d:num`; `[hdb p]`] NAT_STEP_ASSUME;;
let PL_INV_STEP_SPEC r md hk =
  SPECL [`cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
         `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
         `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`;
         `cw':num->num`; r; `[]:(num#num#num)list`; md; hk; `d:num`] PL_INV_THM_STEP;;

let pl_assume_fired_goal = `!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk t md hk cw'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     holr_live 2 t (LENGTH ntms) drops /\ ntm_ty (EL t ntms) = 1 /\
     pl_interned dbs (6,ntm_db (EL t ntms),0) hk md /\
     LENGTH ths + 1 < 2 EXP 60 /\ (!n. n <= 6 ==> cw' n = cw n)
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RAssume t)
                  (ctx,nms,tys,ntms,APPEND dbs md,APPEND ths [(hk,ntm_db (EL t ntms))],nmap,ymap,drops,pol) /\
         pl_inv (cw',(ctx,nms,tys,ntms,APPEND dbs md,APPEND ths [(hk,ntm_db (EL t ntms))],
                      nmap,ymap,drops,pol),stk)`;;

let PL_ASSUME_SETUP_TAC =
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_interned] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `md:(num#num#num)list`)) THEN
  (SUBGOAL_THEN `t < LENGTH (ntms:(num#num#num#num#num)list)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[holr_live] o check (fun th -> is_const_app "holr_live" (concl th))) THEN
    SIMP_TAC[]; ALL_TAC]) THEN
  MP_TAC(SPEC_ALL PL_TM_ROW) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:holterm` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`;
                `ntm_ty (EL t (ntms:(num#num#num#num#num)list))`; `htypeof p`] PL_TYPE_BOOL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_BOOL) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_NAMES_INJ) THEN
  (SUBGOAL_THEN `ntm_db (EL t (ntms:(num#num#num#num#num)list)) < LENGTH (dbs:(num#num#num)list)` ASSUME_TAC THENL
   [MP_TAC(CONJUNCT1(SPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`] FDDB_BOUND)) THEN
    ASM_MESON_TAC[]; ALL_TAC]) THEN
  ABBREV_TAC `d = ntm_db (EL t (ntms:(num#num#num#num#num)list))` THEN
  PL_STRIP_INV_TAC THEN
  REWRITE_TAC[APPEND_NIL] THEN RULE_ASSUM_TAC(REWRITE_RULE[APPEND_NIL]);;

let PL_ASSUME_FOUND_TAC =
  SUBGOAL_THEN `nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RAssume t)
                          (ctx,nms,tys,ntms,dbs,APPEND ths [hk,d:num],nmap,ymap,drops,pol)` ASSUME_TAC THENL
   [MP_TAC(PL_STEP_ASSUME_SPEC `[]:(num#num#num)list` `hk:num`) THEN REWRITE_TAC[APPEND_NIL] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[NAT_TYS_OK_NIL; NAT_NEW_ROWS_NIL; MEM; nat_ops_live; holr_operands; ALL; FST; SND] THEN
    MATCH_MP_TAC FDDBS_CONS THEN MAP_EVERY EXISTS_TAC [`d:num`; `0`] THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN
    MP_TAC(PL_INV_STEP_SPEC `RAssume t` `[]:(num#num#num)list` `hk:num`) THEN
    REWRITE_TAC[APPEND_NIL; LENGTH; ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `[d:num]` THEN REWRITE_TAC[pl_ids; PAIRWISE; ALL] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `0` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];;

let PL_ASSUME_APPENDED_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `hk:num`)) THEN
  SUBGOAL_THEN `nat_keys tys (APPEND dbs [6,d:num,0]) /\ keys_distinct (APPEND (dbs:(num#num#num)list) [6,d,0])`
    STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC PL_DB_SNOC THEN ASM_REWRITE_TAC[db_key_ok] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `EL (LENGTH (dbs:(num#num#num)list)) (APPEND dbs [6,d:num,0]) = (6,d,0)` ASSUME_TAC THENL
   [REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD]; ALL_TAC] THEN
  SUBGOAL_THEN `fddb nms tys (APPEND dbs [6,d:num,0]) d (hdb p) /\ fddbs nms tys (APPEND dbs [6,d:num,0]) 0 []`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[PL_FDDB_APPEND]; ALL_TAC] THEN
  SUBGOAL_THEN `fddbs nms tys (APPEND dbs [6,d:num,0]) (LENGTH (dbs:(num#num#num)list)) [hdb p]` ASSUME_TAC THENL
   [MATCH_MP_TAC FDDBS_CONS THEN MAP_EVERY EXISTS_TAC [`d:num`; `0`] THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RAssume t)
     (ctx,nms,tys,ntms,APPEND dbs [6,d:num,0],APPEND ths [LENGTH (dbs:(num#num#num)list),d],nmap,ymap,drops,pol)`
    ASSUME_TAC THENL
   [MP_TAC(PL_STEP_ASSUME_SPEC `[6,d:num,0]` `LENGTH (dbs:(num#num#num)list)`) THEN REWRITE_TAC[APPEND_NIL] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[NAT_TYS_OK_NIL; MEM; nat_ops_live; holr_operands; ALL; FST; SND] THEN
    MATCH_MP_TAC NAT_KEYS_NEW_ROWS THEN ASM_REWRITE_TAC[APPEND_NIL; LENGTH; ADD_CLAUSES] THEN
    X_GEN_TAC `k:num` THEN DISCH_THEN(SUBST1_TAC o MATCH_MP (ARITH_RULE `k < SUC n /\ n <= k ==> k = n`)) THEN
    DISJ2_TAC THEN EXISTS_TAC `[hdb p]` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(PL_INV_STEP_SPEC `RAssume t` `[6,d:num,0]` `LENGTH (dbs:(num#num#num)list)`) THEN
  REWRITE_TAC[APPEND_NIL; LENGTH; ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(ASM_ARITH_TAC THEN NO_TAC) THEN
  EXISTS_TAC `[d:num]` THEN REWRITE_TAC[pl_ids; PAIRWISE; ALL] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `0` THEN
  ASM_SIMP_TAC[EL_APPEND; LENGTH_APPEND; LENGTH; ARITH_RULE `1 <= l ==> 0 < l /\ 0 < l + SUC 0`];;

let PL_ASSUME_FIRED = prove(pl_assume_fired_goal,
  PL_ASSUME_SETUP_TAC THENL [PL_ASSUME_FOUND_TAC; PL_ASSUME_APPENDED_TAC]);;

let pl_assume_goal =
 `!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk t k i cw' ns' stk'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ cw 8 = t /\
     pl_run pl_plan_assume 0 (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) (k,i,(cw',ns',stk'))
     ==> (k = 1 ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RAssume t) ns' /\
                    pl_inv (cw',ns',stk')) /\
         (k = 0 <=> ~(nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RAssume t) /\
                      ?p. fdtm nms tys ntms t p /\ htypeof p = HBool))`;;

(* PL_ASSUME: the plan's FIRED run is ASSUME's nat_step and keeps pl_inv;  *)
(* it is REFUSED exactly when t is not live or not of type bool.           *)
let PL_ASSUME = prove(pl_assume_goal,
  PL_START_TAC pl_plan_assume THEN
  PL_INV_ASM(fun th -> REWRITE_TAC[MATCH_MP PL_ASSUME_GUARDS th]) THEN REWRITE_TAC[ARITH_EQ] THEN
  ASM_REWRITE_TAC[] THEN TRY(ASM_ARITH_TAC THEN NO_TAC) THEN PL_FIRED_TAC PL_ASSUME_FIRED);;

(* ------------------------------------------------------------------------- *)
(* EQ_MP.                                                                    *)
(* ------------------------------------------------------------------------- *)

let PL_EQMP_GUARDS = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h1 h2.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
     ==> ((nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (REqMp h1 h2) /\
           ?ty p q. fddb nms tys dbs (SND(EL h1 ths)) (hdbComb (hdbComb (hdbConst "=" ty) p) q) /\
                    fddb nms tys dbs (SND(EL h2 ths)) p) <=>
          holr_live 3 h1 (LENGTH ths) drops /\ holr_live 3 h2 (LENGTH ths) drops /\
          pl_eq_ok dbs (SND(EL h1 ths)) /\ pl_eq_lhs dbs (SND(EL h1 ths)) = SND(EL h2 ths))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nat_ops_live; holr_operands; ALL; FST; SND] THEN
  ASM_CASES_TAC `holr_live 3 h1 (LENGTH (ths:(num#num)list)) drops` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `holr_live 3 h2 (LENGTH (ths:(num#num)list)) drops` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `h1 < LENGTH (ths:(num#num)list) /\ h2 < LENGTH ths` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[holr_live]; ALL_TAC] THEN
  MP_TAC(PL_SPEC [`h1:num`] PL_THM_DEC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `C1:hdbterm`) (K ALL_TAC)) THEN
  MP_TAC(PL_SPEC [`SND(EL h1 (ths:(num#num)list))`; `C1:hdbterm`] PL_EQ_DEC) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_CANON) THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `ty:holtype` (X_CHOOSE_THEN `p:hdbterm` (X_CHOOSE_THEN `q:hdbterm` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `C1 = hdbComb (hdbComb (hdbConst "=" ty) p) q` ASSUME_TAC THENL
     [ASM_MESON_TAC[FDDB_FUN]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    STRIP_TAC THEN
    SUBGOAL_THEN `?ty l r. C1 = hdbComb (hdbComb (hdbConst "=" ty) l) r` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ty:holtype` (X_CHOOSE_THEN `l:hdbterm` (X_CHOOSE_THEN `r:hdbterm` ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`ty:holtype`; `l:hdbterm`; `r:hdbterm`] THEN
    ASM_MESON_TAC[]]);;

let pl_eqmp_fired_goal =
 `!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h1 h2 md hk cw'.
   pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
   holr_live 3 h1 (LENGTH ths) drops /\ holr_live 3 h2 (LENGTH ths) drops /\
   pl_eq_ok dbs (SND(EL h1 ths)) /\ pl_eq_lhs dbs (SND(EL h1 ths)) = SND(EL h2 ths) /\
   (keys_distinct dbs ==> keys_distinct (APPEND dbs md)) /\ LENGTH (APPEND dbs md) < 2 EXP 60 /\
   (!I1 I2. pl_ids dbs (FST(EL h1 ths)) I1 /\ pl_ids dbs (FST(EL h2 ths)) I2 /\
            PAIRWISE (<) I1 /\ PAIRWISE (<) I2
            ==> (?ids. pl_ids (APPEND dbs md) hk ids /\ PAIRWISE (<) ids /\
                       (!x. MEM x ids <=> MEM x I1 \/ MEM x I2)) /\
                pl_cells_new 6 (LENGTH dbs) (APPEND dbs md) (\a. MEM a I1 \/ MEM a I2)) /\
   LENGTH ths + 1 < 2 EXP 60 /\ (!n. n <= 6 ==> cw' n = cw n)
   ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (REqMp h1 h2)
         (ctx,nms,tys,ntms,APPEND dbs md,APPEND ths [(hk,pl_eq_rhs dbs (SND(EL h1 ths)))],nmap,ymap,drops,pol) /\
       pl_inv (cw',(ctx,nms,tys,ntms,APPEND dbs md,APPEND ths [(hk,pl_eq_rhs dbs (SND(EL h1 ths)))],
                    nmap,ymap,drops,pol),stk)`;;
let PL_EQMP_FIRED = prove(pl_eqmp_fired_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `h1 < LENGTH (ths:(num#num)list) /\ h2 < LENGTH ths` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[holr_live]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_NAMES_INJ) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_CANON) THEN
  MP_TAC(PL_SPEC [`h1:num`] PL_THM_DEC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `C1:hdbterm`) (X_CHOOSE_TAC `hs1:hdbterm list`)) THEN
  MP_TAC(PL_SPEC [`h2:num`] PL_THM_DEC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `C2:hdbterm`) (X_CHOOSE_TAC `hs2:hdbterm list`)) THEN
  MP_TAC(PL_SPEC [`SND(EL h1 (ths:(num#num)list))`; `C1:hdbterm`] PL_EQ_DEC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `ty:holtype` (X_CHOOSE_THEN `p:hdbterm` (X_CHOOSE_THEN `q:hdbterm` ASSUME_TAC))) ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ty:holtype`; `p:hdbterm`; `q:hdbterm`] o
                check (fun th -> is_forall(concl th) && can (find_term ((=) `pl_eq_rhs`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN PL_INV_FACTS_TAC THEN
  SUBGOAL_THEN `?I1. pl_ids dbs (FST(EL h1 (ths:(num#num)list))) I1 /\ PAIRWISE (<) I1`
    (X_CHOOSE_THEN `I1:num list` STRIP_ASSUME_TAC) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?I2. pl_ids dbs (FST(EL h2 (ths:(num#num)list))) I2 /\ PAIRWISE (<) I2`
    (X_CHOOSE_THEN `I2:num list` STRIP_ASSUME_TAC) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`I1:num list`; `I2:num list`] o
                check (fun th -> is_forall(concl th) && can (find_term ((=) `pl_cells_new`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `ids:num list` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`; `md:(num#num#num)list`;
                `FST(EL h1 (ths:(num#num)list))`; `FST(EL h2 (ths:(num#num)list))`; `hk:num`;
                `I1:num list`; `I2:num list`; `hs1:hdbterm list`; `hs2:hdbterm list`] PL_UNION_STEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXISTS_TAC `ids:num list` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `hs:hdbterm list` STRIP_ASSUME_TAC))) THEN
FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `C1:hdbterm` then SUBST_ALL_TAC th else failwith "") THEN
  SUBGOAL_THEN `keys_distinct (APPEND (dbs:(num#num#num)list) md)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_eq_rhs dbs (SND(EL h1 (ths:(num#num)list))) < LENGTH dbs` ASSUME_TAC THENL
   [ASM_MESON_TAC[FDDB_BOUND]; ALL_TAC] THEN
  SUBGOAL_THEN `nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (REqMp h1 h2)
     (ctx,nms,tys,ntms,APPEND dbs md,APPEND ths [(hk,pl_eq_rhs dbs (SND(EL h1 (ths:(num#num)list))))],
      nmap,ymap,drops,pol)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                  `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                  `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `h1:num`; `h2:num`;
                  `hs1:hdbterm list`; `hs2:hdbterm list`; `ty:holtype`; `p:hdbterm`; `q:hdbterm`;
                  `[]:(num#num#num)list`; `md:(num#num#num)list`; `hk:num`;
                  `pl_eq_rhs dbs (SND(EL h1 (ths:(num#num)list)))`; `hs:hdbterm list`] NAT_STEP_EQMP) THEN
    REWRITE_TAC[APPEND_NIL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[NAT_TYS_OK_NIL; nat_ops_live; holr_operands; ALL; FST; SND] THEN
    CONJ_TAC THENL
     [MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
                    `[]:(num#num#num)list`; `md:(num#num#num)list`] NAT_KEYS_NEW_ROWS) THEN
      REWRITE_TAC[APPEND_NIL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      ASM_MESON_TAC[PL_FDDB_APPEND]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`;
                `cw':num->num`; `REqMp h1 h2`; `[]:(num#num#num)list`; `md:(num#num#num)list`; `hk:num`;
                `pl_eq_rhs dbs (SND(EL h1 (ths:(num#num)list)))`] PL_INV_THM_STEP) THEN
  REWRITE_TAC[APPEND_NIL; LENGTH; ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN
  REPEAT CONJ_TAC THEN TRY(ASM_ARITH_TAC THEN NO_TAC) THEN ASM_MESON_TAC[]);;

let pl_eqmp_goal =
 `!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h1 h2 k i cw' ns' stk'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ cw 8 = h1 /\ cw 9 = h2 /\
     pl_run pl_plan_eqmp 0 (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) (k,i,(cw',ns',stk'))
     ==> (k = 1 ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (REqMp h1 h2) ns' /\
                    pl_inv (cw',ns',stk')) /\
         (k = 0 <=> ~(nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (REqMp h1 h2) /\
                      ?ty p q. fddb nms tys dbs (SND(EL h1 ths)) (hdbComb (hdbComb (hdbConst "=" ty) p) q) /\
                               fddb nms tys dbs (SND(EL h2 ths)) p))`;;

(* PL_EQMP: the plan's FIRED run is EQ_MP's nat_step and keeps pl_inv; it *)
(* is REFUSED exactly when an operand is not live, h1's conclusion is not   *)
(* an equation, or its left side is not h2's conclusion.                    *)
let PL_EQMP = prove(pl_eqmp_goal,
  PL_START_TAC pl_plan_eqmp THEN
  PL_INV_ASM(fun th -> REWRITE_TAC[MATCH_MP PL_EQMP_GUARDS th]) THEN
  REWRITE_TAC[ARITH_EQ; pl_eq_ok; pl_eq_lhs] THEN
  ASM_REWRITE_TAC[] THEN TRY(ASM_ARITH_TAC THEN NO_TAC) THEN PL_FIRED_TAC PL_EQMP_FIRED);;

(* ------------------------------------------------------------------------- *)
(* TRANS.                                                                    *)
(* ------------------------------------------------------------------------- *)

let PL_TRANS_GUARDS = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h1 h2.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
     ==> ((nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RTrans h1 h2) /\
           ?ty1 ty2 l mid r. fddb nms tys dbs (SND(EL h1 ths)) (hdbComb (hdbComb (hdbConst "=" ty1) l) mid) /\
                             fddb nms tys dbs (SND(EL h2 ths)) (hdbComb (hdbComb (hdbConst "=" ty2) mid) r)) <=>
          holr_live 3 h1 (LENGTH ths) drops /\ holr_live 3 h2 (LENGTH ths) drops /\
          pl_eq_ok dbs (SND(EL h1 ths)) /\ pl_eq_ok dbs (SND(EL h2 ths)) /\
          pl_eq_rhs dbs (SND(EL h1 ths)) = pl_eq_lhs dbs (SND(EL h2 ths)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nat_ops_live; holr_operands; ALL; FST; SND] THEN
  ASM_CASES_TAC `holr_live 3 h1 (LENGTH (ths:(num#num)list)) drops` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `holr_live 3 h2 (LENGTH (ths:(num#num)list)) drops` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `h1 < LENGTH (ths:(num#num)list) /\ h2 < LENGTH ths` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[holr_live]; ALL_TAC] THEN
  MP_TAC(PL_SPEC [`h1:num`] PL_THM_DEC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `C1:hdbterm`) (K ALL_TAC)) THEN
  MP_TAC(PL_SPEC [`h2:num`] PL_THM_DEC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `C2:hdbterm`) (K ALL_TAC)) THEN
  MP_TAC(PL_SPEC [`SND(EL h1 (ths:(num#num)list))`; `C1:hdbterm`] PL_EQ_DEC) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(PL_SPEC [`SND(EL h2 (ths:(num#num)list))`; `C2:hdbterm`] PL_EQ_DEC) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_CANON) THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `ty1:holtype` (X_CHOOSE_THEN `ty2:holtype` (X_CHOOSE_THEN `l:hdbterm`
      (X_CHOOSE_THEN `mid:hdbterm` (X_CHOOSE_THEN `r:hdbterm` STRIP_ASSUME_TAC))))) THEN
    SUBGOAL_THEN `C1 = hdbComb (hdbComb (hdbConst "=" ty1) l) mid /\
                  C2 = hdbComb (hdbComb (hdbConst "=" ty2) mid) r` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[FDDB_FUN]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    STRIP_TAC THEN
    SUBGOAL_THEN `?ty1 l m. C1 = hdbComb (hdbComb (hdbConst "=" ty1) l) m` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ty1:holtype` (X_CHOOSE_THEN `l:hdbterm` (X_CHOOSE_THEN `m:hdbterm` ASSUME_TAC))) THEN
    SUBGOAL_THEN `?ty2 l2 r. C2 = hdbComb (hdbComb (hdbConst "=" ty2) l2) r` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ty2:holtype` (X_CHOOSE_THEN `l2:hdbterm` (X_CHOOSE_THEN `r:hdbterm` ASSUME_TAC))) THEN
    SUBGOAL_THEN `m:hdbterm = l2` SUBST_ALL_TAC THENL [ASM_MESON_TAC[FDDB_FUN]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`ty1:holtype`; `ty2:holtype`; `l:hdbterm`; `l2:hdbterm`; `r:hdbterm`] THEN
    ASM_MESON_TAC[]]);;

let pl_trans_fired_goal =
 `!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h1 h2 md kk md2 hk cw'.
   pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
   holr_live 3 h1 (LENGTH ths) drops /\ holr_live 3 h2 (LENGTH ths) drops /\
   pl_eq_ok dbs (SND(EL h1 ths)) /\ pl_eq_ok dbs (SND(EL h2 ths)) /\
   pl_eq_rhs dbs (SND(EL h1 ths)) = pl_eq_lhs dbs (SND(EL h2 ths)) /\
   pl_interned dbs (3,FST(SND(EL (SND(EL h1 ths)) dbs)),pl_eq_rhs dbs (SND(EL h2 ths))) kk md /\
   (keys_distinct (APPEND dbs md) ==> keys_distinct (APPEND (APPEND dbs md) md2)) /\
   LENGTH (APPEND (APPEND dbs md) md2) < 2 EXP 60 /\
   (!I1 I2. pl_ids (APPEND dbs md) (FST(EL h1 ths)) I1 /\ pl_ids (APPEND dbs md) (FST(EL h2 ths)) I2 /\
            PAIRWISE (<) I1 /\ PAIRWISE (<) I2
            ==> (?ids. pl_ids (APPEND (APPEND dbs md) md2) hk ids /\ PAIRWISE (<) ids /\
                       (!x. MEM x ids <=> MEM x I1 \/ MEM x I2)) /\
                pl_cells_new 6 (LENGTH (APPEND dbs md)) (APPEND (APPEND dbs md) md2)
                             (\a. MEM a I1 \/ MEM a I2)) /\
   LENGTH ths + 1 < 2 EXP 60 /\ (!n. n <= 6 ==> cw' n = cw n)
   ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RTrans h1 h2)
         (ctx,nms,tys,ntms,APPEND (APPEND dbs md) md2,APPEND ths [(hk,kk)],nmap,ymap,drops,pol) /\
       pl_inv (cw',(ctx,nms,tys,ntms,APPEND (APPEND dbs md) md2,APPEND ths [(hk,kk)],
                    nmap,ymap,drops,pol),stk)`;;
let PL_TRANS_APPENDED_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `kk:num`)) THEN
  SUBGOAL_THEN `nat_keys tys (APPEND dbs [3,FST(SND(EL (SND(EL h1 (ths:(num#num)list))) dbs)),pl_eq_rhs dbs (SND(EL h2 ths))]) /\
                keys_distinct (APPEND dbs [3,FST(SND(EL (SND(EL h1 (ths:(num#num)list))) dbs)),pl_eq_rhs dbs (SND(EL h2 ths))])`
    STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC PL_DB_SNOC THEN ASM_REWRITE_TAC[db_key_ok] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `EL (LENGTH (dbs:(num#num#num)list))
                   (APPEND dbs [3,FST(SND(EL (SND(EL h1 (ths:(num#num)list))) dbs)),pl_eq_rhs dbs (SND(EL h2 ths))]) =
                (3,FST(SND(EL (SND(EL h1 ths)) dbs)),pl_eq_rhs dbs (SND(EL h2 ths)))` ASSUME_TAC THENL
   [REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD]; ALL_TAC] THEN
  SUBGOAL_THEN `fddb nms tys (APPEND dbs [3,FST(SND(EL (SND(EL h1 (ths:(num#num)list))) dbs)),pl_eq_rhs dbs (SND(EL h2 ths))])
                     (LENGTH (dbs:(num#num#num)list)) (hdbComb (hdbComb (hdbConst "=" ty1) l) r)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[FDDB_COMB_INV] THEN REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN ASM_MESON_TAC[PL_FDDB_APPEND];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND; LENGTH]) THEN
  REPEAT CONJ_TAC THEN TRY(ASM_ARITH_TAC THEN NO_TAC) THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `k = LENGTH (dbs:(num#num#num)list)` SUBST1_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]];;
let PL_TRANS_UNION_TAC =
  SUBGOAL_THEN `?I1. pl_ids dbs (FST(EL h1 (ths:(num#num)list))) I1 /\ PAIRWISE (<) I1`
    (X_CHOOSE_THEN `I1:num list` STRIP_ASSUME_TAC) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?I2. pl_ids dbs (FST(EL h2 (ths:(num#num)list))) I2 /\ PAIRWISE (<) I2`
    (X_CHOOSE_THEN `I2:num list` STRIP_ASSUME_TAC) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`I1:num list`; `I2:num list`] o
                check (fun th -> is_forall(concl th) && can (find_term ((=) `pl_cells_new`)) (concl th))) THEN
  ASM_SIMP_TAC[PL_IDS_APPEND] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `ids:num list` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `APPEND (dbs:(num#num#num)list) md`;
                `md2:(num#num#num)list`;
                `FST(EL h1 (ths:(num#num)list))`; `FST(EL h2 (ths:(num#num)list))`; `hk:num`;
                `I1:num list`; `I2:num list`; `hs1:hdbterm list`; `hs2:hdbterm list`] PL_UNION_STEP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[PL_IDS_APPEND] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[PL_FDDB_APPEND]; ASM_MESON_TAC[PL_FDDB_APPEND];
      EXISTS_TAC `ids:num list` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `hs:hdbterm list` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `keys_distinct (APPEND (APPEND (dbs:(num#num#num)list) md) md2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC];;
let PL_TRANS_STEP_TAC =
  SUBGOAL_THEN `fddb nms tys (APPEND (APPEND dbs md) md2) kk (hdbComb (hdbComb (hdbConst "=" ty1) l) r)`
    ASSUME_TAC THENL [ASM_MESON_TAC[PL_FDDB_APPEND]; ALL_TAC] THEN
  SUBGOAL_THEN `nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RTrans h1 h2)
     (ctx,nms,tys,ntms,APPEND (APPEND dbs md) md2,APPEND ths [(hk,kk)],nmap,ymap,drops,pol)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                  `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                  `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `h1:num`; `h2:num`;
                  `hs1:hdbterm list`; `hs2:hdbterm list`; `ty1:holtype`; `ty2:holtype`; `l:hdbterm`;
                  `mid:hdbterm`; `r:hdbterm`; `[]:(num#num#num)list`; `APPEND md md2:(num#num#num)list`;
                  `hk:num`; `kk:num`; `hs:hdbterm list`] NAT_STEP_TRANS) THEN
    REWRITE_TAC[APPEND_NIL; APPEND_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[NAT_TYS_OK_NIL; nat_ops_live; holr_operands; ALL; FST; SND] THEN
    MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
                  `[]:(num#num#num)list`; `APPEND md md2:(num#num#num)list`] NAT_KEYS_NEW_ROWS) THEN
    REWRITE_TAC[APPEND_NIL; APPEND_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:num` THEN REWRITE_TAC[LENGTH_APPEND] THEN STRIP_TAC THEN
    ASM_CASES_TAC `k < LENGTH (APPEND (dbs:(num#num#num)list) md)` THENL
     [DISJ1_TAC THEN ASM_MESON_TAC[PL_FDDB_APPEND];
      DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN
      REWRITE_TAC[LENGTH_APPEND] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`;
                `cw':num->num`; `RTrans h1 h2`; `[]:(num#num#num)list`; `APPEND md md2:(num#num#num)list`;
                `hk:num`; `kk:num`] PL_INV_THM_STEP) THEN
  REWRITE_TAC[APPEND_NIL; APPEND_ASSOC; LENGTH; ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN REWRITE_TAC[LENGTH_APPEND] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_ARITH_TAC THEN NO_TAC) THEN ASM_MESON_TAC[];;
let PL_TRANS_FIRED = prove(pl_trans_fired_goal,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_interned] THEN DISCH_THEN(fun th ->
    let cs = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC (filter (fun c -> not(is_disj(concl c))) cs) THEN
    ASSUME_TAC(find (fun c -> is_disj(concl c)) cs)) THEN
  SUBGOAL_THEN `h1 < LENGTH (ths:(num#num)list) /\ h2 < LENGTH ths` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[holr_live]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_NAMES_INJ) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_CANON) THEN
  MP_TAC(PL_SPEC [`h1:num`] PL_THM_DEC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `C1:hdbterm`) (X_CHOOSE_TAC `hs1:hdbterm list`)) THEN
  MP_TAC(PL_SPEC [`h2:num`] PL_THM_DEC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `C2:hdbterm`) (X_CHOOSE_TAC `hs2:hdbterm list`)) THEN
  MP_TAC(PL_SPEC [`SND(EL h1 (ths:(num#num)list))`; `C1:hdbterm`] PL_EQ_DEC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `ty1:holtype` (X_CHOOSE_THEN `l:hdbterm` (X_CHOOSE_THEN `mid:hdbterm` ASSUME_TAC))) ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ty1:holtype`; `l:hdbterm`; `mid:hdbterm`] o
                check (fun th -> is_forall(concl th) && can (find_term ((=) `pl_eq_ty`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(PL_SPEC [`SND(EL h2 (ths:(num#num)list))`; `C2:hdbterm`] PL_EQ_DEC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `ty2:holtype` (X_CHOOSE_THEN `l2:hdbterm` (X_CHOOSE_THEN `r:hdbterm` ASSUME_TAC))) ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ty2:holtype`; `l2:hdbterm`; `r:hdbterm`] o
                check (fun th -> is_forall(concl th) && can (find_term ((=) `pl_eq_ty`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `l2:hdbterm = mid` SUBST_ALL_TAC THENL [ASM_MESON_TAC[FDDB_FUN]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_eq(concl th) && (lhs(concl th) = `C1:hdbterm` || lhs(concl th) = `C2:hdbterm`)
                                 then SUBST_ALL_TAC th else failwith "")) THEN
  SUBGOAL_THEN `fddb nms tys dbs (FST(SND(EL (SND(EL h1 (ths:(num#num)list))) dbs))) (hdbComb (hdbConst "=" ty1) l)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `fddb nms tys dbs (SND(EL h1 (ths:(num#num)list))) (hdbComb (hdbComb (hdbConst "=" ty1) l) mid)` THEN
    DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[FDDB_COMB_INV]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  PL_INV_FACTS_TAC THEN
  SUBGOAL_THEN
   `nat_keys tys (APPEND dbs md) /\ keys_distinct (APPEND (dbs:(num#num#num)list) md) /\
    LENGTH (APPEND dbs md) < 2 EXP 60 /\ kk < LENGTH (APPEND dbs md) /\
    fddb nms tys (APPEND dbs md) kk (hdbComb (hdbComb (hdbConst "=" ty1) l) r) /\
    (!k. k < LENGTH (APPEND dbs md) /\ LENGTH dbs <= k ==> ?t. fddb nms tys (APPEND dbs md) k t)`
   STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `FST(SND(EL (SND(EL h1 (ths:(num#num)list))) dbs)) < LENGTH (dbs:(num#num#num)list) /\
                  pl_eq_rhs dbs (SND(EL h2 (ths:(num#num)list))) < LENGTH dbs` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[FDDB_BOUND]; ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `md:(num#num#num)list`)) THENL
     [REWRITE_TAC[APPEND_NIL] THEN ONCE_REWRITE_TAC[FDDB_COMB_INV] THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC;
      PL_TRANS_APPENDED_TAC];
    ALL_TAC] THEN
  PL_TRANS_UNION_TAC THEN PL_TRANS_STEP_TAC);;

let pl_trans_goal =
 `!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h1 h2 k i cw' ns' stk'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ cw 8 = h1 /\ cw 9 = h2 /\
     pl_run pl_plan_trans 0 (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) (k,i,(cw',ns',stk'))
     ==> (k = 1 ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RTrans h1 h2) ns' /\
                    pl_inv (cw',ns',stk')) /\
         (k = 0 <=> ~(nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RTrans h1 h2) /\
                      ?ty1 ty2 l mid r.
                        fddb nms tys dbs (SND(EL h1 ths)) (hdbComb (hdbComb (hdbConst "=" ty1) l) mid) /\
                        fddb nms tys dbs (SND(EL h2 ths)) (hdbComb (hdbComb (hdbConst "=" ty2) mid) r)))`;;

(* PL_TRANS: the plan's FIRED run is TRANS's nat_step and keeps pl_inv; it *)
(* is REFUSED exactly when an operand is not live, a conclusion is not an  *)
(* equation, or the middle terms differ.                                     *)
let PL_TRANS = prove(pl_trans_goal,
  PL_START_TAC pl_plan_trans THEN
  PL_INV_ASM(fun th -> REWRITE_TAC[MATCH_MP PL_TRANS_GUARDS th]) THEN
  REWRITE_TAC[ARITH_EQ; pl_eq_ok; pl_eq_lhs; pl_eq_rhs] THEN
  ASM_REWRITE_TAC[] THEN TRY(ASM_ARITH_TAC THEN NO_TAC) THEN
  PL_FIRED_TAC PL_TRANS_FIRED);;

(* ------------------------------------------------------------------------- *)
(* REFL: the equation's type and row built by interning (EQBUILD).           *)
(* ------------------------------------------------------------------------- *)

let PL_REFL_GUARDS = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk t.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
     ==> ((nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RRefl t) /\
           ?tm. fdtm nms tys ntms t tm) <=> holr_live 2 t (LENGTH ntms) drops)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nat_ops_live; holr_operands; ALL; FST; SND] THEN
  ASM_CASES_TAC `holr_live 2 t (LENGTH (ntms:(num#num#num#num#num)list)) drops` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `t < LENGTH (ntms:(num#num#num#num#num)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[holr_live]; ALL_TAC] THEN
  MP_TAC(SPEC_ALL PL_TM_ROW) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let FDTY_TYAPP = el 1 (CONJUNCTS(SPEC_ALL fdty_RULES));;
let FDTYS_CONS = el 3 (CONJUNCTS(SPEC_ALL fdty_RULES));;
let FDDB_CONST = el 2 (CONJUNCTS(SPEC_ALL fddb_RULES));;
let FDDB_COMB = el 3 (CONJUNCTS(SPEC_ALL fddb_RULES));;

let pl_refl_fired_goal =
 `!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk t l1 f1 l2 l3 e q x k
   mt1 mt2 mt3 mt4 mt5 md1 md2 md3 cw'.
   pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
   holr_live 2 t (LENGTH ntms) drops /\
   pl_interned tys (3,ntm_ty (EL t ntms),3) l1 mt1 /\
   pl_interned (APPEND tys mt1) (1,1,l1) f1 mt2 /\
   pl_interned (APPEND (APPEND tys mt1) mt2) (3,f1,0) l2 mt3 /\
   pl_interned (APPEND (APPEND (APPEND tys mt1) mt2) mt3) (3,ntm_ty (EL t ntms),l2) l3 mt4 /\
   pl_interned (APPEND (APPEND (APPEND (APPEND tys mt1) mt2) mt3) mt4) (1,1,l3) e mt5 /\
   pl_interned dbs (2,2,e) q md1 /\
   pl_interned (APPEND dbs md1) (3,q,ntm_db (EL t ntms)) x md2 /\
   pl_interned (APPEND (APPEND dbs md1) md2) (3,x,ntm_db (EL t ntms)) k md3 /\
   LENGTH ths + 1 < 2 EXP 60 /\ (!n. n <= 6 ==> cw' n = cw n)
   ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RRefl t)
         (ctx,nms,APPEND (APPEND (APPEND (APPEND (APPEND tys mt1) mt2) mt3) mt4) mt5,ntms,
          APPEND (APPEND (APPEND dbs md1) md2) md3,APPEND ths [(0,k)],nmap,ymap,drops,pol) /\
       pl_inv (cw',(ctx,nms,APPEND (APPEND (APPEND (APPEND (APPEND tys mt1) mt2) mt3) mt4) mt5,ntms,
                    APPEND (APPEND (APPEND dbs md1) md2) md3,APPEND ths [(0,k)],nmap,ymap,drops,pol),stk)`;;


let PL_TY_STEP_TAC tys key pay mt ok_tac =
  MP_TAC(ISPECL [`ctx:hupdate list`; `nms:string list`; tys; `dbs:(num#num#num)list`; key; pay; mt] PL_TY_STEP) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      REWRITE_TAC[ty_key_ok; ARITH_EQ; LENGTH_APPEND] THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN
      ASM_ARITH_TAC;
      ok_tac];
    ALL_TAC] THEN
  STRIP_TAC;;

let PL_DB_STEP_TAC tys dbs key pay md ok_tac =
  MP_TAC(ISPECL [`ctx:hupdate list`; `nms:string list`; tys; dbs; key; pay; md] PL_DB_STEP) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      REWRITE_TAC[db_key_ok; ARITH_EQ; LENGTH_APPEND] THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN
      ASM_ARITH_TAC;
      ok_tac];
    ALL_TAC] THEN
  STRIP_TAC;;

(* The appended row at index LENGTH T of APPEND T [key] is key. *)
let PL_EL_SNOC = prove
 (`!(T:(num#num#num)list) key. LENGTH T < LENGTH (APPEND T [key]) /\ EL (LENGTH T) (APPEND T [key]) = key`,
  REWRITE_TAC[LENGTH_APPEND; LENGTH; EL_APPEND; LT_REFL; SUB_REFL; EL; HD] THEN ARITH_TAC);;

let FDTY_FUN = prove
 (`!nms tys i t u. fdty nms tys i t /\ fdty nms tys i u ==> t = u`, MESON_TAC[FDTY_FUNCTIONAL]);;

let PL_EXT_TAC =
  let e1 = CONJUNCT1(SPEC_ALL PL_FDTY_APPEND) and e2 = CONJUNCT2(SPEC_ALL PL_FDTY_APPEND)
  and d1 = CONJUNCT1(SPEC_ALL PL_FDDB_APPEND) and d2 = CONJUNCT2(SPEC_ALL PL_FDDB_APPEND)
  and t1 = CONJUNCT1(SPEC_ALL PL_FDDB_TYS_APPEND) and t2 = CONJUNCT2(SPEC_ALL PL_FDDB_TYS_APPEND) in
  let rec tac g =
    (FIRST_ASSUM ACCEPT_TAC ORELSE
     ((MATCH_MP_TAC e1 ORELSE MATCH_MP_TAC e2 ORELSE MATCH_MP_TAC d1 ORELSE MATCH_MP_TAC d2 ORELSE
       MATCH_MP_TAC t1 ORELSE MATCH_MP_TAC t2) THEN tac)) g in
  tac;;
let pl_ty_t = `htypeof tm` and pl_y_t = `ntm_ty (EL t (ntms:(num#num#num#num#num)list))`
and pl_d_t = `ntm_db (EL t (ntms:(num#num#num#num#num)list))`;;
let PL_TAB0 = `tys:(num#num#num)list` and PL_TAB1 = `APPEND (tys:(num#num#num)list) mt1`
and PL_TAB2 = `APPEND (APPEND (tys:(num#num#num)list) mt1) mt2`
and PL_TAB3 = `APPEND (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) mt3`
and PL_TAB4 = `APPEND (APPEND (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) mt3) mt4`
and PL_TAB5 = `APPEND (APPEND (APPEND (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) mt3) mt4) mt5`;;
let PL_DBT0 = `dbs:(num#num#num)list` and PL_DBT1 = `APPEND (dbs:(num#num#num)list) md1`
and PL_DBT2 = `APPEND (APPEND (dbs:(num#num#num)list) md1) md2`
and PL_DBT3 = `APPEND (APPEND (APPEND (dbs:(num#num#num)list) md1) md2) md3`;;
(* the appended row decodes as a list, through the cons rule *)
let PL_CONS_OK_TAC a b l =
  REWRITE_TAC[fibre_ty_ok] THEN DISJ2_TAC THEN EXISTS_TAC l THEN CONJ_TAC THENL
   [MATCH_MP_TAC FDTYS_CONS THEN MAP_EVERY EXISTS_TAC [a; b] THEN REWRITE_TAC[PL_EL_SNOC] THEN
    CONJ_TAC THEN PL_EXT_TAC;
    ASM_REWRITE_TAC[ALL]];;
(* the appended row decodes as fun applied to a list *)
let PL_FUN_OK_TAC b args =
  REWRITE_TAC[fibre_ty_ok] THEN DISJ1_TAC THEN
  EXISTS_TAC (mk_comb(mk_comb(`TyApp`, `EL 1 (nms:string list)`), args)) THEN CONJ_TAC THENL
   [MATCH_MP_TAC FDTY_TYAPP THEN EXISTS_TAC b THEN REWRITE_TAC[PL_EL_SNOC] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; PL_EXT_TAC];
    ASM_REWRITE_TAC[GSYM HFun]];;
let PL_CONS_OK_TAC a b l =
  REWRITE_TAC[fibre_ty_ok] THEN DISJ2_TAC THEN EXISTS_TAC l THEN CONJ_TAC THENL
   [MATCH_MP_TAC FDTYS_CONS THEN MAP_EVERY EXISTS_TAC [a; b] THEN REWRITE_TAC[PL_EL_SNOC] THEN
    CONJ_TAC THEN PL_EXT_TAC;
    ASM_REWRITE_TAC[ALL; GSYM HFun]];;
let PL_DEC_CONS_TAC a b = MATCH_MP_TAC FDTYS_CONS THEN MAP_EVERY EXISTS_TAC [a; b] THEN
  REPEAT CONJ_TAC THEN PL_EXT_TAC;;
let PL_DEC_FUN_TAC b = MATCH_MP_TAC FDTY_TYAPP THEN EXISTS_TAC b THEN
  REPEAT CONJ_TAC THEN (PL_EXT_TAC ORELSE ASM_ARITH_TAC);;
let PL_DBOK_TAC dec rule exs =
  DISJ1_TAC THEN EXISTS_TAC dec THEN MATCH_MP_TAC rule THEN MAP_EVERY EXISTS_TAC exs THEN
  REWRITE_TAC[PL_EL_SNOC] THEN REPEAT CONJ_TAC THEN (PL_EXT_TAC ORELSE ASM_ARITH_TAC);;
let PL_DBDEC_TAC rule exs =
  MATCH_MP_TAC rule THEN MAP_EVERY EXISTS_TAC exs THEN REPEAT CONJ_TAC THEN (PL_EXT_TAC ORELSE ASM_ARITH_TAC);;
let rec PL_TYS_OK_TAC g =
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (MATCH_MP_TAC NAT_TYS_OK_APPEND THEN REWRITE_TAC[APPEND_ASSOC] THEN CONJ_TAC THEN PL_TYS_OK_TAC)) g;;
let PL_REFL_FIRED = prove(pl_refl_fired_goal,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `t < LENGTH (ntms:(num#num#num#num#num)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[holr_live]; ALL_TAC] THEN
  MP_TAC(SPEC_ALL PL_TM_ROW) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tm:holterm` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_STD_SIG) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_TABS_OK) THEN
  FIRST_ASSUM(fun th -> if is_const_app "pl_tabs_ok" (concl th)
                        then STRIP_ASSUME_TAC(REWRITE_RULE[pl_tabs_ok] th) else failwith "") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_BOOT_LISTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_BOOL) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_NAMES_INJ) THEN
  PL_INV_FACTS_TAC THEN
  SUBGOAL_THEN `ntm_ty (EL t (ntms:(num#num#num#num#num)list)) < LENGTH (tys:(num#num#num)list) /\
                ntm_db (EL t ntms) < LENGTH (dbs:(num#num#num)list)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(CONJUNCT1(SPEC_ALL FDTY_BOUND)) THEN EXISTS_TAC `htypeof tm` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(CONJUNCT1(SPEC_ALL FDDB_BOUND)) THEN EXISTS_TAC `hdb tm` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `htype_ok (FST(hsigof ctx)) (htypeof tm)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[fibre_ty_ok] o
                C MP (ASSUME `ntm_ty (EL t (ntms:(num#num#num#num#num)list)) < LENGTH (tys:(num#num#num)list)`) o
                SPEC `ntm_ty (EL t (ntms:(num#num#num#num#num)list))` o
                check (fun th -> is_forall(concl th) && can (find_term ((=) `fibre_ty_ok`)) (concl th))) THEN
    STRIP_TAC THENL
     [SUBGOAL_THEN `ty:holtype = htypeof tm` (fun th -> ASM_MESON_TAC[th]) THEN
      MATCH_MP_TAC FDTY_FUN THEN MAP_EVERY EXISTS_TAC
       [`nms:string list`; `tys:(num#num#num)list`; `ntm_ty (EL t (ntms:(num#num#num#num#num)list))`] THEN
      ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `ntm_ty (EL t (ntms:(num#num#num#num#num)list))`;
                    `htypeof tm`; `l:holtype list`] FDTY_NOT_BOTH) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPEC `hsigof ctx` HTYPE_OK_STD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC) THEN
  (PL_TY_STEP_TAC PL_TAB0 `(3,ntm_ty (EL t (ntms:(num#num#num#num#num)list)),3)` `l1:num` `mt1:(num#num#num)list`
    (PL_CONS_OK_TAC pl_y_t `3` `[htypeof tm; HBool]`)) THEN
  (SUBGOAL_THEN `fdtys nms (APPEND (tys:(num#num#num)list) mt1) l1 [htypeof tm; HBool]` ASSUME_TAC THENL
   [PL_DEC_CONS_TAC pl_y_t `3`; ALL_TAC]) THEN
  (PL_TY_STEP_TAC PL_TAB1 `(1,1,l1:num)` `f1:num` `mt2:(num#num#num)list` (PL_FUN_OK_TAC `l1:num` `[htypeof tm; HBool]`)) THEN
  (SUBGOAL_THEN `fdty nms (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) f1 (TyApp (EL 1 nms) [htypeof tm; HBool])`
    ASSUME_TAC THENL [PL_DEC_FUN_TAC `l1:num`; ALL_TAC]) THEN
  (PL_TY_STEP_TAC PL_TAB2 `(3,f1:num,0)` `l2:num` `mt3:(num#num#num)list`
    (PL_CONS_OK_TAC `f1:num` `0` `[TyApp (EL 1 nms) [htypeof tm; HBool]]`)) THEN
  (SUBGOAL_THEN `fdtys nms (APPEND (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) mt3) l2
                      [TyApp (EL 1 nms) [htypeof tm; HBool]]` ASSUME_TAC THENL
   [PL_DEC_CONS_TAC `f1:num` `0`; ALL_TAC]) THEN
  (PL_TY_STEP_TAC PL_TAB3 `(3,ntm_ty (EL t (ntms:(num#num#num#num#num)list)),l2:num)` `l3:num` `mt4:(num#num#num)list`
    (PL_CONS_OK_TAC pl_y_t `l2:num` `[htypeof tm; TyApp (EL 1 nms) [htypeof tm; HBool]]`)) THEN
  (SUBGOAL_THEN `fdtys nms (APPEND (APPEND (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) mt3) mt4) l3
                      [htypeof tm; TyApp (EL 1 nms) [htypeof tm; HBool]]` ASSUME_TAC THENL
   [PL_DEC_CONS_TAC pl_y_t `l2:num`; ALL_TAC]) THEN
  (PL_TY_STEP_TAC PL_TAB4 `(1,1,l3:num)` `e:num` `mt5:(num#num#num)list`
    (PL_FUN_OK_TAC `l3:num` `[htypeof tm; TyApp (EL 1 nms) [htypeof tm; HBool]]`)) THEN
  (SUBGOAL_THEN `fdty nms (APPEND (APPEND (APPEND (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) mt3) mt4) mt5) e
                     (TyApp (EL 1 nms) [htypeof tm; TyApp (EL 1 nms) [htypeof tm; HBool]])` ASSUME_TAC THENL
   [PL_DEC_FUN_TAC `l3:num`; ALL_TAC]) THEN
  (PL_DB_STEP_TAC PL_TAB5 PL_DBT0 `(2,2,e:num)` `q:num` `md1:(num#num#num)list`
    (PL_DBOK_TAC `hdbConst (EL 2 nms) (TyApp (EL 1 nms) [htypeof tm; TyApp (EL 1 nms) [htypeof tm; HBool]])`
                 FDDB_CONST [`e:num`])) THEN
  (SUBGOAL_THEN `fddb nms (APPEND (APPEND (APPEND (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) mt3) mt4) mt5)
                     (APPEND (dbs:(num#num#num)list) md1) q
                     (hdbConst (EL 2 nms) (TyApp (EL 1 nms) [htypeof tm; TyApp (EL 1 nms) [htypeof tm; HBool]]))`
    ASSUME_TAC THENL [PL_DBDEC_TAC FDDB_CONST [`e:num`]; ALL_TAC]) THEN
  (PL_DB_STEP_TAC PL_TAB5 PL_DBT1 `(3,q:num,ntm_db (EL t (ntms:(num#num#num#num#num)list)))` `x:num` `md2:(num#num#num)list`
    (PL_DBOK_TAC `hdbComb (hdbConst (EL 2 nms) (TyApp (EL 1 nms) [htypeof tm; TyApp (EL 1 nms) [htypeof tm; HBool]])) (hdb tm)`
                 FDDB_COMB [`q:num`; pl_d_t])) THEN
  (SUBGOAL_THEN `fddb nms (APPEND (APPEND (APPEND (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) mt3) mt4) mt5)
                     (APPEND (APPEND (dbs:(num#num#num)list) md1) md2) x
                     (hdbComb (hdbConst (EL 2 nms) (TyApp (EL 1 nms) [htypeof tm; TyApp (EL 1 nms) [htypeof tm; HBool]])) (hdb tm))`
    ASSUME_TAC THENL [PL_DBDEC_TAC FDDB_COMB [`q:num`; pl_d_t]; ALL_TAC]) THEN
  (PL_DB_STEP_TAC PL_TAB5 PL_DBT2 `(3,x:num,ntm_db (EL t (ntms:(num#num#num#num#num)list)))` `k:num` `md3:(num#num#num)list`
    (PL_DBOK_TAC `hdbComb (hdbComb (hdbConst (EL 2 nms) (TyApp (EL 1 nms) [htypeof tm; TyApp (EL 1 nms) [htypeof tm; HBool]])) (hdb tm)) (hdb tm)`
                 FDDB_COMB [`x:num`; pl_d_t])) THEN
  (SUBGOAL_THEN `fddb nms (APPEND (APPEND (APPEND (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) mt3) mt4) mt5)
                     (APPEND (APPEND (APPEND (dbs:(num#num#num)list) md1) md2) md3) k
                     (hdbComb (hdbComb (hdbConst (EL 2 nms) (TyApp (EL 1 nms) [htypeof tm; TyApp (EL 1 nms) [htypeof tm; HBool]])) (hdb tm)) (hdb tm))`
    ASSUME_TAC THENL [PL_DBDEC_TAC FDDB_COMB [`x:num`; pl_d_t]; ALL_TAC]) THEN
  (SUBGOAL_THEN `fddb nms (APPEND (APPEND (APPEND (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) mt3) mt4) mt5)
                     (APPEND (APPEND (APPEND (dbs:(num#num#num)list) md1) md2) md3) k (hdb (tm =:= tm))`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "fddb" (concl th) &&
                    can (find_term ((=) `k:num`)) (concl th))) THEN
    ASM_REWRITE_TAC[HDB_EQUATION; HFun];
    ALL_TAC]) THEN
  (FIRST_ASSUM(fun th -> if is_const_app "pl_tabs_ok" (concl th) &&
                           can (find_term ((=) `md3:(num#num#num)list`)) (concl th)
                        then STRIP_ASSUME_TAC(REWRITE_RULE[pl_tabs_ok] th) else failwith "")) THEN
  (SUBGOAL_THEN `nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RRefl t)
         (ctx,nms,APPEND (APPEND (APPEND (APPEND (APPEND tys mt1) mt2) mt3) mt4) mt5,ntms,
          APPEND (APPEND (APPEND dbs md1) md2) md3,APPEND ths [(0,k)],nmap,ymap,drops,pol)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                  `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                  `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `t:num`; `tm:holterm`;
                  `APPEND mt1 (APPEND mt2 (APPEND mt3 (APPEND mt4 mt5))):(num#num#num)list`;
                  `APPEND md1 (APPEND md2 md3):(num#num#num)list`; `0`; `k:num`] NAT_STEP_REFL) THEN
    REWRITE_TAC[APPEND_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[nat_ops_live; holr_operands; ALL; FST; SND] THEN REPEAT CONJ_TAC THENL
     [PL_TYS_OK_TAC;
      MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
                    `APPEND mt1 (APPEND mt2 (APPEND mt3 (APPEND mt4 mt5))):(num#num#num)list`;
                    `APPEND md1 (APPEND md2 md3):(num#num#num)list`] NAT_KEYS_NEW_ROWS) THEN
      REWRITE_TAC[APPEND_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM LENGTH_APPEND; GSYM APPEND_ASSOC] THEN REWRITE_TAC[APPEND_ASSOC] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      PL_EXT_TAC];
    ALL_TAC]) THEN
  (ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`;
                `cw':num->num`; `RRefl t`;
                `APPEND mt1 (APPEND mt2 (APPEND mt3 (APPEND mt4 mt5))):(num#num#num)list`;
                `APPEND md1 (APPEND md2 md3):(num#num#num)list`; `0`; `k:num`] PL_INV_THM_STEP) THEN
  REWRITE_TAC[APPEND_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM LENGTH_APPEND; GSYM APPEND_ASSOC] THEN REWRITE_TAC[APPEND_ASSOC] THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `[]:num list` THEN REWRITE_TAC[pl_ids; PAIRWISE] THEN
  ASM_SIMP_TAC[EL_APPEND; LENGTH_APPEND; ARITH_RULE `1 <= l ==> 0 < l /\ 0 < l + m`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN ASM_ARITH_TAC));;


let pl_refl_goal =
 `!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk t k i cw' ns' stk'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ cw 8 = t /\
     pl_run pl_plan_refl 0 (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) (k,i,(cw',ns',stk'))
     ==> (k = 1 ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RRefl t) ns' /\
                    pl_inv (cw',ns',stk')) /\
         (k = 0 <=> ~(nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RRefl t) /\
                      ?tm. fdtm nms tys ntms t tm))`;;

(* PL_REFL: the plan's FIRED run is REFL's nat_step and keeps pl_inv; it is *)
(* REFUSED exactly when t is not live.                                       *)
let PL_REFL = prove(pl_refl_goal,
  PL_START_TAC pl_plan_refl THEN
  PL_INV_ASM(fun th -> REWRITE_TAC[MATCH_MP PL_REFL_GUARDS th]) THEN REWRITE_TAC[ARITH_EQ] THEN
  ASM_REWRITE_TAC[] THEN TRY(ASM_ARITH_TAC THEN NO_TAC) THEN PL_FIRED_TAC PL_REFL_FIRED);;

(* ------------------------------------------------------------------------- *)
(* EXPECT_ALPHA: the theorem's conclusion and hypotheses are the listed ones. *)
(* ------------------------------------------------------------------------- *)

let PL_SEL_TM = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk x.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ x < LENGTH ntms
     ==> fdtm nms tys ntms x (@p. fdtm nms tys ntms x p) /\
         fddb nms tys dbs (ntm_db (EL x ntms)) (hdb (@p. fdtm nms tys ntms x p)) /\
         fdty nms tys (ntm_ty (EL x ntms)) (htypeof (@p. fdtm nms tys ntms x p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `fdtm nms tys ntms x (@p. fdtm nms tys ntms x p)` ASSUME_TAC THENL
   [CONV_TAC SELECT_CONV THEN MP_TAC(SPECL [`cw:num->num`; `ctx:hupdate list`; `nms:string list`;
      `tys:(num#num#num)list`; `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
      `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`; `x:num`] PL_TM_ROW) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_TM_DEC THEN
    MAP_EVERY EXISTS_TAC [`cw:num->num`; `ctx:hupdate list`; `ths:(num#num)list`; `nmap:num list`;
                          `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`] THEN
    ASM_REWRITE_TAC[]]);;
let FDDBS_FUN = prove
 (`!nms tys dbs i l m. fddbs nms tys dbs i l /\ fddbs nms tys dbs i m ==> l = m`,
  MESON_TAC[FDDB_FUNCTIONAL]);;
let FDTM_FUN = prove
 (`!nms tys ntms i t u. fdtm nms tys ntms i t /\ fdtm nms tys ntms i u ==> t = u`,
  MESON_TAC[FDTM_FUNCTIONAL]);;

let PL_MEM_DEC = prove
 (`!(rel:num->A->bool) (dec:num->A) (img:B->num) (R:B->C->bool) (h:C->A) ids hl hyps.
     (!i j t. rel i t /\ rel j t ==> i = j) /\ (!i t u. rel i t /\ rel i u ==> t = u) /\
     (!i. MEM i ids ==> rel i (dec i)) /\ ALL2 R hl hyps /\
     (!x y. MEM x hl /\ R x y ==> rel (img x) (h y))
     ==> ((!z. MEM z (MAP dec ids) <=> MEM z (MAP h hyps)) <=> (!i. MEM i ids <=> MEM i (MAP img hl)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[MEM_MAP] THEN EQ_TAC THEN DISCH_TAC THENL
  [(X_GEN_TAC `i:num` THEN EQ_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(dec:num->A) i` o check (fun th -> is_forall(concl th) &&
                    can (find_term (fun t -> try fst(dest_var t) = "dec" with _ -> false)) (concl th) &&
                    can (find_term (fun t -> try fst(dest_var t) = "h" with _ -> false)) (concl th))) THEN
    MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
     [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:C` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`R:B->C->bool`; `hl:B list`; `hyps:C list`; `y:C`] ALL2_MEM_RIGHT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x:B` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(rel:num->A->bool) i (dec i) /\ rel ((img:B->num) x) (dec i)` MP_TAC THENL
     [ASM_SIMP_TAC[]; ASM_MESON_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`R:B->C->bool`; `hl:B list`; `hyps:C list`; `x:B`] ALL2_MEM_LEFT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:C` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(h:C->A) y` o check (fun th -> is_forall(concl th) &&
                    can (find_term (fun t -> try fst(dest_var t) = "dec" with _ -> false)) (concl th) &&
                    can (find_term (fun t -> try fst(dest_var t) = "h" with _ -> false)) (concl th))) THEN
    MATCH_MP_TAC(TAUT `b /\ (a ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
     [EXISTS_TAC `y:C` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(rel:num->A->bool) j ((h:C->A) y) /\ rel ((img:B->num) x) (h y)` MP_TAC THENL
     [ASM_SIMP_TAC[]; ASM_MESON_TAC[]]]);
   (X_GEN_TAC `z:A` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?x. MEM x hl /\ i = (img:B->num) x` (X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`R:B->C->bool`; `hl:B list`; `hyps:C list`; `x:B`] ALL2_MEM_LEFT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:C` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:C` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(rel:num->A->bool) i (dec i) /\ rel i ((h:C->A) y)` MP_TAC THENL
     [ASM_SIMP_TAC[]; ASM_MESON_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `y:C` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`R:B->C->bool`; `hl:B list`; `hyps:C list`; `y:C`] ALL2_MEM_RIGHT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(img:B->num) x` THEN
    SUBGOAL_THEN `MEM ((img:B->num) x) ids` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(rel:num->A->bool) (img x) (dec (img x)) /\ rel ((img:B->num) x) ((h:C->A) y)` MP_TAC THENL
     [ASM_SIMP_TAC[]; ASM_MESON_TAC[]]])]);;

let is_dec_fact th = is_forall(concl th) &&
  (let _,b = strip_forall(concl th) in is_imp b && is_exists(rand b) &&
     (let _,eb = dest_exists(rand b) in is_const_app "fddb" eb));;
let pl_ea_guard_goal =
 `!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h hl c.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
     ==> ((?hsd cn hyps. nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RExpectAlpha h hl c) /\
                         fddbs nms tys dbs (FST(EL h ths)) hsd /\
                         fdtm nms tys ntms c cn /\ fddb nms tys dbs (SND(EL h ths)) (hdb cn) /\
                         ALL2 (fdtm nms tys ntms) hl hyps /\ ALL (\p. htypeof p = HBool) hyps /\
                         (!x. MEM x hsd <=> MEM x (MAP hdb hyps))) <=>
          holr_live 3 h (LENGTH ths) drops /\ holr_live 2 c (LENGTH ntms) drops /\
          SND(EL h ths) = ntm_db (EL c ntms) /\
          ALL (\x. holr_live 2 x (LENGTH ntms) drops /\ ntm_ty (EL x ntms) = 1) hl /\
          (?ids. pl_ids dbs (FST(EL h ths)) ids /\ PAIRWISE (<) ids /\
                 (!x. MEM x ids <=> MEM x (MAP (\x. ntm_db (EL x ntms)) hl))))`;;
let PL_EA_GUARDS = prove(pl_ea_guard_goal,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[nat_ops_live; holr_operands; ALL; FST; SND] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_CANON) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_BOOL) THEN
  ASM_CASES_TAC `holr_live 3 h (LENGTH (ths:(num#num)list)) drops` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `holr_live 2 c (LENGTH (ntms:(num#num#num#num#num)list)) drops` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `h < LENGTH (ths:(num#num)list) /\ c < LENGTH (ntms:(num#num#num#num#num)list)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[holr_live]; ALL_TAC] THEN
  PL_INV_FACTS_TAC THEN
  MP_TAC(PL_SPEC [`h:num`] PL_THM_DEC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_TAC `hs0:hdbterm list`)) THEN
  MP_TAC(PL_SPEC [`c:num`] PL_TM_ROW) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cn0:holterm` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x y. MEM x hl /\ fdtm nms tys ntms x y
                      ==> fddb nms tys dbs (ntm_db (EL x (ntms:(num#num#num#num#num)list))) (hdb y)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MP_TAC(PL_SPEC [`x:num`; `y:holterm`] PL_TM_DEC) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  EQ_TAC THENL
   [(DISCH_THEN(X_CHOOSE_THEN `hsd:hdbterm list` (X_CHOOSE_THEN `cn:holterm`
      (X_CHOOSE_THEN `hyps:holterm list` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `cn:holterm = cn0` SUBST_ALL_TAC THENL [ASM_MESON_TAC[FDTM_FUN]; ALL_TAC] THEN
    SUBGOAL_THEN `hsd:hdbterm list = hs0` SUBST_ALL_TAC THENL [ASM_MESON_TAC[FDDBS_FUN]; ALL_TAC] THEN
    SUBGOAL_THEN `?ids. pl_ids dbs (FST(EL h (ths:(num#num)list))) ids /\ PAIRWISE (<) ids`
      (X_CHOOSE_THEN `ids:num list` STRIP_ASSUME_TAC) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`ids:num list`; `nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
                  `FST(EL h (ths:(num#num)list))`; `hs0:hdbterm list`] PL_FDDBS_IDS) THEN
    ASM_REWRITE_TAC[GSYM ALL_MEM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `hs0:hdbterm list`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
       (let _,b = strip_forall(concl th) in is_imp b && is_eq(rand b) &&
          can (find_term (fun t -> try fst(dest_const t) = "fddb" with _ -> false)) (lhand b) &&
          type_of(lhs(rand b)) = `:num`))) THEN
    EXISTS_TAC `hdb cn0` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
         can (find_term (fun t -> try fst(dest_const t) = "holr_live" with _ -> false)) (concl th) &&
         can (find_term (fun t -> try fst(dest_var t) = "hl" with _ -> false)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`fdtm nms tys ntms`; `hl:num list`; `hyps:holterm list`; `x:num`] ALL2_MEM_LEFT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:holterm` STRIP_ASSUME_TAC) THEN
      MP_TAC(PL_SPEC [`ntm_ty (EL x (ntms:(num#num#num#num#num)list))`; `htypeof y`] PL_TYPE_BOOL) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MP_TAC(PL_SPEC [`x:num`; `y:holterm`] PL_TM_DEC) THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
         can (find_term (fun t -> try fst(dest_const t) = "htypeof" with _ -> false)) (concl th) &&
         can (find_term (fun t -> try fst(dest_var t) = "hyps" with _ -> false)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    EXISTS_TAC `ids:num list` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`fddb nms tys dbs`; `pl_dec nms tys dbs`; `\x. ntm_db (EL x (ntms:(num#num#num#num#num)list))`;
                   `fdtm nms tys ntms`; `hdb`; `ids:num list`; `hl:num list`; `hyps:holterm list`] PL_MEM_DEC) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MESON_TAC[FDDB_FUN];
        X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check is_dec_fact) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `t0:hdbterm`) THEN
        FIRST_ASSUM(SUBST1_TAC o MATCH_MP PL_DEC) THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC]]);
    ((REWRITE_TAC[GSYM ALL_MEM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `ids:num list` STRIP_ASSUME_TAC)))) THEN
    (MP_TAC(SPECL [`ids:num list`; `nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
                `FST(EL h (ths:(num#num)list))`; `hs0:hdbterm list`] PL_FDDBS_IDS) THEN
  ASM_REWRITE_TAC[GSYM ALL_MEM] THEN STRIP_TAC) THEN
    (FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `hs0:hdbterm list`))) THEN
    (SUBGOAL_THEN `!x. MEM x hl ==> x < LENGTH (ntms:(num#num#num#num#num)list)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o check (fun th -> is_forall(concl th) &&
         can (find_term (fun t -> try fst(dest_const t) = "holr_live" with _ -> false)) (concl th) &&
         can (find_term (fun t -> try fst(dest_var t) = "hl" with _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[holr_live] THEN SIMP_TAC[];
    ALL_TAC]) THEN
    (MAP_EVERY EXISTS_TAC [`MAP (pl_dec nms tys dbs) ids`; `cn0:holterm`;
                        `MAP (\x. @p. fdtm nms tys ntms x p) (hl:num list)`]) THEN
    (SUBGOAL_THEN `ALL2 (fdtm nms tys ntms) hl (MAP (\x. @p. fdtm nms tys ntms x p) (hl:num list))` ASSUME_TAC THENL
   [MATCH_MP_TAC ALL2_MAP_SELF THEN REWRITE_TAC[GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(PL_SPEC [`x:num`] PL_SEL_TM) THEN ASM_SIMP_TAC[];
    ALL_TAC]) THEN
    (ASM_REWRITE_TAC[]) THEN
    REPEAT CONJ_TAC THENL [(REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o check (fun th -> is_forall(concl th) &&
         can (find_term (fun t -> try fst(dest_const t) = "ntm_ty" with _ -> false)) (concl th) &&
         can (find_term (fun t -> try fst(dest_var t) = "hl" with _ -> false)) (concl th))) THEN
    ASM_SIMP_TAC[]); (REWRITE_TAC[MEM_MAP] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MP_TAC(PL_SPEC [`ntm_ty (EL x' (ntms:(num#num#num#num#num)list))`; `htypeof (@p. fdtm nms tys ntms x' p)`] PL_TYPE_BOOL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN MP_TAC(PL_SPEC [`x':num`] PL_SEL_TM) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x':num` o check (fun th -> is_forall(concl th) &&
         can (find_term (fun t -> try fst(dest_const t) = "ntm_ty" with _ -> false)) (concl th) &&
         can (find_term (fun t -> try fst(dest_var t) = "hl" with _ -> false)) (concl th))) THEN
  ASM_SIMP_TAC[]); (MP_TAC(ISPECL [`fddb nms tys dbs`; `pl_dec nms tys dbs`; `\x. ntm_db (EL x (ntms:(num#num#num#num#num)list))`;
                   `fdtm nms tys ntms`; `hdb`; `ids:num list`; `hl:num list`;
                   `MAP (\x. @p. fdtm nms tys ntms x p) (hl:num list)`] PL_MEM_DEC) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MESON_TAC[FDDB_FUN];
        X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check is_dec_fact) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `t0:hdbterm`) THEN
        FIRST_ASSUM(SUBST1_TAC o MATCH_MP PL_DEC) THEN ASM_REWRITE_TAC[]];
      DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC])])]);;

let PL_EA_FIRED = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h c hl cw'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     holr_live 3 h (LENGTH ths) drops /\ holr_live 2 c (LENGTH ntms) drops /\
     SND(EL h ths) = ntm_db (EL c ntms) /\
     ALL (\x. holr_live 2 x (LENGTH ntms) drops /\ ntm_ty (EL x ntms) = 1) hl /\
     (?ids. pl_ids dbs (FST(EL h ths)) ids /\ PAIRWISE (<) ids /\
            (!x. MEM x ids <=> MEM x (MAP (\x. ntm_db (EL x ntms)) hl))) /\
     (!n. n <= 6 ==> cw' n = cw n)
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RExpectAlpha h hl c)
                  (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\
         pl_inv (cw',(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(PL_SPEC [`h:num`; `hl:num list`; `c:num`] PL_EA_GUARDS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN
    ANTS_TAC THENL [EXISTS_TAC `ids:num list` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `hsd:hdbterm list` (X_CHOOSE_THEN `cn:holterm`
      (X_CHOOSE_THEN `hyps:holterm list` STRIP_ASSUME_TAC))) THEN
    MATCH_MP_TAC NAT_STEP_EXPECT_ALPHA THEN
    MAP_EVERY EXISTS_TAC [`hsd:hdbterm list`; `cn:holterm`; `hyps:holterm list`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_INV_CW THEN EXISTS_TAC `cw:num->num` THEN ASM_REWRITE_TAC[]]);;

let PL_EA_CLOSE_TAC =
  FIRST
   [CONJ_TAC THENL [PL_FIRED_TAC PL_EA_FIRED; PL_WITNESS_TAC THEN ASM_REWRITE_TAC[]] THEN NO_TAC;
    PL_INV_FACTS_TAC THEN REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `ids0:num list` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> let c = concl th in
      if is_neg c && is_eq(dest_neg c) && rand(dest_neg c) = `FST(EL h (ths:(num#num)list))`
      then MP_TAC th else failwith "") THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC PL_FINDL_UNIQUE THEN PL_WITNESS_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `ids0:num list` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) && is_conj(dest_neg(concl th)))) THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`FST(EL h (ths:(num#num)list))`; `ids0:num list`] THEN
    ASM_REWRITE_TAC[]];;

let pl_expect_alpha_goal =
 `!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h c hl k i cw' ns' stk'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     cw 8 = h /\ cw 10 = c /\ cw 13 + cw 12 <= LENGTH stk /\
     list_of_seq (\j. EL (cw 13 + j) stk) (cw 12) = hl /\
     pl_run pl_plan_expect_alpha 0 (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) (k,i,(cw',ns',stk'))
     ==> (k = 1 ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RExpectAlpha h hl c) ns' /\
                    pl_inv (cw',ns',stk')) /\
         (k = 0 <=> ~(?hsd cn hyps. nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RExpectAlpha h hl c) /\
                                    fddbs nms tys dbs (FST(EL h ths)) hsd /\
                                    fdtm nms tys ntms c cn /\ fddb nms tys dbs (SND(EL h ths)) (hdb cn) /\
                                    ALL2 (fdtm nms tys ntms) hl hyps /\ ALL (\p. htypeof p = HBool) hyps /\
                                    (!x. MEM x hsd <=> MEM x (MAP hdb hyps))))`;;

(* PL_EXPECT_ALPHA: the plan's FIRED run is EXPECT_ALPHA's nat_step (no row *)
(* written) and keeps pl_inv; it is REFUSED exactly when the clause's      *)
(* premises fail: an operand not live, h's conclusion not c's image, a     *)
(* listed term not of type bool, or h's hypotheses not the listed terms'   *)
(* images.                                                                   *)
let PL_EXPECT_ALPHA = prove(pl_expect_alpha_goal,
  PL_START_TAC pl_plan_expect_alpha THEN
  PL_INV_ASM(fun th -> REWRITE_TAC[MATCH_MP PL_EA_GUARDS th]) THEN REWRITE_TAC[ARITH_EQ] THEN
  ASM_REWRITE_TAC[] THEN TRY(ASM_ARITH_TAC THEN NO_TAC) THEN PL_EA_CLOSE_TAC);;

(* ------------------------------------------------------------------------- *)
(* MK_COMB.                                                                  *)
(* ------------------------------------------------------------------------- *)

(* MK_COMB: the function types read off the equality constants' type rows  *)
(* (a function type row is fun applied to a two-element list), the two     *)
(* combinations interned, the equation built (EQBUILD), the hypotheses      *)
(* united.                                                                   *)
let FDTY_TYAPP_INV = prove
 (`!nms tys y n args.
     fdty nms tys y (TyApp n args) <=>
     y < LENGTH tys /\ FST(EL y tys) = 1 /\ FST(SND(EL y tys)) < LENGTH nms /\
     EL (FST(SND(EL y tys))) nms = n /\ fdtys nms tys (SND(SND(EL y tys))) args`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [CONJUNCT1(SPEC_ALL fdty_CASES)] THEN
  REWRITE_TAC[holtype_DISTINCT; holtype_INJ] THEN
  SPEC_TAC(`EL y (tys:(num#num#num)list)`,`r:num#num#num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; FST; SND] THEN MESON_TAC[]);;

let FDTYS_CONS_INV = prove
 (`!nms tys l a rest.
     fdtys nms tys l (CONS a rest) <=>
     l < LENGTH tys /\ FST(EL l tys) = 3 /\ fdty nms tys (FST(SND(EL l tys))) a /\
     fdtys nms tys (SND(SND(EL l tys))) rest`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [CONJUNCT2(SPEC_ALL fdty_CASES)] THEN
  REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN
  SPEC_TAC(`EL l (tys:(num#num#num)list)`,`r:num#num#num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; FST; SND] THEN MESON_TAC[]);;

let FDTY_TAG_INV = prove
 (`!nms tys y X. fdty nms tys y X ==> FST(EL y tys) = 1 ==> ?n args. X = TyApp n args`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [CONJUNCT1(SPEC_ALL fdty_CASES)] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[holtype_DISTINCT; holtype_INJ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[]);;

let FDTYS_TAG_INV = prove
 (`!nms tys l L. fdtys nms tys l L
                 ==> (FST(EL l tys) = 3 ==> ?a r. L = CONS a r) /\ (FST(EL l tys) = 2 ==> L = [])`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [CONJUNCT2(SPEC_ALL fdty_CASES)] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[NOT_CONS_NIL] THEN CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[]);;

let PL_CANON_TYS = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
     ==> (!i j l. fdtys nms tys i l /\ fdtys nms tys j l ==> i = j)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o MATCH_MP PL_INV_NAT) THEN
  REWRITE_TAC[nat_canon; fdty_same] THEN MESON_TAC[]);;

let FDTYS_FUN = prove
 (`!nms tys i l m. fdtys nms tys i l /\ fdtys nms tys i m ==> l = m`, MESON_TAC[FDTY_FUNCTIONAL]);;

(* A type row of a function type: fun applied to a two-element list. *)
let pl_fun_ok = new_definition
 `pl_fun_ok (tys:(num#num#num)list) y <=>
    FST(EL y tys) = 1 /\ FST(SND(EL y tys)) = 1 /\
    FST(EL (SND(SND(EL y tys))) tys) = 3 /\
    FST(EL (SND(SND(EL (SND(SND(EL y tys))) tys))) tys) = 3 /\
    SND(SND(EL (SND(SND(EL (SND(SND(EL y tys))) tys))) tys)) = 0`;;
let pl_fun_dom = new_definition
 `pl_fun_dom (tys:(num#num#num)list) y = FST(SND(EL (SND(SND(EL y tys))) tys))`;;
let pl_fun_cod = new_definition
 `pl_fun_cod (tys:(num#num#num)list) y = FST(SND(EL (SND(SND(EL (SND(SND(EL y tys))) tys))) tys))`;;

let PL_FUN_DEC = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk y X.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ fdty nms tys y X
     ==> ((?D C. X = HFun D C) <=> pl_fun_ok tys y) /\
         (!D C. X = HFun D C ==> fdty nms tys (pl_fun_dom tys y) D /\ fdty nms tys (pl_fun_cod tys y) C)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_NAMES_INJ) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_CANON_TYS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_BOOT_LISTS) THEN
  PL_INV_FACTS_TAC THEN
  SUBGOAL_THEN `!D C. X = HFun D C ==> pl_fun_ok tys y /\ fdty nms tys (pl_fun_dom tys y) D /\
                                      fdty nms tys (pl_fun_cod tys y) C` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `fdty nms tys y (HFun D C)` THEN
    REWRITE_TAC[HFun; FDTY_TYAPP_INV; FDTYS_CONS_INV; pl_fun_ok; pl_fun_dom; pl_fun_cod] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[NAMES_INJ] o
                    check (fun th -> is_const_app "NAMES_INJ" (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
         can (find_term (fun t -> try fst(dest_const t) = "fdtys" with _ -> false)) (concl th) &&
         (let _,b = strip_forall(concl th) in is_imp b && is_eq(rand b)))) THEN
      EXISTS_TAC `[]:holtype list` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  EQ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[pl_fun_ok] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `y:num`; `X:holtype`] FDTY_TAG_INV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:string` (X_CHOOSE_THEN `args:holtype list` SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[FDTY_TYAPP_INV] o
                check (fun th -> is_const_app "fdty" (concl th) &&
                                 can (find_term ((=) `TyApp n args`)) (concl th))) THEN
  MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `SND(SND(EL y (tys:(num#num#num)list)))`;
                `args:holtype list`] FDTYS_TAG_INV) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:holtype` (X_CHOOSE_THEN `r:holtype list` SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[FDTYS_CONS_INV] o
                check (fun th -> is_const_app "fdtys" (concl th) &&
                                 can (find_term ((=) `CONS (D:holtype) r`)) (concl th))) THEN
  MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`;
                `SND(SND(EL (SND(SND(EL y (tys:(num#num#num)list)))) tys))`; `r:holtype list`] FDTYS_TAG_INV) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:holtype` (X_CHOOSE_THEN `r':holtype list` SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[FDTYS_CONS_INV] o
                check (fun th -> is_const_app "fdtys" (concl th) &&
                                 can (find_term ((=) `CONS (C:holtype) r'`)) (concl th))) THEN
  SUBGOAL_THEN `r':holtype list = []` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FDTYS_FUN THEN MAP_EVERY EXISTS_TAC [`nms:string list`; `tys:(num#num#num)list`; `0`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`D:holtype`; `C:holtype`] THEN REWRITE_TAC[HFun; holtype_INJ] THEN
  ASM_MESON_TAC[]);;

let PL_FUN_DEC2 = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk y A B.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ fdty nms tys y (HFun A B)
     ==> pl_fun_ok tys y /\ fdty nms tys (pl_fun_dom tys y) A /\ fdty nms tys (pl_fun_cod tys y) B`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MP_TAC(MATCH_MP PL_FUN_DEC th)) THEN MESON_TAC[]);;
let PL_FUN_DEC3 = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk y X.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ fdty nms tys y X /\ pl_fun_ok tys y
     ==> ?A B. X = HFun A B /\ fdty nms tys (pl_fun_dom tys y) A /\ fdty nms tys (pl_fun_cod tys y) B`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MP_TAC(SPEC_ALL PL_FUN_DEC) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let pl_mk_guard_goal =
 `!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h1 h2.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
     ==> ((nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RMkComb h1 h2) /\
           ?f g a b tx ty.
             fddb nms tys dbs (SND(EL h1 ths))
               (hdbComb (hdbComb (hdbConst "=" (HFun (HFun tx ty) (HFun (HFun tx ty) HBool))) f) g) /\
             fddb nms tys dbs (SND(EL h2 ths))
               (hdbComb (hdbComb (hdbConst "=" (HFun tx (HFun tx HBool))) a) b)) <=>
          holr_live 3 h1 (LENGTH ths) drops /\ holr_live 3 h2 (LENGTH ths) drops /\
          pl_eq_ok dbs (SND(EL h1 ths)) /\ pl_eq_ok dbs (SND(EL h2 ths)) /\
          pl_fun_ok tys (pl_eq_ty dbs (SND(EL h1 ths))) /\
          pl_fun_ok tys (pl_fun_cod tys (pl_eq_ty dbs (SND(EL h1 ths)))) /\
          pl_fun_dom tys (pl_fun_cod tys (pl_eq_ty dbs (SND(EL h1 ths)))) =
            pl_fun_dom tys (pl_eq_ty dbs (SND(EL h1 ths))) /\
          pl_fun_cod tys (pl_fun_cod tys (pl_eq_ty dbs (SND(EL h1 ths)))) = 1 /\
          pl_fun_ok tys (pl_fun_dom tys (pl_eq_ty dbs (SND(EL h1 ths)))) /\
          pl_fun_ok tys (pl_eq_ty dbs (SND(EL h2 ths))) /\
          pl_fun_dom tys (pl_eq_ty dbs (SND(EL h2 ths))) =
            pl_fun_dom tys (pl_fun_dom tys (pl_eq_ty dbs (SND(EL h1 ths)))) /\
          pl_fun_ok tys (pl_fun_cod tys (pl_eq_ty dbs (SND(EL h2 ths)))) /\
          pl_fun_dom tys (pl_fun_cod tys (pl_eq_ty dbs (SND(EL h2 ths)))) =
            pl_fun_dom tys (pl_fun_dom tys (pl_eq_ty dbs (SND(EL h1 ths)))) /\
          pl_fun_cod tys (pl_fun_cod tys (pl_eq_ty dbs (SND(EL h2 ths)))) = 1)`;;

let PL_FUNDEC_TAC y x =
  MP_TAC(PL_SPEC [y; x] PL_FUN_DEC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC;;

let PL_CANON_TY_TAC x =
  FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
     (let _,b = strip_forall(concl th) in is_imp b && is_eq(rand b) &&
        is_conj(lhand b) && is_const_app "fdty" (lhand(lhand b))))) THEN
  EXISTS_TAC x THEN ASM_REWRITE_TAC[];;
let pl_t1 = `pl_eq_ty dbs (SND(EL h1 (ths:(num#num)list)))`
and pl_t2 = `pl_eq_ty dbs (SND(EL h2 (ths:(num#num)list)))`;;
let dom_t y = mk_comb(mk_comb(`pl_fun_dom`, `tys:(num#num#num)list`), y)
and cod_t y = mk_comb(mk_comb(`pl_fun_cod`, `tys:(num#num#num)list`), y);;
let PL_FD2_TAC y a b =
  MP_TAC(PL_SPEC [y; a; b] PL_FUN_DEC2) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC];;
let PL_FD3_TAC y x a b =
  MP_TAC(PL_SPEC [y; x] PL_FUN_DEC3) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN a (X_CHOOSE_THEN b STRIP_ASSUME_TAC));;
let PL_TYEQ_TAC x y row =
  MATCH_MP_TAC FDTY_FUN THEN MAP_EVERY EXISTS_TAC [`nms:string list`; `tys:(num#num#num)list`; row] THEN
  ASM_REWRITE_TAC[];;
let PL_MK_GUARDS = prove(pl_mk_guard_goal,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nat_ops_live; holr_operands; ALL; FST; SND] THEN
  ASM_CASES_TAC `holr_live 3 h1 (LENGTH (ths:(num#num)list)) drops` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `holr_live 3 h2 (LENGTH (ths:(num#num)list)) drops` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `h1 < LENGTH (ths:(num#num)list) /\ h2 < LENGTH ths` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[holr_live]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_BOOL) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_CANON) THEN
  MP_TAC(PL_SPEC [`h1:num`] PL_THM_DEC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `C1:hdbterm`) (K ALL_TAC)) THEN
  MP_TAC(PL_SPEC [`h2:num`] PL_THM_DEC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `C2:hdbterm`) (K ALL_TAC)) THEN
  MP_TAC(PL_SPEC [`SND(EL h1 (ths:(num#num)list))`; `C1:hdbterm`] PL_EQ_DEC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "E1") (LABEL_TAC "D1")) THEN
  MP_TAC(PL_SPEC [`SND(EL h2 (ths:(num#num)list))`; `C2:hdbterm`] PL_EQ_DEC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "E2") (LABEL_TAC "D2")) THEN
  EQ_TAC THENL
   [(DISCH_THEN(X_CHOOSE_THEN `f:hdbterm` (X_CHOOSE_THEN `g:hdbterm` (X_CHOOSE_THEN `a:hdbterm`
     (X_CHOOSE_THEN `b:hdbterm` (X_CHOOSE_THEN `tx:holtype` (X_CHOOSE_THEN `ty:holtype` STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `C1 = hdbComb (hdbComb (hdbConst "=" (HFun (HFun tx ty) (HFun (HFun tx ty) HBool))) f) g /\
                C2 = hdbComb (hdbComb (hdbConst "=" (HFun tx (HFun tx HBool))) a) b` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FDDB_FUN]; ALL_TAC] THEN
  USE_THEN "E1" (fun th -> REWRITE_TAC[GSYM th]) THEN USE_THEN "E2" (fun th -> REWRITE_TAC[GSYM th]) THEN
    USE_THEN "D1" (STRIP_ASSUME_TAC o C MP
     (ASSUME `C1 = hdbComb (hdbComb (hdbConst "=" (HFun (HFun tx ty) (HFun (HFun tx ty) HBool))) f) g`) o
     SPECL [`HFun (HFun tx ty) (HFun (HFun tx ty) HBool)`; `f:hdbterm`; `g:hdbterm`]) THEN
  USE_THEN "D2" (STRIP_ASSUME_TAC o C MP
     (ASSUME `C2 = hdbComb (hdbComb (hdbConst "=" (HFun tx (HFun tx HBool))) a) b`) o
     SPECL [`HFun tx (HFun tx HBool)`; `a:hdbterm`; `b:hdbterm`]) THEN
  PL_FD2_TAC pl_t1 `HFun tx ty` `HFun (HFun tx ty) HBool` THEN
  PL_FD2_TAC (cod_t pl_t1) `HFun tx ty` `HBool` THEN
  PL_FD2_TAC (dom_t pl_t1) `tx:holtype` `ty:holtype` THEN
  PL_FD2_TAC pl_t2 `tx:holtype` `HFun tx HBool` THEN
  PL_FD2_TAC (cod_t pl_t2) `tx:holtype` `HBool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[]; ASM_MESON_TAC[];
    PL_CANON_TY_TAC `HFun tx ty`; PL_CANON_TY_TAC `HBool`; PL_CANON_TY_TAC `tx:holtype`;
    PL_CANON_TY_TAC `tx:holtype`; PL_CANON_TY_TAC `HBool`]);
    (STRIP_TAC THEN
  USE_THEN "E1" (fun th -> MP_TAC(EQ_MP (SYM th) (ASSUME `pl_eq_ok dbs (SND(EL h1 (ths:(num#num)list)))`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `TY1:holtype` (X_CHOOSE_THEN `f:hdbterm` (X_CHOOSE_THEN `g:hdbterm` ASSUME_TAC))) THEN
  USE_THEN "D1" (STRIP_ASSUME_TAC o C MP (ASSUME `C1 = hdbComb (hdbComb (hdbConst "=" TY1) f) g`) o
                 SPECL [`TY1:holtype`; `f:hdbterm`; `g:hdbterm`]) THEN
  USE_THEN "E2" (fun th -> MP_TAC(EQ_MP (SYM th) (ASSUME `pl_eq_ok dbs (SND(EL h2 (ths:(num#num)list)))`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `TY2:holtype` (X_CHOOSE_THEN `a:hdbterm` (X_CHOOSE_THEN `b:hdbterm` ASSUME_TAC))) THEN
  USE_THEN "D2" (STRIP_ASSUME_TAC o C MP (ASSUME `C2 = hdbComb (hdbComb (hdbConst "=" TY2) a) b`) o
                 SPECL [`TY2:holtype`; `a:hdbterm`; `b:hdbterm`]) THEN
  PL_FD3_TAC pl_t1 `TY1:holtype` `A1:holtype` `B1:holtype` THEN
  PL_FD3_TAC (cod_t pl_t1) `B1:holtype` `A2:holtype` `B2:holtype` THEN
  PL_FD3_TAC (dom_t pl_t1) `A1:holtype` `tx:holtype` `ty:holtype` THEN
  PL_FD3_TAC pl_t2 `TY2:holtype` `E1:holtype` `R2:holtype` THEN
  PL_FD3_TAC (cod_t pl_t2) `R2:holtype` `E3:holtype` `B3:holtype` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME (mk_eq(dom_t (cod_t pl_t1), dom_t pl_t1));
                              ASSUME (mk_eq(cod_t (cod_t pl_t1), `1`));
                              ASSUME (mk_eq(dom_t pl_t2, dom_t (dom_t pl_t1)));
                              ASSUME (mk_eq(dom_t (cod_t pl_t2), dom_t (dom_t pl_t1)));
                              ASSUME (mk_eq(cod_t (cod_t pl_t2), `1`))]) THEN
  SUBGOAL_THEN `A2:holtype = A1 /\ B2 = HBool /\ (E1:holtype) = tx /\ (E3:holtype) = tx /\ B3 = HBool` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [PL_TYEQ_TAC `A2:holtype` `A1:holtype` (dom_t pl_t1);
      PL_TYEQ_TAC `B2:holtype` `HBool` `1`;
      PL_TYEQ_TAC `E1:holtype` `tx:holtype` (dom_t (dom_t pl_t1));
      PL_TYEQ_TAC `E3:holtype` `tx:holtype` (dom_t (dom_t pl_t1));
      PL_TYEQ_TAC `B3:holtype` `HBool` `1`];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`f:hdbterm`; `g:hdbterm`; `a:hdbterm`; `b:hdbterm`; `tx:holtype`; `ty:holtype`] THEN
  REPEAT(FIRST_X_ASSUM(fun th -> let c = concl th in
    if is_eq c && is_var(lhs c) && mem (fst(dest_var(lhs c))) ["TY1";"TY2";"A1";"B1";"A2";"B2";"E1";"R2";"E3";"B3";"C1";"C2"]
    then SUBST_ALL_TAC th else failwith "")) THEN
  ASM_REWRITE_TAC[])]);;

let pl_fr = `pl_fun_cod tys (pl_fun_dom tys (pl_eq_ty dbs (SND(EL h1 (ths:(num#num)list)))))`;;
let lhs1 = `pl_eq_lhs dbs (SND(EL h1 (ths:(num#num)list)))` and lhs2 = `pl_eq_lhs dbs (SND(EL h2 (ths:(num#num)list)))`
and rhs1 = `pl_eq_rhs dbs (SND(EL h1 (ths:(num#num)list)))` and rhs2 = `pl_eq_rhs dbs (SND(EL h2 (ths:(num#num)list)))`;;
let PL_DBB_TAC row t =
  SUBGOAL_THEN (mk_comb(mk_comb(`(<):num->num->bool`, row), `LENGTH (dbs:(num#num#num)list)`)) ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1(SPEC_ALL FDDB_BOUND)) THEN EXISTS_TAC t THEN ASM_REWRITE_TAC[]; ALL_TAC];;
let PL_TY_STEP_TAC2 tys dbs key pay mt ok_tac =
  MP_TAC(ISPECL [`ctx:hupdate list`; `nms:string list`; tys; dbs; key; pay; mt] PL_TY_STEP) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      REWRITE_TAC[ty_key_ok; ARITH_EQ; LENGTH_APPEND] THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN
      ASM_ARITH_TAC;
      ok_tac];
    ALL_TAC] THEN
  STRIP_TAC;;
let MK_D2 = `APPEND (APPEND (dbs:(num#num#num)list) md1) md2`;;
let MK_D3 = `APPEND (APPEND (APPEND (dbs:(num#num#num)list) md1) md2) md3`
and MK_D4 = `APPEND (APPEND (APPEND (APPEND (dbs:(num#num#num)list) md1) md2) md3) md4`;;
let is_bound_fact c =
  try let op,args = strip_comb c in
      let n = fst(dest_const op) in (n = "<" || n = "<=") && length args = 2
  with Failure _ -> false;;
let PL_BOUND_ARITH_TAC =
  REWRITE_TAC[LENGTH_APPEND] THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_bound_fact(concl th) then MP_TAC(REWRITE_RULE[LENGTH_APPEND] th)
                                 else failwith "")) THEN
  ARITH_TAC;;
let PL_DB_STEP_TAC2 tys dbs key pay md ok_tac =
  MP_TAC(ISPECL [`ctx:hupdate list`; `nms:string list`; tys; dbs; key; pay; md] PL_DB_STEP) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      REWRITE_TAC[db_key_ok; ARITH_EQ] THEN PL_BOUND_ARITH_TAC;
      ok_tac];
    ALL_TAC] THEN
  STRIP_TAC;;
let PL_EXT_TAC =
  let e1 = CONJUNCT1(SPEC_ALL PL_FDTY_APPEND) and e2 = CONJUNCT2(SPEC_ALL PL_FDTY_APPEND)
  and d1 = CONJUNCT1(SPEC_ALL PL_FDDB_APPEND) and d2 = CONJUNCT2(SPEC_ALL PL_FDDB_APPEND)
  and t1 = CONJUNCT1(SPEC_ALL PL_FDDB_TYS_APPEND) and t2 = CONJUNCT2(SPEC_ALL PL_FDDB_TYS_APPEND) in
  let rec tac g =
    (FIRST_ASSUM ACCEPT_TAC ORELSE
     (MATCH_MP_TAC e1 THEN tac) ORELSE (MATCH_MP_TAC e2 THEN tac) ORELSE
     (MATCH_MP_TAC d1 THEN tac) ORELSE (MATCH_MP_TAC d2 THEN tac) ORELSE
     (MATCH_MP_TAC t1 THEN tac) ORELSE (MATCH_MP_TAC t2 THEN tac)) g in
  tac;;
let PL_DBOK_TAC dec rule exs =
  DISJ1_TAC THEN EXISTS_TAC dec THEN MATCH_MP_TAC rule THEN MAP_EVERY EXISTS_TAC exs THEN
  REWRITE_TAC[PL_EL_SNOC] THEN REPEAT CONJ_TAC THEN (PL_EXT_TAC ORELSE PL_BOUND_ARITH_TAC);;
let PL_DBDEC_TAC rule exs =
  MATCH_MP_TAC rule THEN MAP_EVERY EXISTS_TAC exs THEN REPEAT CONJ_TAC THEN (PL_EXT_TAC ORELSE PL_BOUND_ARITH_TAC);;
let MK_D5 = `APPEND (APPEND (APPEND (APPEND (APPEND (dbs:(num#num#num)list) md1) md2) md3) md4) md5`;;
let PL_IDS_UP_TAC = REPEAT(MATCH_MP_TAC PL_IDS_APPEND) THEN ASM_REWRITE_TAC[];;
let pl_mk_fired_goal =
 `!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h1 h2 fa gb l1 f1 l2 l3 e q x k
   md1 md2 mt1 mt2 mt3 mt4 mt5 md3 md4 md5 md6 hk cw'.
   pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
   holr_live 3 h1 (LENGTH ths) drops /\ holr_live 3 h2 (LENGTH ths) drops /\
   pl_eq_ok dbs (SND(EL h1 ths)) /\ pl_eq_ok dbs (SND(EL h2 ths)) /\
   pl_fun_ok tys (pl_eq_ty dbs (SND(EL h1 ths))) /\
   pl_fun_ok tys (pl_fun_cod tys (pl_eq_ty dbs (SND(EL h1 ths)))) /\
   pl_fun_dom tys (pl_fun_cod tys (pl_eq_ty dbs (SND(EL h1 ths)))) =
     pl_fun_dom tys (pl_eq_ty dbs (SND(EL h1 ths))) /\
   pl_fun_cod tys (pl_fun_cod tys (pl_eq_ty dbs (SND(EL h1 ths)))) = 1 /\
   pl_fun_ok tys (pl_fun_dom tys (pl_eq_ty dbs (SND(EL h1 ths)))) /\
   pl_fun_ok tys (pl_eq_ty dbs (SND(EL h2 ths))) /\
   pl_fun_dom tys (pl_eq_ty dbs (SND(EL h2 ths))) =
     pl_fun_dom tys (pl_fun_dom tys (pl_eq_ty dbs (SND(EL h1 ths)))) /\
   pl_fun_ok tys (pl_fun_cod tys (pl_eq_ty dbs (SND(EL h2 ths)))) /\
   pl_fun_dom tys (pl_fun_cod tys (pl_eq_ty dbs (SND(EL h2 ths)))) =
     pl_fun_dom tys (pl_fun_dom tys (pl_eq_ty dbs (SND(EL h1 ths)))) /\
   pl_fun_cod tys (pl_fun_cod tys (pl_eq_ty dbs (SND(EL h2 ths)))) = 1 /\
   pl_interned dbs (3,pl_eq_lhs dbs (SND(EL h1 ths)),pl_eq_lhs dbs (SND(EL h2 ths))) fa md1 /\
   pl_interned (APPEND dbs md1) (3,pl_eq_rhs dbs (SND(EL h1 ths)),pl_eq_rhs dbs (SND(EL h2 ths))) gb md2 /\
   pl_interned tys (3,pl_fun_cod tys (pl_fun_dom tys (pl_eq_ty dbs (SND(EL h1 ths)))),3) l1 mt1 /\
   pl_interned (APPEND tys mt1) (1,1,l1) f1 mt2 /\
   pl_interned (APPEND (APPEND tys mt1) mt2) (3,f1,0) l2 mt3 /\
   pl_interned (APPEND (APPEND (APPEND tys mt1) mt2) mt3)
     (3,pl_fun_cod tys (pl_fun_dom tys (pl_eq_ty dbs (SND(EL h1 ths)))),l2) l3 mt4 /\
   pl_interned (APPEND (APPEND (APPEND (APPEND tys mt1) mt2) mt3) mt4) (1,1,l3) e mt5 /\
   pl_interned (APPEND (APPEND dbs md1) md2) (2,2,e) q md3 /\
   pl_interned (APPEND (APPEND (APPEND dbs md1) md2) md3) (3,q,fa) x md4 /\
   pl_interned (APPEND (APPEND (APPEND (APPEND dbs md1) md2) md3) md4) (3,x,gb) k md5 /\
   (keys_distinct (APPEND (APPEND (APPEND (APPEND (APPEND dbs md1) md2) md3) md4) md5)
    ==> keys_distinct (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND dbs md1) md2) md3) md4) md5) md6)) /\
   LENGTH (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND dbs md1) md2) md3) md4) md5) md6) < 2 EXP 60 /\
   (!I1 I2. pl_ids (APPEND (APPEND (APPEND (APPEND (APPEND dbs md1) md2) md3) md4) md5) (FST(EL h1 ths)) I1 /\
            pl_ids (APPEND (APPEND (APPEND (APPEND (APPEND dbs md1) md2) md3) md4) md5) (FST(EL h2 ths)) I2 /\
            PAIRWISE (<) I1 /\ PAIRWISE (<) I2
            ==> (?ids. pl_ids (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND dbs md1) md2) md3) md4) md5) md6) hk ids /\
                       PAIRWISE (<) ids /\ (!x. MEM x ids <=> MEM x I1 \/ MEM x I2)) /\
                pl_cells_new 6 (LENGTH (APPEND (APPEND (APPEND (APPEND (APPEND dbs md1) md2) md3) md4) md5))
                  (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND dbs md1) md2) md3) md4) md5) md6)
                  (\a. MEM a I1 \/ MEM a I2)) /\
   LENGTH ths + 1 < 2 EXP 60 /\ (!n. n <= 6 ==> cw' n = cw n)
   ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RMkComb h1 h2)
         (ctx,nms,APPEND (APPEND (APPEND (APPEND (APPEND tys mt1) mt2) mt3) mt4) mt5,ntms,
          APPEND (APPEND (APPEND (APPEND (APPEND (APPEND dbs md1) md2) md3) md4) md5) md6,
          APPEND ths [(hk,k)],nmap,ymap,drops,pol) /\
       pl_inv (cw',(ctx,nms,APPEND (APPEND (APPEND (APPEND (APPEND tys mt1) mt2) mt3) mt4) mt5,ntms,
                    APPEND (APPEND (APPEND (APPEND (APPEND (APPEND dbs md1) md2) md3) md4) md5) md6,
                    APPEND ths [(hk,k)],nmap,ymap,drops,pol),stk)`;;
let PL_MKCOMB_FIRED = prove(pl_mk_fired_goal,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `h1 < LENGTH (ths:(num#num)list) /\ h2 < LENGTH ths` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[holr_live]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_NAMES_INJ) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_CANON) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_STD_SIG) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_TABS_OK) THEN
  FIRST_ASSUM(fun th -> if is_const_app "pl_tabs_ok" (concl th)
                        then STRIP_ASSUME_TAC(REWRITE_RULE[pl_tabs_ok] th) else failwith "") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_BOOT_LISTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_BOOL) THEN
  PL_INV_FACTS_TAC THEN
  MP_TAC(PL_SPEC [`h1:num`] PL_THM_DEC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `C1:hdbterm`) (X_CHOOSE_TAC `hs1:hdbterm list`)) THEN
  MP_TAC(PL_SPEC [`h2:num`] PL_THM_DEC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `C2:hdbterm`) (X_CHOOSE_TAC `hs2:hdbterm list`)) THEN
  MP_TAC(PL_SPEC [`h1:num`; `h2:num`] PL_MK_GUARDS) THEN ASM_REWRITE_TAC[nat_ops_live; holr_operands; ALL; FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:hdbterm` (X_CHOOSE_THEN `g:hdbterm` (X_CHOOSE_THEN `a:hdbterm`
     (X_CHOOSE_THEN `b:hdbterm` (X_CHOOSE_THEN `tx:holtype` (X_CHOOSE_THEN `ty:holtype` STRIP_ASSUME_TAC))))))) THEN
  (MP_TAC(PL_SPEC [`SND(EL h1 (ths:(num#num)list))`;
                  `hdbComb (hdbComb (hdbConst "=" (HFun (HFun tx ty) (HFun (HFun tx ty) HBool))) f) g`] PL_EQ_DEC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`HFun (HFun tx ty) (HFun (HFun tx ty) HBool)`; `f:hdbterm`; `g:hdbterm`] o CONJUNCT2) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(PL_SPEC [`SND(EL h2 (ths:(num#num)list))`;
                  `hdbComb (hdbComb (hdbConst "=" (HFun tx (HFun tx HBool))) a) b`] PL_EQ_DEC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`HFun tx (HFun tx HBool)`; `a:hdbterm`; `b:hdbterm`] o CONJUNCT2) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  PL_FD2_TAC pl_t1 `HFun tx ty` `HFun (HFun tx ty) HBool` THEN
  PL_FD2_TAC (dom_t pl_t1) `tx:holtype` `ty:holtype` THEN
  SUBGOAL_THEN (mk_comb(mk_comb(`(<):num->num->bool`, pl_fr), `LENGTH (tys:(num#num#num)list)`)) ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1(SPEC_ALL FDTY_BOUND)) THEN EXISTS_TAC `ty:holtype` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `htype_ok (FST(hsigof ctx)) ty` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[fibre_ty_ok] o
                C MP (ASSUME (mk_comb(mk_comb(`(<):num->num->bool`, pl_fr), `LENGTH (tys:(num#num#num)list)`))) o
                SPEC pl_fr o
                check (fun th -> is_forall(concl th) && can (find_term ((=) `fibre_ty_ok`)) (concl th))) THEN
    STRIP_TAC THENL
     [SUBGOAL_THEN `ty':holtype = ty` (fun th -> ASM_MESON_TAC[th]) THEN
      MATCH_MP_TAC FDTY_FUN THEN MAP_EVERY EXISTS_TAC [`nms:string list`; `tys:(num#num#num)list`; pl_fr] THEN
      ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; pl_fr; `ty:holtype`; `l:holtype list`]
                   FDTY_NOT_BOTH) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPEC `hsigof ctx` HTYPE_OK_STD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC) THEN
  (PL_DBB_TAC lhs1 `f:hdbterm` THEN PL_DBB_TAC lhs2 `a:hdbterm` THEN
  PL_DBB_TAC rhs1 `g:hdbterm` THEN PL_DBB_TAC rhs2 `b:hdbterm`) THEN
  (PL_DB_STEP_TAC `tys:(num#num#num)list` `dbs:(num#num#num)list`
    `(3,pl_eq_lhs dbs (SND(EL h1 (ths:(num#num)list))),pl_eq_lhs dbs (SND(EL h2 (ths:(num#num)list))))`
    `fa:num` `md1:(num#num#num)list`
    (PL_DBOK_TAC `hdbComb f a` FDDB_COMB [lhs1; lhs2])) THEN
  (SUBGOAL_THEN `fddb nms tys (APPEND (dbs:(num#num#num)list) md1) fa (hdbComb f a)` ASSUME_TAC THENL
   [PL_DBDEC_TAC FDDB_COMB [lhs1; lhs2]; ALL_TAC]) THEN
  (PL_DB_STEP_TAC `tys:(num#num#num)list` `APPEND (dbs:(num#num#num)list) md1`
    `(3,pl_eq_rhs dbs (SND(EL h1 (ths:(num#num)list))),pl_eq_rhs dbs (SND(EL h2 (ths:(num#num)list))))`
    `gb:num` `md2:(num#num#num)list`
    (PL_DBOK_TAC `hdbComb g b` FDDB_COMB [rhs1; rhs2])) THEN
  (SUBGOAL_THEN `fddb nms tys (APPEND (APPEND (dbs:(num#num#num)list) md1) md2) gb (hdbComb g b)` ASSUME_TAC THENL
   [PL_DBDEC_TAC FDDB_COMB [rhs1; rhs2]; ALL_TAC]) THEN
  (PL_TY_STEP_TAC2 PL_TAB0 MK_D2 `(3,pl_fun_cod tys (pl_fun_dom tys (pl_eq_ty dbs (SND(EL h1 (ths:(num#num)list))))),3)`
    `l1:num` `mt1:(num#num#num)list` (PL_CONS_OK_TAC pl_fr `3` `[ty:holtype; HBool]`)) THEN
  (SUBGOAL_THEN `fdtys nms (APPEND (tys:(num#num#num)list) mt1) l1 [ty:holtype; HBool]` ASSUME_TAC THENL
   [PL_DEC_CONS_TAC pl_fr `3`; ALL_TAC]) THEN
  (PL_TY_STEP_TAC2 PL_TAB1 MK_D2 `(1,1,l1:num)` `f1:num` `mt2:(num#num#num)list`
    (PL_FUN_OK_TAC `l1:num` `[ty:holtype; HBool]`)) THEN
  (SUBGOAL_THEN `fdty nms (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) f1 (TyApp (EL 1 nms) [ty:holtype; HBool])`
    ASSUME_TAC THENL [PL_DEC_FUN_TAC `l1:num`; ALL_TAC]) THEN
  (PL_TY_STEP_TAC2 PL_TAB2 MK_D2 `(3,f1:num,0)` `l2:num` `mt3:(num#num#num)list`
    (PL_CONS_OK_TAC `f1:num` `0` `[TyApp (EL 1 nms) [ty:holtype; HBool]]`)) THEN
  (SUBGOAL_THEN `fdtys nms (APPEND (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) mt3) l2
                      [TyApp (EL 1 nms) [ty:holtype; HBool]]` ASSUME_TAC THENL
   [PL_DEC_CONS_TAC `f1:num` `0`; ALL_TAC]) THEN
  (PL_TY_STEP_TAC2 PL_TAB3 MK_D2 `(3,pl_fun_cod tys (pl_fun_dom tys (pl_eq_ty dbs (SND(EL h1 (ths:(num#num)list))))),l2:num)`
    `l3:num` `mt4:(num#num#num)list`
    (PL_CONS_OK_TAC pl_fr `l2:num` `[ty:holtype; TyApp (EL 1 nms) [ty; HBool]]`)) THEN
  (SUBGOAL_THEN `fdtys nms (APPEND (APPEND (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) mt3) mt4) l3
                      [ty:holtype; TyApp (EL 1 nms) [ty; HBool]]` ASSUME_TAC THENL
   [PL_DEC_CONS_TAC pl_fr `l2:num`; ALL_TAC]) THEN
  (PL_TY_STEP_TAC2 PL_TAB4 MK_D2 `(1,1,l3:num)` `e:num` `mt5:(num#num#num)list`
    (PL_FUN_OK_TAC `l3:num` `[ty:holtype; TyApp (EL 1 nms) [ty; HBool]]`)) THEN
  (SUBGOAL_THEN `fdty nms (APPEND (APPEND (APPEND (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) mt3) mt4) mt5) e
                     (TyApp (EL 1 nms) [ty:holtype; TyApp (EL 1 nms) [ty; HBool]])` ASSUME_TAC THENL
   [PL_DEC_FUN_TAC `l3:num`; ALL_TAC]) THEN
  (PL_DB_STEP_TAC PL_TAB5 MK_D2 `(2,2,e:num)` `q:num` `md3:(num#num#num)list`
    (PL_DBOK_TAC `hdbConst (EL 2 nms) (TyApp (EL 1 nms) [ty:holtype; TyApp (EL 1 nms) [ty; HBool]])`
                 FDDB_CONST [`e:num`])) THEN
  (SUBGOAL_THEN `fddb nms (APPEND (APPEND (APPEND (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) mt3) mt4) mt5)
                     (APPEND (APPEND (APPEND (dbs:(num#num#num)list) md1) md2) md3) q
                     (hdbConst (EL 2 nms) (TyApp (EL 1 nms) [ty:holtype; TyApp (EL 1 nms) [ty; HBool]]))`
    ASSUME_TAC THENL [PL_DBDEC_TAC FDDB_CONST [`e:num`]; ALL_TAC]) THEN
  (PL_DB_STEP_TAC2 PL_TAB5 MK_D3 `(3,q:num,fa:num)` `x:num` `md4:(num#num#num)list`
    (PL_DBOK_TAC `hdbComb (hdbConst (EL 2 nms) (TyApp (EL 1 nms) [ty:holtype; TyApp (EL 1 nms) [ty; HBool]])) (hdbComb f a)`
                 FDDB_COMB [`q:num`; `fa:num`])) THEN
  (SUBGOAL_THEN `fddb nms (APPEND (APPEND (APPEND (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) mt3) mt4) mt5)
                     (APPEND (APPEND (APPEND (APPEND (dbs:(num#num#num)list) md1) md2) md3) md4) x
                     (hdbComb (hdbConst (EL 2 nms) (TyApp (EL 1 nms) [ty:holtype; TyApp (EL 1 nms) [ty; HBool]])) (hdbComb f a))`
    ASSUME_TAC THENL [PL_DBDEC_TAC FDDB_COMB [`q:num`; `fa:num`]; ALL_TAC]) THEN
  (PL_DB_STEP_TAC2 PL_TAB5 MK_D4 `(3,x:num,gb:num)` `k:num` `md5:(num#num#num)list`
    (PL_DBOK_TAC `hdbComb (hdbComb (hdbConst (EL 2 nms) (TyApp (EL 1 nms) [ty:holtype; TyApp (EL 1 nms) [ty; HBool]])) (hdbComb f a)) (hdbComb g b)`
                 FDDB_COMB [`x:num`; `gb:num`])) THEN
  (SUBGOAL_THEN `fddb nms (APPEND (APPEND (APPEND (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) mt3) mt4) mt5)
                     (APPEND (APPEND (APPEND (APPEND (APPEND (dbs:(num#num#num)list) md1) md2) md3) md4) md5) k
                     (hdbComb (hdbComb (hdbConst (EL 2 nms) (TyApp (EL 1 nms) [ty:holtype; TyApp (EL 1 nms) [ty; HBool]])) (hdbComb f a)) (hdbComb g b))`
    ASSUME_TAC THENL [PL_DBDEC_TAC FDDB_COMB [`x:num`; `gb:num`]; ALL_TAC]) THEN
  (FIRST_ASSUM(fun th -> if is_const_app "pl_tabs_ok" (concl th) &&
                           can (find_term ((=) `md5:(num#num#num)list`)) (concl th)
                        then STRIP_ASSUME_TAC(REWRITE_RULE[pl_tabs_ok] th) else failwith "")) THEN
  (SUBGOAL_THEN `?I1. pl_ids dbs (FST(EL h1 (ths:(num#num)list))) I1 /\ PAIRWISE (<) I1`
    (X_CHOOSE_THEN `I1:num list` STRIP_ASSUME_TAC) THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  (SUBGOAL_THEN `?I2. pl_ids dbs (FST(EL h2 (ths:(num#num)list))) I2 /\ PAIRWISE (<) I2`
    (X_CHOOSE_THEN `I2:num list` STRIP_ASSUME_TAC) THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  (FIRST_X_ASSUM(MP_TAC o SPECL [`I1:num list`; `I2:num list`] o
                check (fun th -> is_forall(concl th) && can (find_term ((=) `pl_cells_new`)) (concl th)))) THEN
  (SUBGOAL_THEN `pl_ids (APPEND (APPEND (APPEND (APPEND (APPEND (dbs:(num#num#num)list) md1) md2) md3) md4) md5)
                       (FST(EL h1 (ths:(num#num)list))) I1 /\
                pl_ids (APPEND (APPEND (APPEND (APPEND (APPEND (dbs:(num#num#num)list) md1) md2) md3) md4) md5)
                       (FST(EL h2 (ths:(num#num)list))) I2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN PL_IDS_UP_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `ids:num list` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  MP_TAC(ISPECL [`nms:string list`; PL_TAB5; MK_D5; `md6:(num#num#num)list`;
                 `FST(EL h1 (ths:(num#num)list))`; `FST(EL h2 (ths:(num#num)list))`; `hk:num`;
                 `I1:num list`; `I2:num list`; `hs1:hdbterm list`; `hs2:hdbterm list`] PL_UNION_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [PL_EXT_TAC; PL_EXT_TAC; EXISTS_TAC `ids:num list` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `hs:hdbterm list` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `keys_distinct (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (dbs:(num#num#num)list) md1) md2) md3) md4) md5) md6)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC]) THEN
  (SUBGOAL_THEN `fddb nms (APPEND (APPEND (APPEND (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) mt3) mt4) mt5)
                     (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (dbs:(num#num#num)list) md1) md2) md3) md4) md5) md6) k
                     (hdbComb (hdbComb (hdbConst "=" (HFun ty (HFun ty HBool))) (hdbComb f a)) (hdbComb g b))`
    ASSUME_TAC THENL
   [SUBGOAL_THEN `hdbComb (hdbComb (hdbConst "=" (HFun ty (HFun ty HBool))) (hdbComb f a)) (hdbComb g b) =
                  hdbComb (hdbComb (hdbConst (EL 2 nms) (TyApp (EL 1 nms) [ty:holtype; TyApp (EL 1 nms) [ty; HBool]]))
                                   (hdbComb f a)) (hdbComb g b)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[HFun]; PL_EXT_TAC];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RMkComb h1 h2)
     (ctx,nms,APPEND (APPEND (APPEND (APPEND (APPEND tys mt1) mt2) mt3) mt4) mt5,ntms,
      APPEND (APPEND (APPEND (APPEND (APPEND (APPEND dbs md1) md2) md3) md4) md5) md6,
      APPEND ths [(hk,k)],nmap,ymap,drops,pol)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                  `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                  `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `h1:num`; `h2:num`;
                  `hs1:hdbterm list`; `hs2:hdbterm list`; `f:hdbterm`; `g:hdbterm`; `a:hdbterm`; `b:hdbterm`;
                  `tx:holtype`; `ty:holtype`;
                  `APPEND mt1 (APPEND mt2 (APPEND mt3 (APPEND mt4 mt5))):(num#num#num)list`;
                  `APPEND md1 (APPEND md2 (APPEND md3 (APPEND md4 (APPEND md5 md6)))):(num#num#num)list`;
                  `hk:num`; `k:num`; `hs:hdbterm list`] NAT_STEP_MKCOMB) THEN
    REWRITE_TAC[APPEND_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[nat_ops_live; holr_operands; ALL; FST; SND] THEN REPEAT CONJ_TAC THENL
     [PL_TYS_OK_TAC;
      MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
                    `APPEND mt1 (APPEND mt2 (APPEND mt3 (APPEND mt4 mt5))):(num#num#num)list`;
                    `APPEND md1 (APPEND md2 (APPEND md3 (APPEND md4 (APPEND md5 md6)))):(num#num#num)list`]
                   NAT_KEYS_NEW_ROWS) THEN
      REWRITE_TAC[APPEND_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM LENGTH_APPEND; GSYM APPEND_ASSOC] THEN REWRITE_TAC[APPEND_ASSOC] THEN
      X_GEN_TAC `kk:num` THEN STRIP_TAC THEN
      ASM_CASES_TAC `kk < LENGTH (APPEND (APPEND (APPEND (APPEND (APPEND (dbs:(num#num#num)list) md1) md2) md3) md4) md5)` THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `kk:num` o check (fun th -> is_forall(concl th) &&
           (let _,b = strip_forall(concl th) in is_imp b && is_disj(rand b)) &&
           can (find_term ((=) `md5:(num#num#num)list`)) (concl th) &&
           not(can (find_term ((=) `md6:(num#num#num)list`)) (concl th)))) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
         [DISJ1_TAC THEN EXISTS_TAC `t:hdbterm` THEN PL_EXT_TAC;
          DISJ2_TAC THEN EXISTS_TAC `l:hdbterm list` THEN PL_EXT_TAC];
        DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN
        REWRITE_TAC[LENGTH_APPEND] THEN ASM_ARITH_TAC]];
    ALL_TAC]) THEN
  (ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`;
                `cw':num->num`; `RMkComb h1 h2`;
                `APPEND mt1 (APPEND mt2 (APPEND mt3 (APPEND mt4 mt5))):(num#num#num)list`;
                `APPEND md1 (APPEND md2 (APPEND md3 (APPEND md4 (APPEND md5 md6)))):(num#num#num)list`;
                `hk:num`; `k:num`] PL_INV_THM_STEP) THEN
  REWRITE_TAC[APPEND_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM LENGTH_APPEND; GSYM APPEND_ASSOC] THEN REWRITE_TAC[APPEND_ASSOC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(PL_BOUND_ARITH_TAC THEN NO_TAC) THEN
  EXISTS_TAC `ids:num list` THEN ASM_REWRITE_TAC[]));;

(* The FIRED closing, reading function-type rows too. *)
let PL_FIRED_TAC th =
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_EQ]) THEN
  MATCH_MP_TAC(REWRITE_RULE[pl_eq_rhs; pl_eq_lhs; pl_eq_ty; pl_fun_dom; pl_fun_cod] th) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  PL_WITNESS_TAC THEN ASM_REWRITE_TAC[pl_eq_ok; pl_fun_ok] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_ARITH_TAC THEN NO_TAC) THEN
  TRY(PL_WITNESS_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN TRY PL_SET_LOW_TAC;;

let pl_mkcomb_goal =
 `!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h1 h2 k i cw' ns' stk'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ cw 8 = h1 /\ cw 9 = h2 /\
     pl_run pl_plan_mkcomb 0 (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) (k,i,(cw',ns',stk'))
     ==> (k = 1 ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RMkComb h1 h2) ns' /\
                    pl_inv (cw',ns',stk')) /\
         (k = 0 <=> ~(nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RMkComb h1 h2) /\
                      ?f g a b tx ty.
                        fddb nms tys dbs (SND(EL h1 ths))
                          (hdbComb (hdbComb (hdbConst "=" (HFun (HFun tx ty) (HFun (HFun tx ty) HBool))) f) g) /\
                        fddb nms tys dbs (SND(EL h2 ths))
                          (hdbComb (hdbComb (hdbConst "=" (HFun tx (HFun tx HBool))) a) b)))`;;

(* PL_MKCOMB: the plan's FIRED run is MK_COMB's nat_step and keeps pl_inv;  *)
(* it is REFUSED exactly when an operand is not live, a conclusion is not   *)
(* an equation, or the two equality constants are not typed                 *)
(* (tx->ty)->(tx->ty)->bool and tx->tx->bool for some tx and ty.            *)
let PL_MKCOMB = prove(pl_mkcomb_goal,
  PL_START_TAC pl_plan_mkcomb THEN
  PL_INV_ASM(fun th -> REWRITE_TAC[MATCH_MP PL_MK_GUARDS th]) THEN
  REWRITE_TAC[ARITH_EQ; pl_eq_ok; pl_eq_lhs; pl_eq_rhs; pl_eq_ty; pl_fun_ok; pl_fun_dom; pl_fun_cod] THEN
  ASM_REWRITE_TAC[] THEN TRY(ASM_ARITH_TAC THEN NO_TAC) THEN PL_FIRED_TAC PL_MKCOMB_FIRED);;

(* ========================================================================= *)
(* Whole-image theorems, generated from the emitter's record of an image:    *)
(* the program, its bytes, and its spans (offset, length, template, and the  *)
(* path of the statement each span realizes).                                *)
(*                                                                           *)
(* The generator proves every template instance, with the facts of its       *)
(* program point, and joins them up the statement tree with the sequence and *)
(* if theorems. The facts come from a small abstract interpretation of the   *)
(* program (pointers in regions, Boolean registers); they are checked: every *)
(* template theorem proves its exit facts from its entry facts.              *)
(* ========================================================================= *)

needs "tisa/hol/tisa_x86_templates.ml";;

let TISA_RUNS_WEAKEN = prove
 (`!mc pc off e epi P Q Q' S C.
        (!t. Q t ==> Q' t) /\ tisa_x86_runs mc pc off e epi P Q S C
        ==> tisa_x86_runs mc pc off e epi P Q' S C`,
  REWRITE_TAC[tisa_x86_runs] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:tisa_state`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_POSTCONDITION_THM) THEN
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `tisa_exec S t` tisa_result_CASES) THEN
  REWRITE_TAC[tisa_x86_postf] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The IF test and the jump over the else.                                   *)
(* ------------------------------------------------------------------------- *)

let TISA_TEST_TAC execth stops =
  REWRITE_TAC[tisa_x86_test; tisa_x86_rel; tisa_bool] THEN X_GEN_TAC `t:tisa_state` THEN
  TISA_NAME_STATE_TAC THEN DISCH_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN TISA_RUN_TAC execth `pc:num` stops 1 THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_AND_REFL; VAL_EQ_0]) THEN ASM_REWRITE_TAC[];;

let TISA_JUMP_TAC execth stops =
  REWRITE_TAC[tisa_x86_jump; tisa_x86_rel] THEN X_GEN_TAC `t:tisa_state` THEN
  TISA_NAME_STATE_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN TISA_RUN_TAC execth `pc:num` stops 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let tisa_test_goal mc oi c ot ol =
  parse_term (Printf.sprintf "tisa_x86_test %s pc %d %d %d %d (%s)" mc oi c ot ol tisa_frame_str);;

let tisa_jump_goal mc oj oe =
  parse_term (Printf.sprintf "tisa_x86_jump %s pc %d %d (%s)" mc oj oe tisa_frame_str);;

(* ------------------------------------------------------------------------- *)
(* Facts of program points: pointer registers (register, region) and         *)
(* Boolean registers; None where no path continues.                       *)
(* ------------------------------------------------------------------------- *)

(* Some(pointers, Booleans), or None where no path continues. *)

let tisa_kill d f = match f with
  | None -> None
  | Some(p,b) -> Some(filter (fun (r,_) -> r <> d) p, filter (fun r -> r <> d) b);;

let tisa_add_bool d f = match f with
  | None -> None | Some(p,b) -> Some(p, setify(d::b));;

let tisa_add_ptr d r f = match f with
  | None -> None | Some(p,b) -> Some(setify((d,r)::p), b);;

let tisa_meet f g = match f,g with
  | None,h | h,None -> h
  | Some(p1,b1),Some(p2,b2) -> Some(intersect p1 p2, intersect b1 b2);;

let tisa_num t = dest_small_numeral t;;
let tisa_int t =
  match t with
  | Comb(Const("int_neg",_),Comb(Const("int_of_num",_),n)) -> - (dest_small_numeral n)
  | Comb(Const("int_of_num",_),n) -> dest_small_numeral n
  | _ -> failwith "tisa_int";;
let tisa_cname t = fst(dest_const(fst(strip_comb t)));;

let tisa_transfer instr f =
  let c,args = strip_comb instr in
  let is_bool ty = fst(dest_const ty) = "TyBool" in
  match fst(dest_const c), args with
  | "TImm",[ty;d;_] -> let f' = tisa_kill (tisa_num d) f in
                       if is_bool ty then tisa_add_bool (tisa_num d) f' else f'
  | "TMov",[ty;d;a] ->
      let ptr = (match f with Some(p,_) -> (try Some(assoc (tisa_num a) p) with Failure _ -> None) | None -> None) in
      let f' = tisa_kill (tisa_num d) f in
      if is_bool ty then tisa_add_bool (tisa_num d) f'
      else (match ptr with Some r when fst(dest_const ty) = "TyPtr" -> tisa_add_ptr (tisa_num d) r f' | _ -> f')
  | ("TBin"|"TShift"),[_;ty;d;_;_] -> let f' = tisa_kill (tisa_num d) f in
                                    if is_bool ty then tisa_add_bool (tisa_num d) f' else f'
  | "TExtract",[_;d;_;_;_] -> tisa_kill (tisa_num d) f
  | "TCmp",[_;_;d;_;_] -> tisa_add_bool (tisa_num d) (tisa_kill (tisa_num d) f)
  | "TSelect",[ty;d;_;_;_] -> let f' = tisa_kill (tisa_num d) f in
                              if is_bool ty then tisa_add_bool (tisa_num d) f' else f'
  | "TAddr",[r;d;_;_;_;_] -> tisa_add_ptr (tisa_num d) (tisa_num r) (tisa_kill (tisa_num d) f)
  | "TLoad",[ty;_;_;d;_;_] -> let f' = tisa_kill (tisa_num d) f in
                              if is_bool ty then tisa_add_bool (tisa_num d) f' else f'
  | "TLoadFrame",[ty;d;fi] ->
      let f' = tisa_kill (tisa_num d) f in
      if is_bool ty then tisa_add_bool (tisa_num d) f'
      else if fst(dest_const ty) = "TyPtr" && tisa_num fi mod 2 = 0
      then tisa_add_ptr (tisa_num d) (tisa_num fi / 2) f' else f'
  | "TStore",_ -> f
  | _ -> failwith "tisa_transfer: unknown instruction";;

(* Extra facts conjoined to every facts text, as "tregs t 6 = word j0": the
   loop being proved names its index and bound here. *)
let tisa_extra_facts = ref ([] : string list);;

let tisa_facts_text nregions f = match f with
  | None -> tisa_nofacts_str
  | Some(p,b) ->
      let base = tisa_facts_str nregions (sort (<) p) (sort (<) b) in
      if !tisa_extra_facts = [] then base
      else String.sub base 0 (String.length base - 1) ^
           String.concat "" (map (fun e -> " /\\ " ^ e) !tisa_extra_facts) ^ ")";;

(* ------------------------------------------------------------------------- *)
(* The generator.                                                            *)
(* ------------------------------------------------------------------------- *)

type tisa_image_ctx = {
  mc : string; mclen : int; epi : int; decls : int list; nregions : int;
  execth : thm * thm option array; spans : (string, (int * int * string)) Hashtbl.t;
  global : term };;

let tisa_hex_bytes hex =
  map (fun i -> int_of_string ("0x" ^ String.sub hex (2*i) 2)) (0--(String.length hex / 2 - 1));;

let tisa_cut_global ctx th = UNDISCH (SPEC_ALL th);;

(* A goal whose conjuncts are facts among the assumptions: accept each one,
   rewriting with the assumptions only as a fallback. Two facts can bound the
   same register (nested loops sharing a bound register: val(tregs t 3) = nv0
   and val(tregs t 3) = nv4), and rewriting with one of them would leave the
   other as nv0 = nv4. *)
let TISA_FACTS_CLOSE_TAC =
  BETA_TAC THEN REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE REFL_TAC ORELSE ASM_REWRITE_TAC[GSYM WORD_ADD]);;

let tisa_imp_facts p q =
  (* |- !t. P t ==> Q t, Q's conjuncts being among P's *)
  let tm = parse_term (Printf.sprintf "!t:tisa_state. %s t ==> %s t" p q) in
  tisa_side_prove "weaker facts" (tm, GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN TISA_FACTS_CLOSE_TAC);;

let tisa_span ctx path =
  match Hashtbl.find_all ctx.spans path with
  | [] -> failwith ("no span for path " ^ path)
  | l -> rev l;;   (* in emission order *)

let tisa_child path k = if path = "" then string_of_int k else path ^ "." ^ string_of_int k;;

let tisa_count = ref 0;;

(* Loops are proved by tisa_x86_loops.ml, through this hook. *)
let tisa_loop_hook =
  ref (fun (_:tisa_image_ctx) (_:term) (_:string) (_:((int*int) list * int list) option) (_:int) ->
         (failwith "loops not loaded" : thm * int * int * ((int*int) list * int list) option));;

(* Prove the statement at path with entry facts f; the code starts at
   cursor. Returns (G |- runs ..., start, end, exit facts). *)
let rec tisa_prove_stmt ctx node path f cursor =
  let mclen = ctx.mclen and epi = ctx.epi and mc = ctx.mc in
  let pf = tisa_facts_text ctx.nregions f in
  match tisa_cname node with
  | "TSkip" ->
      let g = parse_term (Printf.sprintf "tisa_x86_runs %s pc %d %d %d %s %s TSkip (%s)"
                            mc cursor cursor epi pf pf tisa_frame_str) in
      let th = prove(g, MATCH_MP_TAC TISA_SKIP_RUNS THEN REWRITE_TAC[TISA_FRAME_REFL]) in
      (ADD_ASSUM ctx.global th, cursor, cursor, f)
  | "TSeq" ->
      let _,[a;b] = strip_comb node in
      let tha,sa,ea,fa = tisa_prove_stmt ctx a (tisa_child path 0) f cursor in
      let thb,sb,eb,fb = tisa_prove_stmt ctx b (tisa_child path 1) fa ea in
      (MATCH_MP TISA_SEQ_RUNS (CONJ TISA_FRAME_IDEMPOT (CONJ tha thb)), sa, eb, fb)
  | "TIf" ->
      let _,[c;a;b] = strip_comb node in
      let ci = tisa_num c in
      (match f with None -> () | Some(_,bs) when mem ci bs -> () | _ -> failwith ("IF on a register not known Boolean at " ^ path));
      let spans = tisa_span ctx path in
      let (oi,li,_) = hd spans in
      let tha,sa,ea,fa = tisa_prove_stmt ctx a (tisa_child path 1) f (oi + li) in
      let has_else = tisa_cname b <> "TSkip" in
      let ol,thb,eb,fb =
        if has_else then
          let (oj,lj,_) = el 1 spans in
          if oj <> ea then failwith "IF-ELSE not at the end of the then-branch";
          let thb,sb,eb,fb = tisa_prove_stmt ctx b (tisa_child path 2) f (oj + lj) in
          (sb, thb, eb, fb)
        else
          let thb,sb,eb,fb = tisa_prove_stmt ctx b (tisa_child path 2) f ea in
          (ea, thb, ea, fb) in
      let oe = eb in
      let fq = tisa_meet fa fb in
      let q = tisa_facts_text ctx.nregions fq in
      let weaken th fx =
        let qx = tisa_facts_text ctx.nregions fx in
        if qx = q then th
        else MATCH_MP TISA_RUNS_WEAKEN (CONJ (tisa_imp_facts qx q) th) in
      let tha' = weaken tha fa and thb' = weaken thb fb in
      let tha'' =
        if has_else then
          let (oj,lj,_) = el 1 spans in
          let jth = time_prove (Printf.sprintf "%s jump %d" path oj)
                      (tisa_jump_goal mc oj oe) (TISA_JUMP_TAC ctx.execth [oe]) in
          MATCH_MP TISA_RUNS_JUMP (CONJ TISA_FRAME_IDEMPOT (CONJ tha' jth))
        else tha' in
      let tth = time_prove (Printf.sprintf "%s test %d" path oi)
                  (tisa_test_goal mc oi ci (oi + li) ol) (TISA_TEST_TAC ctx.execth [oi + li; ol]) in
      let side1 = tisa_side_prove (path ^ " Boolean")
                    (parse_term (Printf.sprintf "!t:tisa_state. %s t ==> tisa_bool (tregs t %d)" pf ci),
                     GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN TISA_FACTS_CLOSE_TAC) in
      let side2 = tisa_side_prove (path ^ " then facts")
                    (parse_term (Printf.sprintf "!t:tisa_state. %s t /\\ ~(tregs t %d = word 0) ==> %s t" pf ci pf),
                     MESON_TAC[]) in
      let side3 = tisa_side_prove (path ^ " else facts")
                    (parse_term (Printf.sprintf "!t:tisa_state. %s t /\\ tregs t %d = word 0 ==> %s t" pf ci pf),
                     MESON_TAC[]) in
      let th = MATCH_MP TISA_IF_RUNS
                 (end_itlist CONJ [TISA_FRAME_IDEMPOT; side1; side2; side3; tth; tha''; thb']) in
      (th, oi, oe, fq)
  | "TInstr" | "TReturn" | "TFund" ->
      let (off,len,tmpl) = hd (tisa_span ctx path) in
      let fq = (match tisa_cname node with
                | "TReturn" -> None
                | "TFund" -> f            (* FUND writes only the receipt word *)
                | _ -> tisa_transfer (rand node) f) in
      let q = tisa_facts_text ctx.nregions fq in
      let g = vsubst [node, `tisa_stmt_here:tisa_stmt`]
                (tisa_runs_goal mc mclen ctx.decls epi "tisa_stmt_here" off len pf q) in
      let tac =
        if tmpl = "STORE" then
          let _,[w;r;p;dsp;_] = strip_comb (rand node) in
          let disp = tisa_int dsp in
          TISA_RUNS_STORE_TAC ctx.execth (off,len) epi (tisa_num r, tisa_num p, disp, tisa_num w) mclen
        else TISA_RUNS_TAC ctx.execth [off + len; epi] in
      incr tisa_count;
      let th = time_prove (Printf.sprintf "%s %s %d" tmpl path off) g tac in
      (tisa_cut_global ctx th, off, off + len, fq)
  | "TCountLoop" | "TEarlyLoop" -> !tisa_loop_hook ctx node path f cursor
  | k -> failwith ("tisa_prove_stmt: not yet: " ^ k);;

(* ------------------------------------------------------------------------- *)
(* An image: G |- tisa_x86_runs mc pc 9 e epi P0 (\t. F) root C, where the  *)
(* body starts after the 9-byte prologue and P0 are the entry facts.         *)
(* ------------------------------------------------------------------------- *)

(* Each proved image: its context, program, entry facts and body theorem. *)
let tisa_images = ref ([] : (string * (tisa_image_ctx * term * string * thm)) list);;

let tisa_prove_image name prog hex spanlist =
  let t0 = Sys.time() in
  tisa_count := 0;
  let bs = tisa_hex_bytes hex in
  let mcname = String.lowercase_ascii name ^ "_mc" in
  let def = new_definition (mk_eq(mk_var(mcname,`:byte list`),
              mk_list(map (fun b -> mk_comb(`word:num->byte`, mk_small_numeral b)) bs, `:byte`))) in
  let execth = X86_MK_EXEC_RULE def in
  let _,[decls;init;root] = strip_comb prog in
  let modes = map (fun d -> tisa_num (fst(dest_pair d))) (dest_list decls) in
  let spans = Hashtbl.create 64 in
  List.iter (fun (ofs,l,tm,p) -> Hashtbl.add spans p (ofs,l,tm)) spanlist;
  let epi = (match filter (fun (_,_,tm,_) -> tm = "EPILOGUE") spanlist with
             | [(ofs,_,_,_)] -> ofs | _ -> failwith "no epilogue") in
  let global = parse_term (tisa_global_str (length bs) modes) in
  let ctx = { mc = mcname; mclen = length bs; epi = epi; decls = modes; nregions = length modes;
              execth = execth; spans = spans; global = global } in
  let f0 = itlist (fun v f ->
             let r,(ty,q) = (fun (a,b) -> a, dest_pair b) (dest_pair v) in
             match fst(dest_const ty) with
             | "TyPtr" -> tisa_add_ptr (tisa_num r) (tisa_num q) f
             | "TyBool" -> tisa_add_bool (tisa_num r) f
             | _ -> f) (dest_list init) (Some([],[])) in
  let th,s,e,fq = tisa_prove_stmt ctx root "" f0 9 in
  if fq <> None then failwith "a path continues past the end of the program";
  Printf.printf "IMAGE %s: %d bytes, %d template theorems, body %d..%d, %.1fs\n%!"
    name (length bs) !tisa_count s e (Sys.time() -. t0);
  tisa_images := (name, (ctx, prog, tisa_facts_text ctx.nregions f0, th)) :: !tisa_images;
  th;;

(* The record test_tisa writes for each image. *)
let tisa_image name prog hex spanlist =
  try ignore(tisa_prove_image name prog hex spanlist)
  with Failure msg -> Printf.printf "IMAGE %s FAILED: %s\n%!" name msg;;

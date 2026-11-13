(* ========================================================================= *)
(* HOLR v1 in HOL Light: the bytes of a stream, its records, and what an    *)
(* accepted stream claims.                                                   *)
(*                                                                           *)
(* Bytes are numbers below 256. Unsigned integers are LEB128 in minimal     *)
(* form, below 2^62 (so at most nine bytes). A stream is the magic, the     *)
(* pinned kernel identifier, four header integers, the encoded records, and *)
(* END: opcode 0x7f, the record count, and the FNV-1a 64 checksum of every  *)
(* byte before END, little endian. Encoding is a function; a reader is      *)
(* correct when what it accepts is the encoding of what it reports.        *)
(* ========================================================================= *)

needs "Library/words.ml";;

(* ------------------------------------------------------------------------- *)
(* Integers, checksum.                                                       *)
(* ------------------------------------------------------------------------- *)

let leb_enc_def = define
 `leb_enc v = if v < 128 then [v] else CONS (v MOD 128 + 128) (leb_enc (v DIV 128))`;;

let LEB_ENC_NONEMPTY = prove
 (`!v. ~(leb_enc v = [])`,
  GEN_TAC THEN ONCE_REWRITE_TAC[leb_enc_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[NOT_CONS_NIL]);;

(* The 64-bit FNV-1a state over a list of bytes. *)
let fnv1a_def = define
 `(fnv1a (h:int64) [] = h) /\
  (fnv1a h (CONS b bs) = fnv1a (word_mul (word_xor h (word b)) (word 1099511628211)) bs)`;;

let fnv_offset = new_definition
 `fnv_offset:int64 = word 14695981039346656037`;;

(* Little-endian bytes of a 64-bit word. *)
let le8 = new_definition
 `le8 (h:int64) = MAP (\i. (val h DIV (2 EXP (8 * i))) MOD 256) [0;1;2;3;4;5;6;7]`;;

(* ------------------------------------------------------------------------- *)
(* Records, with the operand layouts of the format.                          *)
(* ------------------------------------------------------------------------- *)

let holr_record_INDUCT,holr_record_RECURSION = define_type
 "holr_record =
    RName (num list)
  | RTyVar num | RTyApp num (num list)
  | RVar num num | RConst num num | RComb num num | RAbs num num
  | RRefl num | RTrans num num | RMkComb num num | RAbsRule num num
  | RBeta num | RAssume num | REqMp num num | RDeduct num num
  | RInstType ((num#num) list) num | RInst ((num#num) list) num
  | RNewType num num | RNewConstant num num | RNewAxiom num
  | RNewDefinition num | RNewTypedef num num num num | RPolicy num
  | RExpect num (num list) num | RLabel num num | REmit num
  | RExpectRefused | RExpectAxioms num (num list)
  | RExpectAlpha num (num list) num
  | RDropType num | RDropTerm num | RDropThm num";;

let holr_flat = new_definition
 `holr_flat (l:(num list) list) = ITLIST APPEND l []`;;

let holr_ids = new_definition
 `holr_ids (l:num list) = APPEND (leb_enc (LENGTH l)) (holr_flat (MAP leb_enc l))`;;

let holr_pairs = new_definition
 `holr_pairs (l:(num#num) list) =
    APPEND (leb_enc (LENGTH l)) (holr_flat (MAP (\(a,b). APPEND (leb_enc a) (leb_enc b)) l))`;;

let holr_rec_enc = define
 `(holr_rec_enc (RName bs) = CONS 1 (APPEND (leb_enc (LENGTH bs)) bs)) /\
  (holr_rec_enc (RTyVar n) = CONS 2 (leb_enc n)) /\
  (holr_rec_enc (RTyApp n ys) = CONS 3 (APPEND (leb_enc n) (holr_ids ys))) /\
  (holr_rec_enc (RVar n y) = CONS 4 (APPEND (leb_enc n) (leb_enc y))) /\
  (holr_rec_enc (RConst n y) = CONS 5 (APPEND (leb_enc n) (leb_enc y))) /\
  (holr_rec_enc (RComb s t) = CONS 6 (APPEND (leb_enc s) (leb_enc t))) /\
  (holr_rec_enc (RAbs v t) = CONS 7 (APPEND (leb_enc v) (leb_enc t))) /\
  (holr_rec_enc (RRefl t) = CONS 16 (leb_enc t)) /\
  (holr_rec_enc (RTrans h1 h2) = CONS 17 (APPEND (leb_enc h1) (leb_enc h2))) /\
  (holr_rec_enc (RMkComb h1 h2) = CONS 18 (APPEND (leb_enc h1) (leb_enc h2))) /\
  (holr_rec_enc (RAbsRule t h) = CONS 19 (APPEND (leb_enc t) (leb_enc h))) /\
  (holr_rec_enc (RBeta t) = CONS 20 (leb_enc t)) /\
  (holr_rec_enc (RAssume t) = CONS 21 (leb_enc t)) /\
  (holr_rec_enc (REqMp h1 h2) = CONS 22 (APPEND (leb_enc h1) (leb_enc h2))) /\
  (holr_rec_enc (RDeduct h1 h2) = CONS 23 (APPEND (leb_enc h1) (leb_enc h2))) /\
  (holr_rec_enc (RInstType ps h) = CONS 24 (APPEND (holr_pairs ps) (leb_enc h))) /\
  (holr_rec_enc (RInst ps h) = CONS 25 (APPEND (holr_pairs ps) (leb_enc h))) /\
  (holr_rec_enc (RNewType n a) = CONS 32 (APPEND (leb_enc n) (leb_enc a))) /\
  (holr_rec_enc (RNewConstant n y) = CONS 33 (APPEND (leb_enc n) (leb_enc y))) /\
  (holr_rec_enc (RNewAxiom t) = CONS 34 (leb_enc t)) /\
  (holr_rec_enc (RNewDefinition t) = CONS 35 (leb_enc t)) /\
  (holr_rec_enc (RNewTypedef n a r h) =
     CONS 36 (APPEND (leb_enc n) (APPEND (leb_enc a) (APPEND (leb_enc r) (leb_enc h))))) /\
  (holr_rec_enc (RPolicy p) = CONS 37 (leb_enc p)) /\
  (holr_rec_enc (RExpect h hs c) = CONS 48 (APPEND (leb_enc h) (APPEND (holr_ids hs) (leb_enc c)))) /\
  (holr_rec_enc (RLabel h n) = CONS 49 (APPEND (leb_enc h) (leb_enc n))) /\
  (holr_rec_enc (REmit h) = CONS 50 (leb_enc h)) /\
  (holr_rec_enc RExpectRefused = [51]) /\
  (holr_rec_enc (RExpectAxioms h hs) = CONS 52 (APPEND (leb_enc h) (holr_ids hs))) /\
  (holr_rec_enc (RExpectAlpha h hs c) =
     CONS 53 (APPEND (leb_enc h) (APPEND (holr_ids hs) (leb_enc c)))) /\
  (holr_rec_enc (RDropType y) = CONS 64 (leb_enc y)) /\
  (holr_rec_enc (RDropTerm t) = CONS 65 (leb_enc t)) /\
  (holr_rec_enc (RDropThm h) = CONS 66 (leb_enc h))`;;

(* ------------------------------------------------------------------------- *)
(* Streams.                                                                  *)
(* ------------------------------------------------------------------------- *)

let holr_magic = new_definition
 `holr_magic = [72; 79; 76; 82; 80; 76; 89; 49]`;;

(* The raw SHA-256 of the pinned fusion.ml, as the format fixes it. *)
let holr_kernel_id = new_definition
 `holr_kernel_id =
    [41; 84; 75; 233; 45; 156; 193; 230; 179; 181; 155; 165; 178; 16; 96; 75;
     154; 116; 131; 102; 166; 139; 59; 205; 194; 97; 151; 23; 214; 143; 217; 138]`;;

(* Everything before END: header and records. *)
let holr_body = new_definition
 `holr_body policy flags recs =
    APPEND holr_magic
     (APPEND holr_kernel_id
       (APPEND (leb_enc 1) (APPEND (leb_enc 0) (APPEND (leb_enc policy)
        (APPEND (leb_enc flags) (holr_flat (MAP holr_rec_enc recs)))))))`;;

let holr_stream = new_definition
 `holr_stream policy flags recs =
    APPEND (holr_body policy flags recs)
           (CONS 127 (APPEND (leb_enc (LENGTH recs))
                             (le8 (fnv1a fnv_offset (holr_body policy flags recs)))))`;;

(* ------------------------------------------------------------------------- *)
(* Names from bytes (the port's characters: the first bit is the highest). *)
(* ------------------------------------------------------------------------- *)

let hchar_of = new_definition
 `hchar_of n = ASCII (ODD (n DIV 128)) (ODD (n DIV 64)) (ODD (n DIV 32)) (ODD (n DIV 16))
                     (ODD (n DIV 8)) (ODD (n DIV 4)) (ODD (n DIV 2)) (ODD n)`;;

let holr_name = new_definition
 `holr_name (bs:num list) = MAP hchar_of bs`;;

(* ------------------------------------------------------------------------- *)
(* The axiom policy. OPEN (0) admits any axiom, STANDARD (1) only HOL       *)
(* Light's three standard axioms, SEALED (2 and above) none. Acceptance     *)
(* runs at the larger of the host's policy floor and the stream's header,   *)
(* and POLICY records only tighten it.                                       *)
(*                                                                           *)
(* STANDARD is CeTTa's (hol_env.c, std_recognize_axiom and hk_decl_standard;*)
(* the texts are its hol_std_data.inc, from HOL Light 924faf0c). An axiom   *)
(* is standard in a context when it is ETA_AX, SELECT_AX or INFINITY_AX up  *)
(* to alpha-equivalence and every constant and type operator in it is      *)
(* declared by a standard event: the bootstrap's bool, fun and "=", the    *)
(* type ind of arity 0, the constant "@" at (A->bool)->A, or a basic       *)
(* definition of T, /\, ==>, !, ?, F, ~, ONE_ONE or ONTO whose type is the *)
(* standard one, whose right-hand side is the standard one up to alpha,    *)
(* and whose own constants and type operators are standard, recursively.   *)
(* ------------------------------------------------------------------------- *)

let hstd_defs = new_definition
 `hstd_defs:(string#holtype#holterm)list =
    [("T",
     TyApp "bool" [],
     TmComb (TmComb (TmConst "=" (TyApp "fun" [TyApp "fun" [TyApp "bool" []; TyApp "bool" []]; TyApp "fun" [TyApp "fun" [TyApp "bool" []; TyApp "bool" []]; TyApp "bool" []]])) (TmAbs (TmVar "p" (TyApp "bool" [])) (TmVar "p" (TyApp "bool" [])))) (TmAbs (TmVar "p" (TyApp "bool" [])) (TmVar "p" (TyApp "bool" []))));
    ("/\\",
     TyApp "fun" [TyApp "bool" []; TyApp "fun" [TyApp "bool" []; TyApp "bool" []]],
     TmAbs (TmVar "p" (TyApp "bool" [])) (TmAbs (TmVar "q" (TyApp "bool" [])) (TmComb (TmComb (TmConst "=" (TyApp "fun" [TyApp "fun" [TyApp "fun" [TyApp "bool" []; TyApp "fun" [TyApp "bool" []; TyApp "bool" []]]; TyApp "bool" []]; TyApp "fun" [TyApp "fun" [TyApp "fun" [TyApp "bool" []; TyApp "fun" [TyApp "bool" []; TyApp "bool" []]]; TyApp "bool" []]; TyApp "bool" []]])) (TmAbs (TmVar "f" (TyApp "fun" [TyApp "bool" []; TyApp "fun" [TyApp "bool" []; TyApp "bool" []]])) (TmComb (TmComb (TmVar "f" (TyApp "fun" [TyApp "bool" []; TyApp "fun" [TyApp "bool" []; TyApp "bool" []]])) (TmVar "p" (TyApp "bool" []))) (TmVar "q" (TyApp "bool" []))))) (TmAbs (TmVar "f" (TyApp "fun" [TyApp "bool" []; TyApp "fun" [TyApp "bool" []; TyApp "bool" []]])) (TmComb (TmComb (TmVar "f" (TyApp "fun" [TyApp "bool" []; TyApp "fun" [TyApp "bool" []; TyApp "bool" []]])) (TmConst "T" (TyApp "bool" []))) (TmConst "T" (TyApp "bool" [])))))));
    ("==>",
     TyApp "fun" [TyApp "bool" []; TyApp "fun" [TyApp "bool" []; TyApp "bool" []]],
     TmAbs (TmVar "p" (TyApp "bool" [])) (TmAbs (TmVar "q" (TyApp "bool" [])) (TmComb (TmComb (TmConst "=" (TyApp "fun" [TyApp "bool" []; TyApp "fun" [TyApp "bool" []; TyApp "bool" []]])) (TmComb (TmComb (TmConst "/\\" (TyApp "fun" [TyApp "bool" []; TyApp "fun" [TyApp "bool" []; TyApp "bool" []]])) (TmVar "p" (TyApp "bool" []))) (TmVar "q" (TyApp "bool" [])))) (TmVar "p" (TyApp "bool" [])))));
    ("!",
     TyApp "fun" [TyApp "fun" [TyVar "A"; TyApp "bool" []]; TyApp "bool" []],
     TmAbs (TmVar "P" (TyApp "fun" [TyVar "A"; TyApp "bool" []])) (TmComb (TmComb (TmConst "=" (TyApp "fun" [TyApp "fun" [TyVar "A"; TyApp "bool" []]; TyApp "fun" [TyApp "fun" [TyVar "A"; TyApp "bool" []]; TyApp "bool" []]])) (TmVar "P" (TyApp "fun" [TyVar "A"; TyApp "bool" []]))) (TmAbs (TmVar "x" (TyVar "A")) (TmConst "T" (TyApp "bool" [])))));
    ("?",
     TyApp "fun" [TyApp "fun" [TyVar "A"; TyApp "bool" []]; TyApp "bool" []],
     TmAbs (TmVar "P" (TyApp "fun" [TyVar "A"; TyApp "bool" []])) (TmComb (TmConst "!" (TyApp "fun" [TyApp "fun" [TyApp "bool" []; TyApp "bool" []]; TyApp "bool" []])) (TmAbs (TmVar "q" (TyApp "bool" [])) (TmComb (TmComb (TmConst "==>" (TyApp "fun" [TyApp "bool" []; TyApp "fun" [TyApp "bool" []; TyApp "bool" []]])) (TmComb (TmConst "!" (TyApp "fun" [TyApp "fun" [TyVar "A"; TyApp "bool" []]; TyApp "bool" []])) (TmAbs (TmVar "x" (TyVar "A")) (TmComb (TmComb (TmConst "==>" (TyApp "fun" [TyApp "bool" []; TyApp "fun" [TyApp "bool" []; TyApp "bool" []]])) (TmComb (TmVar "P" (TyApp "fun" [TyVar "A"; TyApp "bool" []])) (TmVar "x" (TyVar "A")))) (TmVar "q" (TyApp "bool" [])))))) (TmVar "q" (TyApp "bool" []))))));
    ("F",
     TyApp "bool" [],
     TmComb (TmConst "!" (TyApp "fun" [TyApp "fun" [TyApp "bool" []; TyApp "bool" []]; TyApp "bool" []])) (TmAbs (TmVar "p" (TyApp "bool" [])) (TmVar "p" (TyApp "bool" []))));
    ("~",
     TyApp "fun" [TyApp "bool" []; TyApp "bool" []],
     TmAbs (TmVar "p" (TyApp "bool" [])) (TmComb (TmComb (TmConst "==>" (TyApp "fun" [TyApp "bool" []; TyApp "fun" [TyApp "bool" []; TyApp "bool" []]])) (TmVar "p" (TyApp "bool" []))) (TmConst "F" (TyApp "bool" []))));
    ("ONE_ONE",
     TyApp "fun" [TyApp "fun" [TyVar "A"; TyVar "B"]; TyApp "bool" []],
     TmAbs (TmVar "_2064" (TyApp "fun" [TyVar "A"; TyVar "B"])) (TmComb (TmConst "!" (TyApp "fun" [TyApp "fun" [TyVar "A"; TyApp "bool" []]; TyApp "bool" []])) (TmAbs (TmVar "x1" (TyVar "A")) (TmComb (TmConst "!" (TyApp "fun" [TyApp "fun" [TyVar "A"; TyApp "bool" []]; TyApp "bool" []])) (TmAbs (TmVar "x2" (TyVar "A")) (TmComb (TmComb (TmConst "==>" (TyApp "fun" [TyApp "bool" []; TyApp "fun" [TyApp "bool" []; TyApp "bool" []]])) (TmComb (TmComb (TmConst "=" (TyApp "fun" [TyVar "B"; TyApp "fun" [TyVar "B"; TyApp "bool" []]])) (TmComb (TmVar "_2064" (TyApp "fun" [TyVar "A"; TyVar "B"])) (TmVar "x1" (TyVar "A")))) (TmComb (TmVar "_2064" (TyApp "fun" [TyVar "A"; TyVar "B"])) (TmVar "x2" (TyVar "A"))))) (TmComb (TmComb (TmConst "=" (TyApp "fun" [TyVar "A"; TyApp "fun" [TyVar "A"; TyApp "bool" []]])) (TmVar "x1" (TyVar "A"))) (TmVar "x2" (TyVar "A")))))))));
    ("ONTO",
     TyApp "fun" [TyApp "fun" [TyVar "A"; TyVar "B"]; TyApp "bool" []],
     TmAbs (TmVar "_2069" (TyApp "fun" [TyVar "A"; TyVar "B"])) (TmComb (TmConst "!" (TyApp "fun" [TyApp "fun" [TyVar "B"; TyApp "bool" []]; TyApp "bool" []])) (TmAbs (TmVar "y" (TyVar "B")) (TmComb (TmConst "?" (TyApp "fun" [TyApp "fun" [TyVar "A"; TyApp "bool" []]; TyApp "bool" []])) (TmAbs (TmVar "x" (TyVar "A")) (TmComb (TmComb (TmConst "=" (TyApp "fun" [TyVar "B"; TyApp "fun" [TyVar "B"; TyApp "bool" []]])) (TmVar "y" (TyVar "B"))) (TmComb (TmVar "_2069" (TyApp "fun" [TyVar "A"; TyVar "B"])) (TmVar "x" (TyVar "A")))))))))]`;;

let hstd_axioms = new_definition
 `hstd_axioms:holterm list =
    [TmComb (TmConst "!" (TyApp "fun" [TyApp "fun" [TyApp "fun" [TyVar "A"; TyVar "B"]; TyApp "bool" []]; TyApp "bool" []])) (TmAbs (TmVar "t" (TyApp "fun" [TyVar "A"; TyVar "B"])) (TmComb (TmComb (TmConst "=" (TyApp "fun" [TyApp "fun" [TyVar "A"; TyVar "B"]; TyApp "fun" [TyApp "fun" [TyVar "A"; TyVar "B"]; TyApp "bool" []]])) (TmAbs (TmVar "x" (TyVar "A")) (TmComb (TmVar "t" (TyApp "fun" [TyVar "A"; TyVar "B"])) (TmVar "x" (TyVar "A"))))) (TmVar "t" (TyApp "fun" [TyVar "A"; TyVar "B"]))));
     TmComb (TmConst "!" (TyApp "fun" [TyApp "fun" [TyApp "fun" [TyVar "A"; TyApp "bool" []]; TyApp "bool" []]; TyApp "bool" []])) (TmAbs (TmVar "P" (TyApp "fun" [TyVar "A"; TyApp "bool" []])) (TmComb (TmConst "!" (TyApp "fun" [TyApp "fun" [TyVar "A"; TyApp "bool" []]; TyApp "bool" []])) (TmAbs (TmVar "x" (TyVar "A")) (TmComb (TmComb (TmConst "==>" (TyApp "fun" [TyApp "bool" []; TyApp "fun" [TyApp "bool" []; TyApp "bool" []]])) (TmComb (TmVar "P" (TyApp "fun" [TyVar "A"; TyApp "bool" []])) (TmVar "x" (TyVar "A")))) (TmComb (TmVar "P" (TyApp "fun" [TyVar "A"; TyApp "bool" []])) (TmComb (TmConst "@" (TyApp "fun" [TyApp "fun" [TyVar "A"; TyApp "bool" []]; TyVar "A"])) (TmVar "P" (TyApp "fun" [TyVar "A"; TyApp "bool" []]))))))));
     TmComb (TmConst "?" (TyApp "fun" [TyApp "fun" [TyApp "fun" [TyApp "ind" []; TyApp "ind" []]; TyApp "bool" []]; TyApp "bool" []])) (TmAbs (TmVar "f" (TyApp "fun" [TyApp "ind" []; TyApp "ind" []])) (TmComb (TmComb (TmConst "/\\" (TyApp "fun" [TyApp "bool" []; TyApp "fun" [TyApp "bool" []; TyApp "bool" []]])) (TmComb (TmConst "ONE_ONE" (TyApp "fun" [TyApp "fun" [TyApp "ind" []; TyApp "ind" []]; TyApp "bool" []])) (TmVar "f" (TyApp "fun" [TyApp "ind" []; TyApp "ind" []])))) (TmComb (TmConst "~" (TyApp "fun" [TyApp "bool" []; TyApp "bool" []])) (TmComb (TmConst "ONTO" (TyApp "fun" [TyApp "fun" [TyApp "ind" []; TyApp "ind" []]; TyApp "bool" []])) (TmVar "f" (TyApp "fun" [TyApp "ind" []; TyApp "ind" []]))))))]`;;

let hstd_choice_ty = new_definition
 `hstd_choice_ty = TyApp "fun" [TyApp "fun" [TyVar "A"; TyApp "bool" []]; TyVar "A"]`;;


(* The type operators and constants a term mentions, with repetitions. *)
let HTYNAMES_DEF = new_recursive_definition holtype_RECURSION
 `(htynames (TyVar v) = []) /\
  (htynames (TyApp s tys) = CONS s (htynames_list tys)) /\
  (htynames_list [] = []) /\
  (htynames_list (CONS ty tys) = APPEND (htynames ty) (htynames_list tys))`;;

let htm_consts = define
 `(htm_consts (TmVar x ty) = []) /\
  (htm_consts (TmConst c ty) = [c]) /\
  (htm_consts (TmComb s t) = APPEND (htm_consts s) (htm_consts t)) /\
  (htm_consts (TmAbs v t) = APPEND (htm_consts v) (htm_consts t))`;;

let htm_tyops = define
 `(htm_tyops (TmVar x ty) = htynames ty) /\
  (htm_tyops (TmConst c ty) = htynames ty) /\
  (htm_tyops (TmComb s t) = APPEND (htm_tyops s) (htm_tyops t)) /\
  (htm_tyops (TmAbs v t) = APPEND (htm_tyops v) (htm_tyops t))`;;

(* Whether an update declaring a constant, or a type operator, is a        *)
(* standard event, given which earlier constants and type operators are.   *)
let hstd_upd_c = define
 `(hstd_upd_c (HNewConst c ty) (pc:string->bool) (pt:string->bool) <=>
      c = "=" /\ ty = HFun (TyVar "A") (HFun (TyVar "A") HBool) \/
      c = "@" /\ ty = hstd_choice_ty) /\
  (hstd_upd_c (HConstSpec eqs prop) pc pt <=>
      ?c r. eqs = [c,r] /\ prop = (TmVar c (htypeof r) =:= r) /\
            (?b. MEM (c,htypeof r,b) hstd_defs /\ HACONV r b) /\
            ALL pc (htm_consts r) /\ ALL pt (htm_tyops r)) /\
  (hstd_upd_c (HTypeDefn n p an rn) pc pt <=> F) /\
  (hstd_upd_c (HNewType n k) pc pt <=> F) /\
  (hstd_upd_c (HNewAxiom p) pc pt <=> F)`;;

let hstd_upd_t = define
 `(hstd_upd_t (HNewType n k) <=> n = "bool" /\ k = 0 \/ n = "fun" /\ k = 2 \/
                                 n = "ind" /\ k = 0) /\
  (hstd_upd_t (HTypeDefn n p an rn) <=> F) /\
  (hstd_upd_t (HConstSpec eqs prop) <=> F) /\
  (hstd_upd_t (HNewConst c ty) <=> F) /\
  (hstd_upd_t (HNewAxiom p) <=> F)`;;

(* Along a context: which constant names and which type operator names are *)
(* declared by a standard event (each name is declared once in a valid      *)
(* context, by its first update in the list).                               *)
let hstd_decls = new_recursive_definition list_RECURSION
 `(hstd_decls [] = ((\c:string. F),(\n:string. F))) /\
  (hstd_decls (CONS upd rest) =
     ((\c. if MEM c (MAP FST (hconsts_of_upd upd))
           then hstd_upd_c upd (FST(hstd_decls rest)) (SND(hstd_decls rest))
           else FST(hstd_decls rest) c),
      (\n. if MEM n (MAP FST (htypes_of_upd upd)) then hstd_upd_t upd
           else SND(hstd_decls rest) n)))`;;

let hstd_term = new_definition
 `hstd_term ctx t <=> ALL (FST(hstd_decls ctx)) (htm_consts t) /\
                      ALL (SND(hstd_decls ctx)) (htm_tyops t)`;;

let hstd_axiom = new_definition
 `hstd_axiom ctx p <=> (?a. MEM a hstd_axioms /\ HACONV p a) /\ hstd_term ctx p`;;

(* The policy's verdict on an axiom. *)
let holr_axiom_ok = new_definition
 `holr_axiom_ok pol ctx p <=> pol = 0 \/ pol = 1 /\ hstd_axiom ctx p`;;

(* ------------------------------------------------------------------------- *)
(* What a stream means. The state holds the context; the name, type, term   *)
(* and theorem spaces; the dropped ids by space (1 types, 2 terms, 3        *)
(* theorems); and the axiom policy, which NEW_AXIOM obeys (holr_axiom_ok).  *)
(* Terms are built exactly as HOL Light's                                    *)
(* constructors build them, with their checks. A theorem entry is any       *)
(* sequent derivable in the context when it is made: the meaning of a      *)
(* stream does not depend on how its theorems were derived, so the rule     *)
(* records share one clause. Each EXPECT_ALPHA is a claim: its hypotheses   *)
(* and conclusion, as the stream's own terms, form a derivable sequent.     *)
(* Exact EXPECT, EXPECT_AXIOMS and EXPECT_REFUSED have no clause: a stream  *)
(* using them is not accepted under this meaning. A type definition takes   *)
(* its predicate from the witness theorem up to alpha-equivalence, as a     *)
(* theorem entry is any derivable sequent and theorems are compared up to   *)
(* alpha; the new theory then holds an alpha-variant of HOL Light's.        *)
(* ------------------------------------------------------------------------- *)

new_type_abbrev("hrstate",
  `:hupdate list # string list # holtype list # holterm list #
    (holterm list # holterm) list # (num#num) list # num`);;

let holr_live = new_definition
 `holr_live sp (n:num) len drops <=> n < len /\ ~MEM (sp,n) drops`;;

(* Every operand of a record that names a type, term or theorem is live.    *)
let holr_pairs_flat = define
 `(holr_pairs_flat [] = []) /\
  (holr_pairs_flat (CONS (a:num,b:num) ps) = CONS a (CONS b (holr_pairs_flat ps)))`;;

(* Defined through the record type's recursion theorem: the same clauses as *)
(* a `define` would take, without the general well-definedness proof that  *)
(* `define` builds for 32 constructors. The theorem keeps the form `define` *)
(* returns: the clauses with free variables.                                *)
let holr_operands =
  let th = new_recursive_definition holr_record_RECURSION
 `(holr_operands (RName bs) = ([],[],[])) /\
  (holr_operands (RTyVar n) = ([],[],[])) /\
  (holr_operands (RTyApp n ys) = (ys,[],[])) /\
  (holr_operands (RVar n y) = ([y],[],[])) /\
  (holr_operands (RConst n y) = ([y],[],[])) /\
  (holr_operands (RComb s t) = ([],[s;t],[])) /\
  (holr_operands (RAbs v t) = ([],[v;t],[])) /\
  (holr_operands (RRefl t) = ([],[t],[])) /\
  (holr_operands (RTrans h1 h2) = ([],[],[h1;h2])) /\
  (holr_operands (RMkComb h1 h2) = ([],[],[h1;h2])) /\
  (holr_operands (RAbsRule t h) = ([],[t],[h])) /\
  (holr_operands (RBeta t) = ([],[t],[])) /\
  (holr_operands (RAssume t) = ([],[t],[])) /\
  (holr_operands (REqMp h1 h2) = ([],[],[h1;h2])) /\
  (holr_operands (RDeduct h1 h2) = ([],[],[h1;h2])) /\
  (holr_operands (RInstType ps h) = (holr_pairs_flat ps,[],[h])) /\
  (holr_operands (RInst ps h) = ([],holr_pairs_flat ps,[h])) /\
  (holr_operands (RNewType n a) = ([],[],[])) /\
  (holr_operands (RNewConstant n y) = ([y],[],[])) /\
  (holr_operands (RNewAxiom t) = ([],[t],[])) /\
  (holr_operands (RNewDefinition t) = ([],[t],[])) /\
  (holr_operands (RNewTypedef n a r h) = ([],[],[h])) /\
  (holr_operands (RPolicy p) = ([],[],[])) /\
  (holr_operands (RExpect h hs c) = ([],CONS c hs,[h])) /\
  (holr_operands (RLabel h n) = ([],[],[h])) /\
  (holr_operands (REmit h) = ([],[],[h])) /\
  (holr_operands RExpectRefused = ([],[],[])) /\
  (holr_operands (RExpectAxioms h hs) = ([],[],CONS h hs)) /\
  (holr_operands (RExpectAlpha h hs c) = ([],CONS c hs,[h])) /\
  (holr_operands (RDropType y) = ([y],[],[])) /\
  (holr_operands (RDropTerm t) = ([],[t],[])) /\
  (holr_operands (RDropThm h) = ([],[],[h]))` in
  end_itlist CONJ (map SPEC_ALL (CONJUNCTS th));;

let holr_ops_live = new_definition
 `holr_ops_live ((ctx,nms,tys,tms,ths,drops,pol):hrstate) r <=>
    ALL (\y. holr_live 1 y (LENGTH tys) drops) (FST(holr_operands r)) /\
    ALL (\t. holr_live 2 t (LENGTH tms) drops) (FST(SND(holr_operands r))) /\
    ALL (\h. holr_live 3 h (LENGTH ths) drops) (SND(SND(holr_operands r)))`;;

let holr_is_rule = define
 `(holr_is_rule (RRefl t) <=> T) /\ (holr_is_rule (RTrans h1 h2) <=> T) /\
  (holr_is_rule (RMkComb h1 h2) <=> T) /\ (holr_is_rule (RAbsRule t h) <=> T) /\
  (holr_is_rule (RBeta t) <=> T) /\ (holr_is_rule (RAssume t) <=> T) /\
  (holr_is_rule (REqMp h1 h2) <=> T) /\ (holr_is_rule (RDeduct h1 h2) <=> T) /\
  (holr_is_rule (RInstType ps h) <=> T) /\ (holr_is_rule (RInst ps h) <=> T) /\
  (holr_is_rule (RName bs) <=> F) /\ (holr_is_rule (RTyVar n) <=> F) /\
  (holr_is_rule (RTyApp n ys) <=> F) /\ (holr_is_rule (RVar n y) <=> F) /\
  (holr_is_rule (RConst n y) <=> F) /\ (holr_is_rule (RComb s t) <=> F) /\
  (holr_is_rule (RAbs v t) <=> F) /\ (holr_is_rule (RNewType n a) <=> F) /\
  (holr_is_rule (RNewConstant n y) <=> F) /\ (holr_is_rule (RNewAxiom t) <=> F) /\
  (holr_is_rule (RNewDefinition t) <=> F) /\ (holr_is_rule (RNewTypedef n a r h) <=> F) /\
  (holr_is_rule (RPolicy p) <=> F) /\ (holr_is_rule (RExpect h hs c) <=> F) /\
  (holr_is_rule (RLabel h n) <=> F) /\ (holr_is_rule (REmit h) <=> F) /\
  (holr_is_rule RExpectRefused <=> F) /\ (holr_is_rule (RExpectAxioms h hs) <=> F) /\
  (holr_is_rule (RExpectAlpha h hs c) <=> F) /\ (holr_is_rule (RDropType y) <=> F) /\
  (holr_is_rule (RDropTerm t) <=> F) /\ (holr_is_rule (RDropThm h) <=> F)`;;

let holr_step_RULES,holr_step_INDUCT,holr_step_CASES = new_inductive_definition
 `(!ctx nms tys tms ths drops pol bs.
     holr_step (ctx,nms,tys,tms,ths,drops,pol) (RName bs)
               (ctx,APPEND nms [holr_name bs],tys,tms,ths,drops,pol)) /\
  (!ctx nms tys tms ths drops pol n.
     n < LENGTH nms
     ==> holr_step (ctx,nms,tys,tms,ths,drops,pol) (RTyVar n)
                   (ctx,nms,APPEND tys [TyVar (EL n nms)],tms,ths,drops,pol)) /\
  (!ctx nms tys tms ths drops pol n ys.
     holr_ops_live (ctx,nms,tys,tms,ths,drops,pol) (RTyApp n ys) /\ n < LENGTH nms /\
     hlookup (htype_list ctx) (EL n nms) = SOME (LENGTH ys)
     ==> holr_step (ctx,nms,tys,tms,ths,drops,pol) (RTyApp n ys)
                   (ctx,nms,APPEND tys [TyApp (EL n nms) (MAP (\y. EL y tys) ys)],
                    tms,ths,drops,pol)) /\
  (!ctx nms tys tms ths drops pol n y.
     holr_ops_live (ctx,nms,tys,tms,ths,drops,pol) (RVar n y) /\ n < LENGTH nms
     ==> holr_step (ctx,nms,tys,tms,ths,drops,pol) (RVar n y)
                   (ctx,nms,tys,APPEND tms [TmVar (EL n nms) (EL y tys)],ths,drops,pol)) /\
  (!ctx nms tys tms ths drops pol n y ty0 tyin.
     holr_ops_live (ctx,nms,tys,tms,ths,drops,pol) (RConst n y) /\ n < LENGTH nms /\
     hlookup (hconst_list ctx) (EL n nms) = SOME ty0 /\ EL y tys = HTYPE_SUBST tyin ty0
     ==> holr_step (ctx,nms,tys,tms,ths,drops,pol) (RConst n y)
                   (ctx,nms,tys,APPEND tms [TmConst (EL n nms) (EL y tys)],ths,drops,pol)) /\
  (!ctx nms tys tms ths drops pol s t B.
     holr_ops_live (ctx,nms,tys,tms,ths,drops,pol) (RComb s t) /\
     htypeof (EL s tms) = HFun (htypeof (EL t tms)) B
     ==> holr_step (ctx,nms,tys,tms,ths,drops,pol) (RComb s t)
                   (ctx,nms,tys,APPEND tms [TmComb (EL s tms) (EL t tms)],ths,drops,pol)) /\
  (!ctx nms tys tms ths drops pol v t x ty.
     holr_ops_live (ctx,nms,tys,tms,ths,drops,pol) (RAbs v t) /\ EL v tms = TmVar x ty
     ==> holr_step (ctx,nms,tys,tms,ths,drops,pol) (RAbs v t)
                   (ctx,nms,tys,APPEND tms [TmAbs (EL v tms) (EL t tms)],ths,drops,pol)) /\
  (!ctx nms tys tms ths drops pol r h c.
     holr_is_rule r /\ holr_ops_live (ctx,nms,tys,tms,ths,drops,pol) r /\
     hproves (hthyof ctx) h c
     ==> holr_step (ctx,nms,tys,tms,ths,drops,pol) r
                   (ctx,nms,tys,tms,APPEND ths [(h,c)],drops,pol)) /\
  (!ctx nms tys tms ths drops pol n a.
     n < LENGTH nms /\ hlookup (htype_list ctx) (EL n nms) = NONE
     ==> holr_step (ctx,nms,tys,tms,ths,drops,pol) (RNewType n a)
                   (CONS (HNewType (EL n nms) a) ctx,nms,tys,tms,ths,drops,pol)) /\
  (!ctx nms tys tms ths drops pol n y.
     holr_ops_live (ctx,nms,tys,tms,ths,drops,pol) (RNewConstant n y) /\ n < LENGTH nms /\
     hlookup (hconst_list ctx) (EL n nms) = NONE /\ htype_ok (htype_list ctx) (EL y tys)
     ==> holr_step (ctx,nms,tys,tms,ths,drops,pol) (RNewConstant n y)
                   (CONS (HNewConst (EL n nms) (EL y tys)) ctx,nms,tys,tms,ths,drops,pol)) /\
  (!ctx nms tys tms ths drops pol t.
     holr_ops_live (ctx,nms,tys,tms,ths,drops,pol) (RNewAxiom t) /\
     holr_axiom_ok pol ctx (EL t tms) /\
     htheory_ok (hthyof ctx) /\ hterm_ok (hsigof ctx) (EL t tms) /\
     EL t tms hhas_type HBool
     ==> holr_step (ctx,nms,tys,tms,ths,drops,pol) (RNewAxiom t)
                   (CONS (HNewAxiom (EL t tms)) ctx,nms,tys,tms,
                    APPEND ths [([],EL t tms)],drops,pol)) /\
  (!ctx nms tys tms ths drops pol t c ty r.
     holr_ops_live (ctx,nms,tys,tms,ths,drops,pol) (RNewDefinition t) /\
     EL t tms = (TmVar c ty =:= r) /\ htheory_ok (hthyof ctx) /\
     hterm_ok (hsigof ctx) (TmVar c ty =:= r) /\ hlookup (hconst_list ctx) c = NONE /\
     HCLOSED r /\ (!v. MEM v (htvars r) ==> MEM v (htyvars ty))
     ==> holr_step (ctx,nms,tys,tms,ths,drops,pol) (RNewDefinition t)
                   (CONS (HConstSpec [c,r] (TmVar c ty =:= r)) ctx,nms,tys,tms,
                    APPEND ths [([],TmConst c ty =:= r)],drops,pol)) /\
  (!ctx nms tys tms ths drops pol n a r h c P x params t1 t2.
     holr_ops_live (ctx,nms,tys,tms,ths,drops,pol) (RNewTypedef n a r h) /\
     n < LENGTH nms /\ a < LENGTH nms /\ r < LENGTH nms /\
     EL h ths = ([],c) /\ HACONV c (TmComb P x) /\ hwelltyped (TmComb P x) /\
     htheory_ok (hthyof ctx) /\ HCLOSED P /\
     hlookup (htype_list ctx) (EL n nms) = NONE /\
     hlookup (hconst_list ctx) (EL a nms) = NONE /\
     hlookup (hconst_list ctx) (EL r nms) = NONE /\ ~(EL a nms = EL r nms) /\
     hstring_sorted params /\ (!v. MEM v params <=> MEM v (htvars P)) /\
     hproves (hthyof (CONS (HTypeDefn (EL n nms) P (EL a nms) (EL r nms)) ctx)) [] t1 /\
     hproves (hthyof (CONS (HTypeDefn (EL n nms) P (EL a nms) (EL r nms)) ctx)) [] t2
     ==> holr_step (ctx,nms,tys,tms,ths,drops,pol) (RNewTypedef n a r h)
                   (CONS (HTypeDefn (EL n nms) P (EL a nms) (EL r nms)) ctx,nms,tys,tms,
                    APPEND ths [([],t1); ([],t2)],drops,pol)) /\
  (!ctx nms tys tms ths drops pol p.
     p <= 2
     ==> holr_step (ctx,nms,tys,tms,ths,drops,pol) (RPolicy p)
                   (ctx,nms,tys,tms,ths,drops,MAX pol p)) /\
  (!ctx nms tys tms ths drops pol h hs c.
     holr_ops_live (ctx,nms,tys,tms,ths,drops,pol) (RExpectAlpha h hs c) /\
     hproves (hthyof ctx) (MAP (\i. EL i tms) hs) (EL c tms)
     ==> holr_step (ctx,nms,tys,tms,ths,drops,pol) (RExpectAlpha h hs c)
                   (ctx,nms,tys,tms,ths,drops,pol)) /\
  (!ctx nms tys tms ths drops pol h n.
     holr_ops_live (ctx,nms,tys,tms,ths,drops,pol) (RLabel h n) /\ n < LENGTH nms
     ==> holr_step (ctx,nms,tys,tms,ths,drops,pol) (RLabel h n)
                   (ctx,nms,tys,tms,ths,drops,pol)) /\
  (!ctx nms tys tms ths drops pol h.
     holr_ops_live (ctx,nms,tys,tms,ths,drops,pol) (REmit h)
     ==> holr_step (ctx,nms,tys,tms,ths,drops,pol) (REmit h)
                   (ctx,nms,tys,tms,ths,drops,pol)) /\
  (!ctx nms tys tms ths drops pol y.
     holr_ops_live (ctx,nms,tys,tms,ths,drops,pol) (RDropType y)
     ==> holr_step (ctx,nms,tys,tms,ths,drops,pol) (RDropType y)
                   (ctx,nms,tys,tms,ths,CONS (1,y) drops,pol)) /\
  (!ctx nms tys tms ths drops pol t.
     holr_ops_live (ctx,nms,tys,tms,ths,drops,pol) (RDropTerm t)
     ==> holr_step (ctx,nms,tys,tms,ths,drops,pol) (RDropTerm t)
                   (ctx,nms,tys,tms,ths,CONS (2,t) drops,pol)) /\
  (!ctx nms tys tms ths drops pol h.
     holr_ops_live (ctx,nms,tys,tms,ths,drops,pol) (RDropThm h)
     ==> holr_step (ctx,nms,tys,tms,ths,drops,pol) (RDropThm h)
                   (ctx,nms,tys,tms,ths,CONS (3,h) drops,pol))`;;

(* A stream is accepted under the host's policy floor hpol when it is the  *)
(* encoding of records in strict mode (flags 0) under a header policy, and  *)
(* the records run from the initial state at the larger of the two.        *)
let holr_accepts = new_definition
 `holr_accepts hpol (bytes:num list) <=>
    ?pol recs s. pol <= 2 /\ bytes = holr_stream pol 0 recs /\
                 tc_path holr_step recs (hinit_ctxt,[],[],[],[],[],MAX hpol pol) s`;;

(* ------------------------------------------------------------------------- *)
(* Every run keeps the context a valid extension of HOL's initial context,  *)
(* with every theorem entry derivable in it.                                 *)
(* ------------------------------------------------------------------------- *)

let holr_inv = new_definition
 `holr_inv ((ctx,nms,tys,tms,ths,drops,pol):hrstate) <=>
    ctx hextends hinit_ctxt /\ ALL (\(h,c). hproves (hthyof ctx) h c) ths`;;

let HOLR_INV_EXTEND = prove
 (`!ctx ctx' ths.
      ctx' hextends ctx /\ ctx hextends hinit_ctxt /\
      ALL (\(h,c). hproves (hthyof ctx) h c) ths
      ==> ctx' hextends hinit_ctxt /\ ALL (\(h,c). hproves (hthyof ctx') h c) ths`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[HEXTENDS_TRANS]; ALL_TAC] THEN
  MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `\(h,c). hproves (hthyof ctx) h c` THEN
  ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN ASM_MESON_TAC[HEXTENDS_PROVES]);;

let HOLR_NEW_TAC th =
  MATCH_MP_TAC HOLR_INV_EXTEND THEN EXISTS_TAC `ctx:hupdate list` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FIBRE_HUPDATES_EXTENDS THEN
  MATCH_MP_TAC th THEN ASM_REWRITE_TAC[];;

let HOLR_STEP_INV = prove
 (`!s r t. holr_step s r t /\ holr_inv s ==> holr_inv t`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC holr_step_INDUCT THEN REWRITE_TAC[holr_inv] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
  REWRITE_TAC[ALL_APPEND; ALL] THEN TRY(DISCH_THEN STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THENL
   [HOLR_NEW_TAC HOL_NEW_TYPE;
    HOLR_NEW_TAC HOL_NEW_CONSTANT;
    MP_TAC(SPECL [`ctx:hupdate list`; `EL t (tms:holterm list)`] HOL_NEW_AXIOM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOLR_INV_EXTEND THEN EXISTS_TAC `ctx:hupdate list` THEN
    ASM_SIMP_TAC[FIBRE_HUPDATES_EXTENDS];
    MP_TAC(SPECL [`ctx:hupdate list`; `c:string`; `ty:holtype`; `r:holterm`]
                 HOL_NEW_BASIC_DEFINITION) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOLR_INV_EXTEND THEN EXISTS_TAC `ctx:hupdate list` THEN
    ASM_SIMP_TAC[FIBRE_HUPDATES_EXTENDS];
    SUBGOAL_THEN `hproves (hthyof ctx) [] (TmComb P x)` ASSUME_TAC THENL
     [SUBGOAL_THEN `hproves (hthyof ctx) [] c` MP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `holr_ops_live`)) (concl th))) THEN
        REWRITE_TAC[holr_ops_live; holr_operands; holr_live; ALL] THEN STRIP_TAC THEN
        UNDISCH_TAC `ALL (\(h,c). hproves (hthyof ctx) h c) (ths:(holterm list#holterm)list)` THEN
        REWRITE_TAC[GSYM ALL_MEM] THEN
        DISCH_THEN(MP_TAC o SPEC `EL h (ths:(holterm list#holterm)list)`) THEN
        ASM_SIMP_TAC[MEM_EL];
        DISCH_TAC THEN MATCH_MP_TAC HPROVES_ACONV THEN
        MAP_EVERY EXISTS_TAC [`[]:holterm list`; `c:holterm`] THEN
        ASM_REWRITE_TAC[MEM; ALL]];
      ALL_TAC] THEN
    MP_TAC(SPECL [`ctx:hupdate list`; `EL n (nms:string list)`; `EL a (nms:string list)`;
                  `EL r (nms:string list)`; `P:holterm`; `x:holterm`; `params:string list`]
                 HOL_NEW_BASIC_TYPE_DEFINITION) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC HOLR_INV_EXTEND THEN EXISTS_TAC `ctx:hupdate list` THEN
    ASM_SIMP_TAC[FIBRE_HUPDATES_EXTENDS]]);;

let HOLR_RUN_INV = prove
 (`!recs s t. tc_path holr_step recs s t /\ holr_inv s ==> holr_inv t`,
  MATCH_MP_TAC TC_PATH_INVARIANT THEN MESON_TAC[HOLR_STEP_INV]);;

(* An accepted stream's theory is a valid extension of HOL's initial theory, *)
(* and every theorem it made is derivable in it.                             *)
let HOLR_ACCEPTS_THEORY = prove
 (`!hpol bytes. holr_accepts hpol bytes
           ==> ?pol recs ctx nms tys tms ths drops pol'.
                 bytes = holr_stream pol 0 recs /\
                 tc_path holr_step recs (hinit_ctxt,[],[],[],[],[],MAX hpol pol)
                         (ctx,nms,tys,tms,ths,drops,pol') /\
                 ctx hextends hinit_ctxt /\ htheory_ok (hthyof ctx) /\
                 ALL (\(h,c). hproves (hthyof ctx) h c) ths`,
  REPEAT GEN_TAC THEN REWRITE_TAC[holr_accepts; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`pol:num`; `recs:holr_record list`] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`ctx:hupdate list`; `nms:string list`; `tys:holtype list`;
                       `tms:holterm list`; `ths:(holterm list#holterm)list`;
                       `drops:(num#num)list`; `pol':num`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `holr_inv (ctx,nms,tys,tms,ths,drops,pol')` MP_TAC THENL
   [MATCH_MP_TAC HOLR_RUN_INV THEN
    MAP_EVERY EXISTS_TAC [`recs:holr_record list`;
                          `(hinit_ctxt,[],[],[],[],[],MAX hpol pol):hrstate`] THEN
    ASM_REWRITE_TAC[holr_inv; ALL] THEN MESON_TAC[hextends_RULES];
    REWRITE_TAC[holr_inv] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`pol:num`; `recs:holr_record list`; `ctx:hupdate list`;
                          `nms:string list`; `tys:holtype list`; `tms:holterm list`;
                          `ths:(holterm list#holterm)list`; `drops:(num#num)list`;
                          `pol':num`] THEN
    ASM_MESON_TAC[HEXTENDS_THEORY_OK; HINIT_THEORY_OK]]);;

(* ------------------------------------------------------------------------- *)
(* Claims. Along a run the context only extends and the term space only     *)
(* grows, so a claim checked at its record stays derivable at the end.      *)
(* ------------------------------------------------------------------------- *)

let hr_ctx = new_definition
 `hr_ctx ((ctx,nms,tys,tms,ths,drops,pol):hrstate) = ctx`;;

let hr_tms = new_definition
 `hr_tms ((ctx,nms,tys,tms,ths,drops,pol):hrstate) = tms`;;

let HOLR_STEP_TMS = prove
 (`!s r t. holr_step s r t ==> ?more. hr_tms t = APPEND (hr_tms s) more`,
  MATCH_MP_TAC holr_step_INDUCT THEN REWRITE_TAC[hr_tms] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
  MESON_TAC[APPEND_NIL]);;

let HOLR_NEW_EXT_TAC th =
  MATCH_MP_TAC FIBRE_HUPDATES_EXTENDS THEN MATCH_MP_TAC th THEN ASM_REWRITE_TAC[];;

let HOLR_STEP_EXTENDS = prove
 (`!s r t. holr_step s r t /\ holr_inv s ==> hr_ctx t hextends hr_ctx s`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC holr_step_INDUCT THEN REWRITE_TAC[holr_inv; hr_ctx] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
  TRY(DISCH_THEN STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[hextends_RULES] THENL
   [HOLR_NEW_EXT_TAC HOL_NEW_TYPE;
    HOLR_NEW_EXT_TAC HOL_NEW_CONSTANT;
    MP_TAC(SPECL [`ctx:hupdate list`; `EL t (tms:holterm list)`] HOL_NEW_AXIOM) THEN
    ASM_SIMP_TAC[FIBRE_HUPDATES_EXTENDS];
    MP_TAC(SPECL [`ctx:hupdate list`; `c:string`; `ty:holtype`; `r:holterm`]
                 HOL_NEW_BASIC_DEFINITION) THEN
    ASM_SIMP_TAC[FIBRE_HUPDATES_EXTENDS];
    SUBGOAL_THEN `hproves (hthyof ctx) [] (TmComb P x)` ASSUME_TAC THENL
     [SUBGOAL_THEN `hproves (hthyof ctx) [] c` MP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `holr_ops_live`)) (concl th))) THEN
        REWRITE_TAC[holr_ops_live; holr_operands; holr_live; ALL] THEN STRIP_TAC THEN
        UNDISCH_TAC `ALL (\(h,c). hproves (hthyof ctx) h c) (ths:(holterm list#holterm)list)` THEN
        REWRITE_TAC[GSYM ALL_MEM] THEN
        DISCH_THEN(MP_TAC o SPEC `EL h (ths:(holterm list#holterm)list)`) THEN
        ASM_SIMP_TAC[MEM_EL];
        DISCH_TAC THEN MATCH_MP_TAC HPROVES_ACONV THEN
        MAP_EVERY EXISTS_TAC [`[]:holterm list`; `c:holterm`] THEN
        ASM_REWRITE_TAC[MEM; ALL]];
      ALL_TAC] THEN
    MP_TAC(SPECL [`ctx:hupdate list`; `EL n (nms:string list)`; `EL a (nms:string list)`;
                  `EL r (nms:string list)`; `P:holterm`; `x:holterm`; `params:string list`]
                 HOL_NEW_BASIC_TYPE_DEFINITION) THEN
    ASM_SIMP_TAC[FIBRE_HUPDATES_EXTENDS]]);;

let HOLR_RECORD_DISTINCT = distinctness "holr_record";;
let HOLR_RECORD_INJ = injectivity "holr_record";;

let HOLR_STEP_EXPECT = prove
 (`!s hh hs c t. holr_step s (RExpectAlpha hh hs c) t
     ==> t = s /\ c < LENGTH (hr_tms s) /\ ALL (\i. i < LENGTH (hr_tms s)) hs /\
         hproves (hthyof (hr_ctx s)) (MAP (\i. EL i (hr_tms s)) hs) (EL c (hr_tms s))`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[holr_step_CASES] THEN
  REWRITE_TAC[HOLR_RECORD_DISTINCT; HOLR_RECORD_INJ; holr_is_rule; PAIR_EQ] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[hr_ctx; hr_tms] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `holr_ops_live`)) (concl th))) THEN
  ASM_REWRITE_TAC[holr_ops_live; holr_operands; holr_live; ALL] THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[]);;

let HOLR_RUN_CLAIMS = prove
 (`!recs s0 s1. tc_path holr_step recs s0 s1 /\ holr_inv s0
     ==> hr_ctx s1 hextends hr_ctx s0 /\ (?more. hr_tms s1 = APPEND (hr_tms s0) more) /\
         !hh hs c. MEM (RExpectAlpha hh hs c) recs
                   ==> hproves (hthyof (hr_ctx s1)) (MAP (\i. EL i (hr_tms s1)) hs)
                               (EL c (hr_tms s1))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[tc_path; MEM] THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[hextends_RULES] THEN
    MESON_TAC[APPEND_NIL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s0:hrstate`; `s1:hrstate`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:hrstate` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  SUBGOAL_THEN `holr_inv u` ASSUME_TAC THENL [ASM_MESON_TAC[HOLR_STEP_INV]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:hrstate`; `s1:hrstate`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `m1:holterm list`) ASSUME_TAC)) THEN
  SUBGOAL_THEN `hr_ctx u hextends hr_ctx s0` ASSUME_TAC THENL
   [MATCH_MP_TAC HOLR_STEP_EXTENDS THEN EXISTS_TAC `h:holr_record` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`s0:hrstate`; `h:holr_record`; `u:hrstate`] HOLR_STEP_TMS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `m0:holterm list`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HEXTENDS_TRANS THEN EXISTS_TAC `hr_ctx u` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `APPEND (m0:holterm list) m1` THEN ASM_REWRITE_TAC[APPEND_ASSOC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`hh:num`; `hs:num list`; `c:num`] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`hh:num`; `hs:num list`; `c:num`] o
                  check (fun th -> is_forall (concl th))) THEN
    ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HOLR_STEP_EXPECT o
    check (fun th -> can (find_term ((=) `holr_step`)) (concl th) && not (is_forall (concl th)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HEXTENDS_PROVES THEN EXISTS_TAC `hr_ctx s0` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `hr_tms s1 = APPEND (hr_tms s0) m1`] THEN
  SUBGOAL_THEN `MAP (\i. EL i (APPEND (hr_tms s0) m1)) hs = MAP (\i. EL i (hr_tms s0)) hs /\
                EL c (APPEND (hr_tms s0) m1) = EL c (hr_tms s0)`
   (fun th -> REWRITE_TAC[th] THEN FIRST_ASSUM ACCEPT_TAC) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MAP_EQ THEN MATCH_MP_TAC ALL_IMP THEN
    EXISTS_TAC `\i. i < LENGTH (hr_tms s0)` THEN
    CONJ_TAC THENL [SIMP_TAC[EL_APPEND]; FIRST_ASSUM ACCEPT_TAC];
    REWRITE_TAC[EL_APPEND; ASSUME `c < LENGTH (hr_tms s0)`]]);;

(* What acceptance means: the bytes encode records whose theory is a valid  *)
(* extension of HOL's initial theory, and every EXPECT_ALPHA claim of the   *)
(* stream, read with the stream's own terms, is derivable in that theory.  *)
let HOLR_ACCEPTS_CLAIMS = prove
 (`!hpol bytes. holr_accepts hpol bytes
           ==> ?pol recs s. bytes = holr_stream pol 0 recs /\
                            tc_path holr_step recs
                                    (hinit_ctxt,[],[],[],[],[],MAX hpol pol) s /\
                            hr_ctx s hextends hinit_ctxt /\ htheory_ok (hthyof (hr_ctx s)) /\
                            !hh hs c. MEM (RExpectAlpha hh hs c) recs
                                      ==> hproves (hthyof (hr_ctx s))
                                                  (MAP (\i. EL i (hr_tms s)) hs)
                                                  (EL c (hr_tms s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[holr_accepts; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`pol:num`; `recs:holr_record list`; `s:hrstate`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`pol:num`; `recs:holr_record list`; `s:hrstate`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`recs:holr_record list`;
                `(hinit_ctxt,[],[],[],[],[],MAX hpol pol):hrstate`;
                `s:hrstate`] HOLR_RUN_CLAIMS) THEN
  ASM_REWRITE_TAC[holr_inv; ALL; hextends_RULES; hr_ctx] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[HEXTENDS_THEORY_OK; HINIT_THEORY_OK]);;

(* ------------------------------------------------------------------------- *)
(* The policy's law. From STANDARD on, every axiom a run adds is standard   *)
(* in the context it is added to; from SEALED on, none is added. The policy *)
(* never loosens along a run.                                                *)
(* ------------------------------------------------------------------------- *)

let hstd_axioms_ok = new_recursive_definition list_RECURSION
 `(hstd_axioms_ok [] <=> T) /\
  (hstd_axioms_ok (CONS upd rest) <=>
     (!p. upd = HNewAxiom p ==> hstd_axiom rest p) /\ hstd_axioms_ok rest)`;;

let hno_axioms = new_definition
 `hno_axioms ctx <=> !p. ~MEM (HNewAxiom p) ctx`;;

let hr_pol = new_definition
 `hr_pol ((ctx,nms,tys,tms,ths,drops,pol):hrstate) = pol`;;

let hr_ths = new_definition
 `hr_ths ((ctx,nms,tys,tms,ths,drops,pol):hrstate) = ths`;;

let hr_nms = new_definition
 `hr_nms ((ctx,nms,tys,tms,ths,drops,pol):hrstate) = nms`;;

let HINIT_AXIOMS = prove
 (`hstd_axioms_ok hinit_ctxt /\ hno_axioms hinit_ctxt`,
  REWRITE_TAC[hinit_ctxt; hstd_axioms_ok; hno_axioms; MEM; hupdate_DISTINCT]);;

let HOLR_STEP_POLICY_LAW = prove
 (`!s r t. holr_step s r t
           ==> hr_pol s <= hr_pol t /\
               (1 <= hr_pol s /\ hstd_axioms_ok (hr_ctx s) ==> hstd_axioms_ok (hr_ctx t)) /\
               (2 <= hr_pol s /\ hno_axioms (hr_ctx s) ==> hno_axioms (hr_ctx t))`,
  MATCH_MP_TAC holr_step_INDUCT THEN REWRITE_TAC[hr_pol; hr_ctx] THEN
  REWRITE_TAC[hstd_axioms_ok; hno_axioms; MEM; hupdate_DISTINCT; hupdate_INJ;
              LE_REFL; ARITH_RULE `x <= MAX x y`] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN TRY(REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `holr_axiom_ok`)) (concl th))) THEN
  REWRITE_TAC[holr_axiom_ok] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[ARITH_RULE `~(1 <= 0) /\ ~(2 <= 0) /\ ~(2 <= 1)`]);;

let POLICY_CHAIN = prove
 (`!ps pu pt as au at ns nu nt.
      (ps <= pu /\ (1 <= ps /\ as ==> au) /\ (2 <= ps /\ ns ==> nu)) ==>
      (pu <= pt /\ (1 <= pu /\ au ==> at) /\ (2 <= pu /\ nu ==> nt)) ==>
      (ps <= pt /\ (1 <= ps /\ as ==> at) /\ (2 <= ps /\ ns ==> nt))`,
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_ARITH_TAC;
    SUBGOAL_THEN `1 <= pu` ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]];
    SUBGOAL_THEN `2 <= pu` ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]]]);;

let HOLR_RUN_POLICY = prove
 (`!recs s0 s1. tc_path holr_step recs s0 s1
              ==> hr_pol s0 <= hr_pol s1 /\
                  (1 <= hr_pol s0 /\ hstd_axioms_ok (hr_ctx s0) ==> hstd_axioms_ok (hr_ctx s1)) /\
                  (2 <= hr_pol s0 /\ hno_axioms (hr_ctx s0) ==> hno_axioms (hr_ctx s1))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[tc_path] THENL
   [REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN SIMP_TAC[LE_REFL]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `u:hrstate` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:hrstate`; `s1:hrstate`]) THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOLR_STEP_POLICY_LAW) THEN
  MATCH_ACCEPT_TAC POLICY_CHAIN);;

(* ------------------------------------------------------------------------- *)
(* What acceptance delivers. EMIT records deliver theorems and LABEL records *)
(* name them; the delivered sequents are the run's theorem entries at those *)
(* ids (entries are never changed once made, so the final state's entry is  *)
(* the one delivered).                                                       *)
(* ------------------------------------------------------------------------- *)

let holr_emits = new_definition
 `holr_emits recs = MAP (\r. @h. r = REmit h) (FILTER (\r. ?h. r = REmit h) recs)`;;

let holr_labels = new_definition
 `holr_labels recs = MAP (\r. @hn. r = RLabel (FST hn) (SND hn))
                         (FILTER (\r. ?h n. r = RLabel h n) recs)`;;

let holr_delivered = new_definition
 `holr_delivered recs (s:hrstate) = MAP (\h. EL h (hr_ths s)) (holr_emits recs)`;;

let holr_labelled = new_definition
 `holr_labelled recs (s:hrstate) =
    MAP (\hn. EL (SND hn) (hr_nms s),EL (FST hn) (hr_ths s)) (holr_labels recs)`;;

let HOLR_EMIT_SEL = prove
 (`!k. (@h. REmit k = REmit h) = k`,
  GEN_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[HOLR_RECORD_INJ] THEN MESON_TAC[]);;

let HOLR_LABEL_SEL = prove
 (`!k m. (@hn. RLabel k m = RLabel (FST hn) (SND hn)) = (k,m)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  REWRITE_TAC[FORALL_PAIR_THM; HOLR_RECORD_INJ; PAIR_EQ; FST; SND] THEN MESON_TAC[]);;

let MEM_HOLR_EMITS = prove
 (`!recs h. MEM h (holr_emits recs) <=> MEM (REmit h) recs`,
  REWRITE_TAC[holr_emits; MEM_MAP; MEM_FILTER] THEN MESON_TAC[HOLR_EMIT_SEL]);;

let MEM_HOLR_LABELS = prove
 (`!recs h n. MEM (h,n) (holr_labels recs) <=> MEM (RLabel h n) recs`,
  REWRITE_TAC[holr_labels; MEM_MAP; MEM_FILTER] THEN MESON_TAC[HOLR_LABEL_SEL; PAIR_EQ]);;

let HOLR_STEP_GROWS = prove
 (`!s r t. holr_step s r t
           ==> (?m. hr_ths t = APPEND (hr_ths s) m) /\ (?m. hr_nms t = APPEND (hr_nms s) m)`,
  MATCH_MP_TAC holr_step_INDUCT THEN REWRITE_TAC[hr_ths; hr_nms] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
  MESON_TAC[APPEND_NIL; APPEND]);;

let HOLR_STEP_DELIVERS = prove
 (`(!s h t. holr_step s (REmit h) t ==> h < LENGTH (hr_ths s)) /\
   (!s h n t. holr_step s (RLabel h n) t ==> h < LENGTH (hr_ths s) /\ n < LENGTH (hr_nms s))`,
  REWRITE_TAC[FORALL_PAIR_THM; hr_ths; hr_nms] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[holr_step_CASES] THEN
  REWRITE_TAC[HOLR_RECORD_DISTINCT; HOLR_RECORD_INJ; holr_is_rule; PAIR_EQ] THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[holr_ops_live; holr_operands; holr_live; ALL]) THEN
  ASM_MESON_TAC[]);;

let APPEND_EL_PREFIX = prove
 (`!(l:A list) m i. i < LENGTH l ==> i < LENGTH (APPEND l m) /\ EL i (APPEND l m) = EL i l`,
  SIMP_TAC[LENGTH_APPEND; EL_APPEND] THEN ARITH_TAC);;

let HOLR_RUN_DELIVERS = prove
 (`!recs s0 s1. tc_path holr_step recs s0 s1
              ==> (?m. hr_ths s1 = APPEND (hr_ths s0) m) /\
                  (?m. hr_nms s1 = APPEND (hr_nms s0) m) /\
                  (!h. MEM (REmit h) recs ==> h < LENGTH (hr_ths s1)) /\
                  (!h n. MEM (RLabel h n) recs
                         ==> h < LENGTH (hr_ths s1) /\ n < LENGTH (hr_nms s1))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[tc_path; MEM] THENL
   [REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN MESON_TAC[APPEND_NIL]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `u:hrstate` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:hrstate`; `s1:hrstate`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `m1:(holterm list#holterm)list`)
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `n1:string list`) STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(CONJUNCTS_THEN2 (X_CHOOSE_TAC `m0:(holterm list#holterm)list`)
                              (X_CHOOSE_TAC `n0:string list`) o MATCH_MP HOLR_STEP_GROWS) THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `APPEND (m0:(holterm list#holterm)list) m1` THEN
    ASM_REWRITE_TAC[APPEND_ASSOC];
    EXISTS_TAC `APPEND (n0:string list) n1` THEN ASM_REWRITE_TAC[APPEND_ASSOC];
    X_GEN_TAC `k:num` THEN
    DISCH_THEN(DISJ_CASES_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP (CONJUNCT1 HOLR_STEP_DELIVERS) o
        check (fun th -> can (term_match [] `holr_step s (REmit k) u`) (concl th))) THEN
      ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC;
      ASM_MESON_TAC[]];
    MAP_EVERY X_GEN_TAC [`k:num`; `j:num`] THEN
    DISCH_THEN(DISJ_CASES_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP (CONJUNCT2 HOLR_STEP_DELIVERS) o
        check (fun th -> can (term_match [] `holr_step s (RLabel k j) u`) (concl th))) THEN
      ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC;
      ASM_MESON_TAC[]]]);;

let HOLR_INV_THS = prove
 (`!s. holr_inv s ==> hr_ctx s hextends hinit_ctxt /\
                      ALL (\(h,c). hproves (hthyof (hr_ctx s)) h c) (hr_ths s)`,
  REWRITE_TAC[FORALL_PAIR_THM; holr_inv; hr_ctx; hr_ths]);;

(* Every delivered and every labelled sequent is derivable in the theory. *)
let HOLR_RUN_DELIVERED = prove
 (`!recs s t. tc_path holr_step recs s t /\ holr_inv s
              ==> ALL (\(h,c). hproves (hthyof (hr_ctx t)) h c) (holr_delivered recs t) /\
                  ALL (\(n,th). hproves (hthyof (hr_ctx t)) (FST th) (SND th))
                      (holr_labelled recs t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `holr_inv t` (STRIP_ASSUME_TAC o MATCH_MP HOLR_INV_THS) THENL
   [ASM_MESON_TAC[HOLR_RUN_INV]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOLR_RUN_DELIVERS) THEN
  SUBGOAL_THEN
   `!k. k < LENGTH (hr_ths t)
        ==> hproves (hthyof (hr_ctx t)) (FST (EL k (hr_ths t))) (SND (EL k (hr_ths t)))`
    ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\(h,c). hproves (hthyof (hr_ctx t)) h c) (hr_ths t)` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `EL k (hr_ths t)`) THEN
    ANTS_TAC THENL [MATCH_MP_TAC MEM_EL THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SPEC_TAC(`EL k (hr_ths t)`,`q:holterm list#holterm`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; FST; SND];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM ALL_MEM; holr_delivered; holr_labelled; MEM_MAP; LEFT_IMP_EXISTS_THM] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`p:holterm list#holterm`; `k:num`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM PAIR] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[MEM_HOLR_EMITS];
    MAP_EVERY X_GEN_TAC [`p:string#holterm list#holterm`; `hn:num#num`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[MEM_HOLR_LABELS; PAIR]]);;

(* ------------------------------------------------------------------------- *)
(* Acceptance against a host's specification (in the manner of MM0's      *)
(* specification input): the host supplies one expected sequent per EMIT,  *)
(* in order. A delivered sequent entails an expected one when their         *)
(* conclusions are alpha-equivalent and each delivered hypothesis is alpha- *)
(* equivalent to an expected one; the expected sequent must be well formed  *)
(* in the stream's final theory. Then every expected sequent is derivable. *)
(* The specification also lists the declarations its statements rely on;   *)
(* every name it mentions must be standard in the stream's theory or       *)
(* declared there as the specification declares it (holr_spec_pinned).    *)
(* ------------------------------------------------------------------------- *)

let holr_entails = new_definition
 `holr_entails ((h,c):holterm list#holterm) ((h',c'):holterm list#holterm) <=>
    HACONV c c' /\ (!x. MEM x h ==> ?y. MEM y h' /\ HACONV x y)`;;

let holr_spec_ok = new_definition
 `holr_spec_ok ctx ((h',c'):holterm list#holterm) <=>
    hterm_ok (hsigof ctx) c' /\ ALL (\p. hterm_ok (hsigof ctx) p /\ p hhas_type HBool) h'`;;

(* ------------------------------------------------------------------------- *)
(* The names a host specification relies on. In the manner of MM0, the     *)
(* specification, not the proof, fixes what its statements mean: besides   *)
(* the expected sequents it lists the declarations they rely on, as        *)
(* updates: a definition (name, type and body, up to alpha), a type        *)
(* definition (its predicate up to alpha, and its names), or an opaque     *)
(* constant or type. The stream's event for a name matches a declaration   *)
(* when it is that declaration, up to alpha.                                *)
(* ------------------------------------------------------------------------- *)

let hdecl_match = define
 `(hdecl_match (HConstSpec eqs prop) u <=>
     ?c r r'. eqs = [c,r] /\ u = HConstSpec [c,r'] (TmVar c (htypeof r') =:= r') /\
              htypeof r' = htypeof r /\ HACONV r r') /\
  (hdecl_match (HTypeDefn n p a rn) u <=> ?p'. u = HTypeDefn n p' a rn /\ HACONV p p') /\
  (hdecl_match (HNewConst c ty) u <=> u = HNewConst c ty) /\
  (hdecl_match (HNewType n k) u <=> u = HNewType n k) /\
  (hdecl_match (HNewAxiom p) u <=> F)`;;

(* A constant or type operator name is pinned in the stream's final context *)
(* when it is standard there, or the specification declares it and the      *)
(* stream's event declaring it matches that declaration.                    *)
let holr_cpinned = new_definition
 `holr_cpinned decls ctx x <=>
    FST(hstd_decls ctx) x \/
    ?d u. MEM d decls /\ MEM x (MAP FST (hconsts_of_upd d)) /\
          MEM u ctx /\ MEM x (MAP FST (hconsts_of_upd u)) /\ hdecl_match d u`;;

let holr_tpinned = new_definition
 `holr_tpinned decls ctx n <=>
    SND(hstd_decls ctx) n \/
    ?d u. MEM d decls /\ MEM n (MAP FST (htypes_of_upd d)) /\
          MEM u ctx /\ MEM n (MAP FST (htypes_of_upd u)) /\ hdecl_match d u`;;

let holr_pinned = new_definition
 `holr_pinned decls ctx t <=>
    ALL (holr_cpinned decls ctx) (htm_consts t) /\ ALL (holr_tpinned decls ctx) (htm_tyops t)`;;

(* The terms a declaration mentions: a definition's body, a type            *)
(* definition's predicate, an opaque constant's type.                       *)
let hdecl_terms = define
 `(hdecl_terms (HConstSpec eqs prop) = MAP SND eqs) /\
  (hdecl_terms (HTypeDefn n p a rn) = [p]) /\
  (hdecl_terms (HNewConst c ty) = [TmVar c ty]) /\
  (hdecl_terms (HNewType n k) = []) /\
  (hdecl_terms (HNewAxiom p) = [p])`;;

(* Every name the specification mentions, in its sequents and in its        *)
(* declarations, is pinned: the specification is closed under the names    *)
(* its declarations use.                                                    *)
let holr_spec_pinned = new_definition
 `holr_spec_pinned decls (spec:(holterm list#holterm)list) ctx <=>
    ALL (\(h,c). ALL (holr_pinned decls ctx) (CONS c h)) spec /\
    ALL (\d. ALL (holr_pinned decls ctx) (hdecl_terms d)) decls`;;

(* The axioms the specification allows (MM0's axiom declarations): every   *)
(* axiom of the stream's theory is one of them, up to alpha, at any policy, *)
(* and their names are pinned as the specification's other terms are.      *)
let holr_axioms_allowed = new_definition
 `holr_axioms_allowed decls axs ctx <=>
    (!p. MEM (HNewAxiom p) ctx ==> ?a. MEM a axs /\ HACONV p a) /\
    ALL (holr_pinned decls ctx) axs`;;

let holr_accepts_spec = new_definition
 `holr_accepts_spec hpol decls axs spec (bytes:num list) <=>
    ?pol recs s. pol <= 2 /\ bytes = holr_stream pol 0 recs /\
                 tc_path holr_step recs (hinit_ctxt,[],[],[],[],[],MAX hpol pol) s /\
                 ALL2 holr_entails (holr_delivered recs s) spec /\
                 ALL (holr_spec_ok (hr_ctx s)) spec /\
                 holr_spec_pinned decls spec (hr_ctx s) /\
                 holr_axioms_allowed decls axs (hr_ctx s)`;;

let HOLR_ENTAILS_PROVES = prove
 (`!ctx h c h' c'. hproves (hthyof ctx) h c /\ holr_entails (h,c) (h',c') /\
                   holr_spec_ok ctx (h',c') ==> hproves (hthyof ctx) h' c'`,
  REWRITE_TAC[holr_entails; holr_spec_ok] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HPROVES_ACONV THEN MAP_EVERY EXISTS_TAC [`h:holterm list`; `c:holterm`] THEN
  ASM_REWRITE_TAC[HTHYOF_SIG] THEN ASM_MESON_TAC[HTERM_OK_WELLTYPED]);;

let ALL2_ENTAILS_PROVES = prove
 (`!ctx ds sp. ALL (\(h,c). hproves (hthyof ctx) h c) ds /\ ALL2 holr_entails ds sp /\
               ALL (holr_spec_ok ctx) sp
               ==> ALL (\(h,c). hproves (hthyof ctx) h c) sp`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; ALL2] THEN
  MAP_EVERY (fun v -> SPEC_TAC(v,v)) [`h':holterm list#holterm`; `h:holterm list#holterm`] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOLR_ENTAILS_PROVES THEN
    MAP_EVERY EXISTS_TAC [`p1:holterm list`; `p2:holterm`] THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* What acceptance means, in full: the bytes encode records; their theory   *)
(* is a valid extension of HOL's initial theory; under STANDARD its axioms  *)
(* are standard, under SEALED it has none; every EXPECT_ALPHA claim, and   *)
(* every delivered and labelled theorem, is derivable in it.                *)
(* ------------------------------------------------------------------------- *)

let HOLR_ACCEPTS_MEANING = prove
 (`!hpol bytes. holr_accepts hpol bytes
      ==> ?pol recs s.
            bytes = holr_stream pol 0 recs /\
            tc_path holr_step recs (hinit_ctxt,[],[],[],[],[],MAX hpol pol) s /\
            hr_ctx s hextends hinit_ctxt /\ htheory_ok (hthyof (hr_ctx s)) /\
            (1 <= MAX hpol pol ==> hstd_axioms_ok (hr_ctx s)) /\
            (2 <= MAX hpol pol ==> hno_axioms (hr_ctx s)) /\
            (!hh hs c. MEM (RExpectAlpha hh hs c) recs
                       ==> hproves (hthyof (hr_ctx s)) (MAP (\i. EL i (hr_tms s)) hs)
                                   (EL c (hr_tms s))) /\
            ALL (\(h,c). hproves (hthyof (hr_ctx s)) h c) (holr_delivered recs s) /\
            ALL (\(n,th). hproves (hthyof (hr_ctx s)) (FST th) (SND th))
                (holr_labelled recs s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOLR_ACCEPTS_CLAIMS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `pol:num` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `recs:holr_record list` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:hrstate` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `holr_inv (hinit_ctxt,[],[],[],[],[],MAX hpol pol)` ASSUME_TAC THENL
   [REWRITE_TAC[holr_inv; ALL; hextends_RULES]; ALL_TAC] THEN
  MP_TAC(SPECL [`recs:holr_record list`;
                `(hinit_ctxt,[],[],[],[],[],MAX hpol pol):hrstate`; `s:hrstate`]
               HOLR_RUN_POLICY) THEN
  MP_TAC(SPECL [`recs:holr_record list`;
                `(hinit_ctxt,[],[],[],[],[],MAX hpol pol):hrstate`; `s:hrstate`]
               HOLR_RUN_DELIVERED) THEN
  ASM_REWRITE_TAC[hr_pol; hr_ctx; HINIT_AXIOMS] THEN SIMP_TAC[]);;

let HOLR_ACCEPTS_SPEC = prove
 (`!hpol decls axs spec bytes. holr_accepts_spec hpol decls axs spec bytes
      ==> holr_accepts hpol bytes /\
          ?pol recs s.
            bytes = holr_stream pol 0 recs /\
            tc_path holr_step recs (hinit_ctxt,[],[],[],[],[],MAX hpol pol) s /\
            hr_ctx s hextends hinit_ctxt /\ htheory_ok (hthyof (hr_ctx s)) /\
            (1 <= MAX hpol pol ==> hstd_axioms_ok (hr_ctx s)) /\
            (2 <= MAX hpol pol ==> hno_axioms (hr_ctx s)) /\
            holr_spec_pinned decls spec (hr_ctx s) /\
            holr_axioms_allowed decls axs (hr_ctx s) /\
            ALL (\(h,c). hproves (hthyof (hr_ctx s)) h c) spec`,
  REPEAT GEN_TAC THEN REWRITE_TAC[holr_accepts_spec; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`pol:num`; `recs:holr_record list`; `s:hrstate`] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[holr_accepts] THEN
    MAP_EVERY EXISTS_TAC [`pol:num`; `recs:holr_record list`; `s:hrstate`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`pol:num`; `recs:holr_record list`; `s:hrstate`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `holr_inv (hinit_ctxt,[],[],[],[],[],MAX hpol pol)` ASSUME_TAC THENL
   [REWRITE_TAC[holr_inv; ALL; hextends_RULES]; ALL_TAC] THEN
  SUBGOAL_THEN `holr_inv s` (STRIP_ASSUME_TAC o MATCH_MP HOLR_INV_THS) THENL
   [ASM_MESON_TAC[HOLR_RUN_INV]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[HEXTENDS_THEORY_OK; HINIT_THEORY_OK];
    MP_TAC(SPECL [`recs:holr_record list`;
                  `(hinit_ctxt,[],[],[],[],[],MAX hpol pol):hrstate`; `s:hrstate`]
                 HOLR_RUN_POLICY) THEN
    ASM_REWRITE_TAC[hr_pol; hr_ctx; HINIT_AXIOMS] THEN MESON_TAC[];
    MP_TAC(SPECL [`recs:holr_record list`;
                  `(hinit_ctxt,[],[],[],[],[],MAX hpol pol):hrstate`; `s:hrstate`]
                 HOLR_RUN_POLICY) THEN
    ASM_REWRITE_TAC[hr_pol; hr_ctx; HINIT_AXIOMS] THEN MESON_TAC[];
    MATCH_MP_TAC ALL2_ENTAILS_PROVES THEN
    EXISTS_TAC `holr_delivered recs s` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`recs:holr_record list`;
                  `(hinit_ctxt,[],[],[],[],[],MAX hpol pol):hrstate`; `s:hrstate`]
                 HOLR_RUN_DELIVERED) THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A stream decodes uniquely: equal streams have equal policies, flags and  *)
(* records. Each encoding is a prefix code: LEB128, the operand lists, each *)
(* record (its first byte, the opcode, names the kind, never 127), and the  *)
(* record sequence up to END's 127.                                         *)
(* ------------------------------------------------------------------------- *)

let APPEND_SAME_LENGTH = prove
 (`!(a:A list) b x y. LENGTH a = LENGTH b /\ APPEND a x = APPEND b y ==> a = b /\ x = y`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; APPEND; NOT_SUC; GSYM NOT_SUC; SUC_INJ; CONS_11] THEN
  ASM_MESON_TAC[]);;

let APPEND_LCANCEL_EQ = prove
 (`!(l:A list) x y. APPEND l x = APPEND l y <=> x = y`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; CONS_11]);;

let LEB_ENC_PREFIX = prove
 (`!v w x y. APPEND (leb_enc v) x = APPEND (leb_enc w) y ==> v = w /\ x = y`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `v:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`w:num`; `x:num list`; `y:num list`] THEN
  ONCE_REWRITE_TAC[leb_enc_def] THEN
  ASM_CASES_TAC `v < 128` THEN ASM_CASES_TAC `w < 128` THEN
  ASM_REWRITE_TAC[APPEND; CONS_11] THENL
   [STRIP_TAC THEN SUBGOAL_THEN `F` CONTR_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN SUBGOAL_THEN `F` CONTR_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v DIV 128`) THEN
  ANTS_TAC THENL
   [MP_TAC(SPECL [`v:num`; `128`] DIVISION) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`w DIV 128`; `x:num list`; `y:num list`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`v:num`; `128`] DIVISION) THEN MP_TAC(SPECL [`w:num`; `128`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN ASM_ARITH_TAC);;

let HOLR_FLAT_CONS = prove
 (`!(a:num list) l. holr_flat (CONS a l) = APPEND a (holr_flat l)`,
  REWRITE_TAC[holr_flat; ITLIST]);;

let HOLR_FLAT_NIL = prove
 (`holr_flat [] = []`,
  REWRITE_TAC[holr_flat; ITLIST]);;

let FLAT_LEBS_PREFIX = prove
 (`!l l' x y. LENGTH l = LENGTH l' /\
              APPEND (holr_flat (MAP leb_enc l)) x = APPEND (holr_flat (MAP leb_enc l')) y
              ==> l = l' /\ x = y`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; MAP; NOT_SUC; GSYM NOT_SUC; SUC_INJ; CONS_11] THEN
  REWRITE_TAC[holr_flat; ITLIST; APPEND] THEN
  REWRITE_TAC[GSYM holr_flat; GSYM APPEND_ASSOC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LEB_ENC_PREFIX) THEN
  ASM_MESON_TAC[]);;

let IDS_PREFIX = prove
 (`!l l' x y. APPEND (holr_ids l) x = APPEND (holr_ids l') y ==> l = l' /\ x = y`,
  REWRITE_TAC[holr_ids; GSYM APPEND_ASSOC] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP LEB_ENC_PREFIX) THEN
  MATCH_MP_TAC FLAT_LEBS_PREFIX THEN ASM_REWRITE_TAC[]);;

let FLAT_PAIRS_PREFIX = prove
 (`!l l' x y.
     LENGTH l = LENGTH l' /\
     APPEND (holr_flat (MAP (\(a,b). APPEND (leb_enc a) (leb_enc b)) l)) x =
     APPEND (holr_flat (MAP (\(a,b). APPEND (leb_enc a) (leb_enc b)) l')) y
     ==> l = l' /\ x = y`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; MAP; NOT_SUC; GSYM NOT_SUC; SUC_INJ; CONS_11; HOLR_FLAT_CONS;
              HOLR_FLAT_NIL; APPEND] THEN
  MAP_EVERY (fun v -> SPEC_TAC(v,v)) [`h':num#num`; `h:num#num`] THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LEB_ENC_PREFIX) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LEB_ENC_PREFIX) THEN
  ASM_MESON_TAC[]);;

let PAIRS_PREFIX = prove
 (`!l l' x y. APPEND (holr_pairs l) x = APPEND (holr_pairs l') y ==> l = l' /\ x = y`,
  REWRITE_TAC[holr_pairs; GSYM APPEND_ASSOC] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP LEB_ENC_PREFIX) THEN
  MATCH_MP_TAC FLAT_PAIRS_PREFIX THEN ASM_REWRITE_TAC[]);;

(* Peel prefix-code equations among the assumptions, then compare fields. *)
let HOLR_PEEL_TAC =
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LEB_ENC_PREFIX) ORELSE
         FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IDS_PREFIX) ORELSE
         FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PAIRS_PREFIX) ORELSE
         FIRST_X_ASSUM(fun th1 -> FIRST_X_ASSUM(fun th2 ->
           STRIP_ASSUME_TAC(MATCH_MP APPEND_SAME_LENGTH (CONJ th1 th2))))) THEN
  ASM_REWRITE_TAC[];;

let HOLR_REC_PREFIX = prove
 (`!r r' x y. APPEND (holr_rec_enc r) x = APPEND (holr_rec_enc r') y ==> r = r' /\ x = y`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `r:holr_record` (cases "holr_record")) THEN
  STRUCT_CASES_TAC(SPEC `r':holr_record` (cases "holr_record")) THEN
  REWRITE_TAC[holr_rec_enc; APPEND; CONS_11; GSYM APPEND_ASSOC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_EQ_CONV) THEN
  REWRITE_TAC[HOLR_RECORD_INJ; HOLR_RECORD_DISTINCT] THEN
  STRIP_TAC THEN HOLR_PEEL_TAC);;

let HOLR_REC_HEAD = prove
 (`!r. ~(holr_rec_enc r = []) /\ ~(HD (holr_rec_enc r) = 127)`,
  GEN_TAC THEN STRUCT_CASES_TAC(SPEC `r:holr_record` (cases "holr_record")) THEN
  REWRITE_TAC[holr_rec_enc; NOT_CONS_NIL; HD] THEN CONV_TAC NUM_REDUCE_CONV);;

let HOLR_RECS_PREFIX = prove
 (`!rs rs' x y. APPEND (holr_flat (MAP holr_rec_enc rs)) (CONS 127 x) =
                APPEND (holr_flat (MAP holr_rec_enc rs')) (CONS 127 y)
                ==> rs = rs' /\ x = y`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; HOLR_FLAT_CONS; HOLR_FLAT_NIL; APPEND; CONS_11; NOT_CONS_NIL] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THENL
   [REPEAT GEN_TAC THEN MP_TAC(SPEC `h:holr_record` HOLR_REC_HEAD) THEN STRIP_TAC THEN
    FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP CONS_HD_TL th]) THEN
    REWRITE_TAC[APPEND; CONS_11] THEN ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN MP_TAC(SPEC `h:holr_record` HOLR_REC_HEAD) THEN STRIP_TAC THEN
    FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP CONS_HD_TL th]) THEN
    REWRITE_TAC[APPEND; CONS_11] THEN ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP HOLR_REC_PREFIX) THEN
    ASM_MESON_TAC[]]);;

let HOLR_STREAM_SHAPE = prove
 (`!p f rs. ?tail.
      holr_stream p f rs =
      APPEND holr_magic (APPEND holr_kernel_id (APPEND (leb_enc 1) (APPEND (leb_enc 0)
        (APPEND (leb_enc p) (APPEND (leb_enc f)
          (APPEND (holr_flat (MAP holr_rec_enc rs)) (CONS 127 tail)))))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[holr_stream] THEN
  GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV o LAND_CONV) [holr_body] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN MESON_TAC[]);;

let HOLR_STREAM_INJ = prove
 (`!p f rs p' f' rs'. holr_stream p f rs = holr_stream p' f' rs'
                      ==> p = p' /\ f = f' /\ rs = rs'`,
  REPEAT GEN_TAC THEN
  X_CHOOSE_THEN `x:num list` SUBST1_TAC (SPECL [`p:num`; `f:num`; `rs:holr_record list`]
                                               HOLR_STREAM_SHAPE) THEN
  X_CHOOSE_THEN `y:num list` SUBST1_TAC (SPECL [`p':num`; `f':num`; `rs':holr_record list`]
                                               HOLR_STREAM_SHAPE) THEN
  REWRITE_TAC[APPEND_LCANCEL_EQ] THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LEB_ENC_PREFIX)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOLR_RECS_PREFIX) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Inverting single steps, for concrete runs.                                *)
(* ------------------------------------------------------------------------- *)

let HOLR_INVERT_TAC =
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[holr_step_CASES] THEN
  REWRITE_TAC[HOLR_RECORD_DISTINCT; HOLR_RECORD_INJ; holr_is_rule; PAIR_EQ] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[];;

let HOLR_INV_NAME = prove
 (`!ctx nms tys tms ths drops pol bs u.
      holr_step (ctx,nms,tys,tms,ths,drops,pol) (RName bs) u
      ==> u = (ctx,APPEND nms [holr_name bs],tys,tms,ths,drops,pol)`,
  HOLR_INVERT_TAC);;

let HOLR_INV_TYAPP = prove
 (`!ctx nms tys tms ths drops pol n ys u.
      holr_step (ctx,nms,tys,tms,ths,drops,pol) (RTyApp n ys) u
      ==> u = (ctx,nms,APPEND tys [TyApp (EL n nms) (MAP (\y. EL y tys) ys)],
               tms,ths,drops,pol)`,
  HOLR_INVERT_TAC);;

let HOLR_INV_NEW_CONSTANT = prove
 (`!ctx nms tys tms ths drops pol n y u.
      holr_step (ctx,nms,tys,tms,ths,drops,pol) (RNewConstant n y) u
      ==> u = (CONS (HNewConst (EL n nms) (EL y tys)) ctx,nms,tys,tms,ths,drops,pol)`,
  HOLR_INVERT_TAC);;

let HOLR_INV_CONST = prove
 (`!ctx nms tys tms ths drops pol n y u.
      holr_step (ctx,nms,tys,tms,ths,drops,pol) (RConst n y) u
      ==> u = (ctx,nms,tys,APPEND tms [TmConst (EL n nms) (EL y tys)],ths,drops,pol)`,
  HOLR_INVERT_TAC);;

let HOLR_INV_VAR = prove
 (`!ctx nms tys tms ths drops pol n y u.
      holr_step (ctx,nms,tys,tms,ths,drops,pol) (RVar n y) u
      ==> u = (ctx,nms,tys,APPEND tms [TmVar (EL n nms) (EL y tys)],ths,drops,pol)`,
  HOLR_INVERT_TAC);;

let HOLR_INV_NEW_AXIOM = prove
 (`!ctx nms tys tms ths drops pol t u.
      holr_step (ctx,nms,tys,tms,ths,drops,pol) (RNewAxiom t) u
      ==> holr_axiom_ok pol ctx (EL t tms)`,
  HOLR_INVERT_TAC);;

(* Every standard axiom is an application. *)
let HACONV_COMB_RIGHT = prove
 (`!p s t. HACONV p (TmComb s t) ==> ?s' t'. p = TmComb s' t'`,
  GEN_TAC THEN STRUCT_CASES_TAC(SPEC `p:holterm` (cases "holterm")) THEN
  REWRITE_TAC[HACONV; HRACONV; holterm_INJ] THEN MESON_TAC[]);;

let HSTD_AXIOMS_COMB = prove
 (`!a. MEM a hstd_axioms ==> ?s t. a = TmComb s t`,
  REWRITE_TAC[hstd_axioms; MEM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[]);;

let HSTD_AXIOM_COMB = prove
 (`!ctx p. hstd_axiom ctx p ==> ?s t. p = TmComb s t`,
  REWRITE_TAC[hstd_axiom] THEN MESON_TAC[HSTD_AXIOMS_COMB; HACONV_COMB_RIGHT]);;

(* Walk a concrete run: replace each successor state by what its record    *)
(* makes, as far as the inversions apply.                                  *)
let HOLR_WALK_TAC =
  let invs = [HOLR_INV_NAME; HOLR_INV_TYAPP; HOLR_INV_NEW_CONSTANT; HOLR_INV_CONST;
              HOLR_INV_VAR] in
  REPEAT(FIRST_X_ASSUM(fun th -> tryfind (fun inv -> SUBST_ALL_TAC(MATCH_MP inv th)) invs));;

(* ------------------------------------------------------------------------- *)
(* Negative controls of the meaning. A stream whose header says STANDARD   *)
(* and which asserts a non-standard axiom is refused under every host floor *)
(* (the floor can only raise the policy):                                    *)
(*   - declare a constant c:bool, assert it as an axiom, and claim |- c;    *)
(*   - assert a boolean variable x as an axiom.                             *)
(* The run is determined up to the axiom, and there the policy refuses: no *)
(* standard axiom is a constant or a variable.                              *)
(* ------------------------------------------------------------------------- *)

let holr_neg_const_axiom = new_definition
 `holr_neg_const_axiom =
    [RName [99]; RName [98;111;111;108]; RTyApp 1 []; RNewConstant 0 0;
     RConst 0 0; RNewAxiom 0; RExpectAlpha 0 [] 0]`;;

let holr_neg_var_axiom = new_definition
 `holr_neg_var_axiom =
    [RName [98;111;111;108]; RTyApp 0 []; RName [120]; RVar 1 0; RNewAxiom 0]`;;

let holr_mentions name th =
  can (find_term (fun t -> is_const t && fst(dest_const t) = name)) (concl th);;

let HOLR_NEG_TAC def =
  GEN_TAC THEN REWRITE_TAC[holr_accepts; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`pol:num`; `recs:holr_record list`; `s:hrstate`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOLR_STREAM_INJ o
                check (fun th -> can (term_match [] `holr_stream a b c = d`) (concl th))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
                       check (fun th -> is_var(rand(concl th))))) THEN
  FIRST_X_ASSUM(MP_TAC o check (holr_mentions "tc_path")) THEN
  REWRITE_TAC[def; tc_path] THEN STRIP_TAC THEN
  HOLR_WALK_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HOLR_INV_NEW_AXIOM o check (holr_mentions "RNewAxiom")) THEN
  REWRITE_TAC[holr_axiom_ok; APPEND; EL; HD; ARITH_RULE `~(MAX a 1 = 0)`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HSTD_AXIOM_COMB o CONJUNCT2) THEN
  REWRITE_TAC[holterm_DISTINCT];;

let HOLR_NEG_CONST_AXIOM = prove
 (`!hpol. ~holr_accepts hpol (holr_stream 1 0 holr_neg_const_axiom)`,
  HOLR_NEG_TAC holr_neg_const_axiom);;

let HOLR_NEG_VAR_AXIOM = prove
 (`!hpol. ~holr_accepts hpol (holr_stream 1 0 holr_neg_var_axiom)`,
  HOLR_NEG_TAC holr_neg_var_axiom);;

(* ------------------------------------------------------------------------- *)
(* A positive control of the policy. In HOL Light's standard theory, as     *)
(* CeTTa's STANDARD certifies it (the bootstrap; the nine definitions in    *)
(* order; the constant "@"; the type ind), each of the three standard       *)
(* axioms is standard, so STANDARD admits ETA_AX, SELECT_AX and INFINITY_AX.*)
(* hstd_seq: every declaration of a context is a standard event, given the *)
(* declarations before it; then every name the context declares is         *)
(* standard (HSTD_SEQ_DECLS).                                               *)
(* ------------------------------------------------------------------------- *)

let hstd_seq = new_recursive_definition list_RECURSION
 `(hstd_seq [] <=> T) /\
  (hstd_seq (CONS upd rest) <=>
     (~(hconsts_of_upd upd = []) ==> hstd_upd_c upd (FST(hstd_decls rest)) (SND(hstd_decls rest))) /\
     (~(htypes_of_upd upd = []) ==> hstd_upd_t upd) /\
     hstd_seq rest)`;;

let MEM_MAP_FST_NONNIL = prove
 (`!(l:(A#B)list) x. MEM x (MAP FST l) ==> ~(l = [])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MEM; NOT_CONS_NIL]);;

let HSTD_SEQ_DECLS = prove
 (`!ctx. hstd_seq ctx
         ==> (!c upd. MEM upd ctx /\ MEM c (MAP FST (hconsts_of_upd upd))
                      ==> FST(hstd_decls ctx) c) /\
             (!n upd. MEM upd ctx /\ MEM n (MAP FST (htypes_of_upd upd))
                      ==> SND(hstd_decls ctx) n)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[hstd_seq; MEM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && lhand(concl th) = `hstd_seq t`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[hstd_decls; FST; SND] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_MESON_TAC[MEM_MAP_FST_NONNIL]);;

let hstd_def_upd = new_definition
 `hstd_def_upd ((c,ty,r):string#holtype#holterm) = HConstSpec [c,r] (TmVar c ty =:= r)`;;

let hstd_ctx = new_definition
 `hstd_ctx = APPEND [HNewType "ind" 0; HNewConst "@" hstd_choice_ty]
                    (APPEND (REVERSE (MAP hstd_def_upd hstd_defs)) hinit_ctxt)`;;

(* The name a standard context declares is standard in it. *)
let HSTD_NAME_TAC dc dt =
  FIRST [MATCH_MP_TAC dc; MATCH_MP_TAC dt] THEN
  REWRITE_TAC[MEM; RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2] THEN
  REWRITE_TAC[hconsts_of_upd; htypes_of_upd; MAP] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST; MEM] THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[];;

(* hstd_seq of one more declaration, from hstd_seq of the rest. *)
let hstd_seq_step prev upd =
  let rest = rand(concl prev) in
  let dc,dt = CONJ_PAIR(MATCH_MP HSTD_SEQ_DECLS prev) in
  let goal = mk_comb(`hstd_seq`,
               mk_comb(mk_comb(`CONS:hupdate->hupdate list->hupdate list`,upd),rest)) in
  let c,args = strip_comb upd in
  let spec_tac =
    if fst(dest_const c) = "HConstSpec" then
      let c0,r0 = dest_pair(hd(dest_list(hd args))) in
      MAP_EVERY EXISTS_TAC [c0; r0] THEN REWRITE_TAC[] THEN
      REWRITE_TAC[htypeof; hcodomain; HFun; HBool] THEN
      CONJ_TAC THENL
       [EXISTS_TAC r0 THEN REWRITE_TAC[HACONV_REFL; hstd_defs; MEM]; ALL_TAC] THEN
      REWRITE_TAC[htm_consts; htm_tyops; HTYNAMES_DEF; APPEND; ALL] THEN
      REPEAT CONJ_TAC THEN HSTD_NAME_TAC dc dt
    else ALL_TAC in
  prove(goal,
    ONCE_REWRITE_TAC[hstd_seq] THEN REWRITE_TAC[prev] THEN
    REWRITE_TAC[hconsts_of_upd; htypes_of_upd; MAP; NOT_CONS_NIL] THEN
    REWRITE_TAC[hstd_upd_c; hstd_upd_t; hstd_choice_ty; HFun; HBool] THEN
    CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[] THEN spec_tac);;

let HSTD_CTX_LIST =
  (REWRITE_CONV[hstd_ctx; hstd_defs; MAP; REVERSE; APPEND; hstd_def_upd; hinit_ctxt;
                hstd_choice_ty; HFun; HBool])
  `hstd_ctx`;;

let HSTD_SEQ_CTX =
  let upds = dest_list(rhs(concl HSTD_CTX_LIST)) in
  let base = prove(`hstd_seq []`, REWRITE_TAC[hstd_seq]) in
  let th = itlist (fun u th -> hstd_seq_step th u) upds base in
  REWRITE_RULE[GSYM HSTD_CTX_LIST] th;;

let HSTD_STANDARD_AXIOMS = prove
 (`hstd_seq hstd_ctx /\ ALL (hstd_axiom hstd_ctx) hstd_axioms`,
  let th = REWRITE_RULE[HSTD_CTX_LIST] HSTD_SEQ_CTX in
  let dc,dt = CONJ_PAIR(MATCH_MP HSTD_SEQ_DECLS th) in
  REWRITE_TAC[HSTD_SEQ_CTX] THEN REWRITE_TAC[HSTD_CTX_LIST] THEN
  GEN_REWRITE_TAC (RAND_CONV) [hstd_axioms] THEN REWRITE_TAC[ALL] THEN
  REPEAT CONJ_TAC THEN REWRITE_TAC[hstd_axiom; hstd_term] THEN
  (CONJ_TAC THENL
    [W(fun (_,w) -> EXISTS_TAC (lhand(rand(snd(dest_exists w))))) THEN
     REWRITE_TAC[HACONV_REFL; hstd_axioms; MEM];
     REWRITE_TAC[htm_consts; htm_tyops; HTYNAMES_DEF; APPEND; ALL] THEN
     REPEAT CONJ_TAC THEN HSTD_NAME_TAC dc dt]));;

(* So, in that context, the policy STANDARD admits each standard axiom. *)
let HSTD_STANDARD_ADMITTED = prove
 (`ALL (holr_axiom_ok 1 hstd_ctx) hstd_axioms`,
  MP_TAC(CONJUNCT2 HSTD_STANDARD_AXIOMS) THEN
  MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[holr_axiom_ok] THEN MESON_TAC[]);;

(* ========================================================================= *)
(* The leaves the record plans call (tcalc/native/PLANS.txt), specified as   *)
(* t-ISA programs: what tisa_run of the program does, from any state its    *)
(* entry validation accepts. A leaf's x86 image theorem is the uniform      *)
(* tisa_leaf_spec prog mc pc (driver_leaf.ml), as for fnv, leb128,          *)
(* intern_name and intern16; this file gives the functional half.           *)
(*                                                                           *)
(* Conventions. Frame words: 18 status, 19 payload, 21 receipt, 22 arg0,     *)
(* 23 arg1; registers v1..v5 hold the plan's control words EL 12..16 of the *)
(* step. Region r's word i is pl_w t r i. A declaration (m,n,a) is mode m   *)
(* (1 read-only, 2 read-write), minimum length n, alignment a. Outcomes:    *)
(* FIRED 1, REFUSED 0, UNSUPPORTED 2. No leaf pays fuel: the receipt is     *)
(* unchanged (pl_leaf_ok). A table leaf takes an interned table (16-byte    *)
(* rows k0 = tag + 8a, k1 = b) at regions 0, 1, 2, as intern16 does, so     *)
(* intern_ok, intern_count and intern_word speak of it.                     *)
(* ========================================================================= *)

(* Word i of region r. *)
let pl_w = new_definition
 `pl_w t r i = tisa_read t (word_add (tisa_base t r) (word(8 * i))) 8`;;

(* The rows of an interned table: row i is (k0 MOD 8, k0 DIV 8, k1). *)
let pl_rows3 = new_definition
 `pl_rows3 t r c = list_of_seq (\i. (val(pl_w t r (2 * i)) MOD 8, val(pl_w t r (2 * i)) DIV 8,
                                     val(pl_w t r (2 * i + 1)))) c`;;

(* pl_ids, pl_tyids and pl_cells_new are plans_abs.ml's. *)

(* Every leaf: admitted, its declarations, its status word its code, and no *)
(* fuel paid.                                                               *)
let pl_leaf_ok = new_definition
 `pl_leaf_ok prog decls <=>
    tisa_leaf_wf prog /\ tisa_decls prog = decls /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
            ==> tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21`;;

(* A table leaf keeps the table invariant, the rows below the count, and    *)
(* publishes its rows only when it fires.                                    *)
let pl_table_kept = new_definition
 `pl_table_kept t k u <=>
    (intern_ok t ==> intern_ok u) /\
    val(intern_count t) <= val(intern_count u) /\
    (!i. i < 2 * val(intern_count t) ==> intern_word u i = intern_word t i) /\
    (~(k = 1) ==> intern_count u = intern_count t)`;;

(* ------------------------------------------------------------------------- *)
(* Pure leaves: no regions.                                                  *)
(* ------------------------------------------------------------------------- *)

(* pack: arg0 a, arg1 tag; payload tag + 8a (the packed key word). *)
let pl_pack_spec = new_definition
 `pl_pack_spec prog <=>
    pl_leaf_ok prog [] /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
      ==> if val(tisa_fword t 22) < 2 EXP 60 /\ val(tisa_fword t 23) < 8
          then k = 1 /\ tisa_fword u 19 = word(val(tisa_fword t 23) + 8 * val(tisa_fword t 22))
          else k = 2`;;

(* unpack: arg0 k0, arg1 tag; REFUSED unless k0's tag is tag; payload a.   *)
let pl_unpack_spec = new_definition
 `pl_unpack_spec prog <=>
    pl_leaf_ok prog [] /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
      ==> if val(tisa_fword t 22) MOD 8 = val(tisa_fword t 23)
          then k = 1 /\ tisa_fword u 19 = word(val(tisa_fword t 22) DIV 8)
          else k = 0`;;

(* eqw: REFUSED unless arg0 = arg1; payload arg0. *)
let pl_eqw_spec = new_definition
 `pl_eqw_spec prog <=>
    pl_leaf_ok prog [] /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
      ==> if tisa_fword t 22 = tisa_fword t 23
          then k = 1 /\ tisa_fword u 19 = tisa_fword t 22
          else k = 0`;;

(* pol_max: arg0 the policy, arg1 a record's p; REFUSED unless p <= 2;     *)
(* payload MAX pol p.                                                        *)
let pl_pol_max_spec = new_definition
 `pl_pol_max_spec prog <=>
    pl_leaf_ok prog [] /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
      ==> if val(tisa_fword t 23) <= 2
          then k = 1 /\ tisa_fword u 19 = word(MAX (val(tisa_fword t 22)) (val(tisa_fword t 23)))
          else k = 0`;;

(* ax_ok: arg0 the policy, arg1 an axiom's image; v1..v3 the images of the  *)
(* standard axioms. FIRED under OPEN, or under STANDARD for those three.    *)
let pl_ax_ok_spec = new_definition
 `pl_ax_ok_spec prog <=>
    pl_leaf_ok prog [] /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
      ==> if val(tisa_fword t 22) = 0 \/
             val(tisa_fword t 22) = 1 /\
             (tisa_fword t 23 = tregs t 1 \/ tisa_fword t 23 = tregs t 2 \/ tisa_fword t 23 = tregs t 3)
          then k = 1 /\ tisa_fword u 19 = tisa_fword t 23
          else k = 0`;;

(* ------------------------------------------------------------------------- *)
(* Row tables: rows of s words, a count word.                                *)
(* ------------------------------------------------------------------------- *)

(* row_word: region 0 the rows (read), region 1 the count (read); v1 the    *)
(* stride s; arg0 the row i, arg1 the word w. Payload word w of row i.      *)
let pl_row_word_spec = new_definition
 `pl_row_word_spec prog <=>
    pl_leaf_ok prog [(1,0,8); (1,8,8)] /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
      ==> if val(tisa_fword t 22) < val(pl_w t 1 0) /\ val(tisa_fword t 23) < val(tregs t 1) /\
             8 * val(tregs t 1) * val(pl_w t 1 0) <= val(tisa_len t 0)
          then k = 1 /\
               tisa_fword u 19 = pl_w t 0 (val(tregs t 1) * val(tisa_fword t 22) + val(tisa_fword t 23))
          else k = 2`;;

(* live: region 0 the count (read), region 1 the dropped marks (read, one   *)
(* word per id); arg0 the id. FIRED (payload the id) exactly when the id is *)
(* below the count and not marked.                                          *)
let pl_live_spec = new_definition
 `pl_live_spec prog <=>
    pl_leaf_ok prog [(1,8,8); (1,0,8)] /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
      ==> if 8 * val(pl_w t 0 0) <= val(tisa_len t 1)
          then (if val(tisa_fword t 22) < val(pl_w t 0 0) /\ pl_w t 1 (val(tisa_fword t 22)) = word 0
                then k = 1 /\ tisa_fword u 19 = tisa_fword t 22
                else k = 0)
          else k = 2`;;

(* append_row: region 0 the rows (rw), region 1 the count (rw); v1 the      *)
(* width w (1..5); the row's words arg0, arg1, v2, v3, v4. Payload the new   *)
(* row's index; the rows below it kept.                                     *)
let pl_append_row_spec = new_definition
 `pl_append_row_spec prog <=>
    pl_leaf_ok prog [(2,0,8); (2,8,8)] /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
      ==> if 1 <= val(tregs t 1) /\ val(tregs t 1) <= 5 /\
             8 * val(tregs t 1) * (val(pl_w t 1 0) + 1) <= val(tisa_len t 0)
          then k = 1 /\ tisa_fword u 19 = pl_w t 1 0 /\
               pl_w u 1 0 = word(val(pl_w t 1 0) + 1) /\
               (!j. j < val(tregs t 1)
                    ==> pl_w u 0 (val(tregs t 1) * val(pl_w t 1 0) + j) =
                        EL j [tisa_fword t 22; tisa_fword t 23; tregs t 2; tregs t 3; tregs t 4]) /\
               (!j. j < val(tregs t 1) * val(pl_w t 1 0) ==> pl_w u 0 j = pl_w t 0 j)
          else k = 2 /\ pl_w u 1 0 = pl_w t 1 0 /\
               (!j. 8 * j + 8 <= val(tisa_len t 0) ==> pl_w u 0 j = pl_w t 0 j)`;;

(* put_word: region 0 the table (rw), region 1 its row count (read); v1 the *)
(* stride s, v2 the word w; arg0 the row i, arg1 the value. Word w of row i *)
(* := value; every other word below s * count kept. UNSUPPORTED keeps every *)
(* word inside the table (words past it can be the frame's status word).   *)
let pl_put_word_spec = new_definition
 `pl_put_word_spec prog <=>
    pl_leaf_ok prog [(2,0,8); (1,8,8)] /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
      ==> if val(tisa_fword t 22) < val(pl_w t 1 0) /\ val(tregs t 2) < val(tregs t 1) /\
             8 * val(tregs t 1) * val(pl_w t 1 0) <= val(tisa_len t 0)
          then k = 1 /\ tisa_fword u 19 = tisa_fword t 23 /\
               pl_w u 0 (val(tregs t 1) * val(tisa_fword t 22) + val(tregs t 2)) = tisa_fword t 23 /\
               (!j. j < val(tregs t 1) * val(pl_w t 1 0) /\
                    ~(j = val(tregs t 1) * val(tisa_fword t 22) + val(tregs t 2))
                    ==> pl_w u 0 j = pl_w t 0 j)
          else k = 2 /\ (!j. 8 * j + 8 <= val(tisa_len t 0) ==> pl_w u 0 j = pl_w t 0 j)`;;

(* ------------------------------------------------------------------------- *)
(* Hypothesis lists: sorted (strictly increasing ids), interned cells.      *)
(* ------------------------------------------------------------------------- *)

(* hyps_union: regions 0..2 the de Bruijn table (rw), 3 work (rw); arg0 and  *)
(* arg1 two sorted lists. Payload the sorted list of their union; every row  *)
(* appended is a cell over earlier rows whose element is in the union.      *)
let pl_hyps_union_spec = new_definition
 `pl_hyps_union_spec prog <=>
    pl_leaf_ok prog [(2,16,8); (2,8,8); (2,8,8); (2,256,8)] /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
      ==> pl_table_kept t k u /\ (k = 1 \/ k = 2) /\
          (intern_ok t /\ k = 1
           ==> !I1 I2. pl_ids (pl_rows3 t 0 (val(intern_count t))) (val(tisa_fword t 22)) I1 /\
                       pl_ids (pl_rows3 t 0 (val(intern_count t))) (val(tisa_fword t 23)) I2 /\
                       PAIRWISE (<) I1 /\ PAIRWISE (<) I2
                       ==> (?ids. pl_ids (pl_rows3 u 0 (val(intern_count u))) (val(tisa_fword u 19)) ids /\
                                PAIRWISE (<) ids /\ (!x. MEM x ids <=> MEM x I1 \/ MEM x I2)) /\
                           pl_cells_new 6 (val(intern_count t)) (pl_rows3 u 0 (val(intern_count u)))
                                        (\a. MEM a I1 \/ MEM a I2))`;;

(* hyps_remove: as hyps_union; arg0 a sorted list, arg1 an id x. Payload    *)
(* the sorted list of the elements other than x.                            *)
let pl_hyps_remove_spec = new_definition
 `pl_hyps_remove_spec prog <=>
    pl_leaf_ok prog [(2,16,8); (2,8,8); (2,8,8); (2,256,8)] /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
      ==> pl_table_kept t k u /\ (k = 1 \/ k = 2) /\
          (intern_ok t /\ k = 1
           ==> !ids. pl_ids (pl_rows3 t 0 (val(intern_count t))) (val(tisa_fword t 22)) ids /\
                   PAIRWISE (<) ids
                   ==> (?J. pl_ids (pl_rows3 u 0 (val(intern_count u))) (val(tisa_fword u 19)) J /\
                            PAIRWISE (<) J /\ (!x. MEM x J <=> MEM x ids /\ ~(x = val(tisa_fword t 23)))) /\
                       pl_cells_new 6 (val(intern_count t)) (pl_rows3 u 0 (val(intern_count u)))
                                    (\a. MEM a ids))`;;

(* The operand list: n words of region r from word s. *)
let pl_oplist = new_definition
 `pl_oplist t r s n = list_of_seq (\j. val(pl_w t r (s + j))) n`;;

(* hyps_find: regions 0..2 the de Bruijn table (read), 3 the named term     *)
(* rows (read, 5 words), 4 their count, 5 their dropped marks, 6 the operand *)
(* stack (read), 7 work (rw); arg0 the first operand, arg1 the number n of  *)
(* term ids. FIRED exactly when every term id is live and of type bool (its *)
(* type row is 1) and the sorted list of their images is a list of the      *)
(* table; payload that list. No row is added.                               *)
let pl_hyps_find_spec = new_definition
 `pl_hyps_find_spec prog <=>
    pl_leaf_ok prog [(1,16,8); (1,8,8); (1,8,8); (1,0,8); (1,8,8); (1,0,8); (1,0,8); (2,256,8)] /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u /\ intern_ok t /\
            8 * (val(tisa_fword t 22) + val(tisa_fword t 23)) <= val(tisa_len t 6) /\
            40 * val(pl_w t 4 0) <= val(tisa_len t 3) /\ 8 * val(pl_w t 4 0) <= val(tisa_len t 5)
      ==> let ts = pl_oplist t 6 (val(tisa_fword t 22)) (val(tisa_fword t 23))
          and img = (\x. val(pl_w t 3 (5 * x + 4)))
          and D = pl_rows3 t 0 (val(intern_count t)) in
          if ALL (\x. x < val(pl_w t 4 0) /\ pl_w t 5 x = word 0 /\ pl_w t 3 (5 * x + 3) = word 1) ts /\
             (?L ids. pl_ids D L ids /\ PAIRWISE (<) ids /\ (!x. MEM x ids <=> MEM x (MAP img ts)))
          then k = 1 /\ (?ids. pl_ids D (val(tisa_fword u 19)) ids /\ PAIRWISE (<) ids /\
                            (!x. MEM x ids <=> MEM x (MAP img ts)))
          else k = 0`;;

(* ------------------------------------------------------------------------- *)
(* Walks over decoded rows. nms is any names list under which distinct name  *)
(* rows hold distinct names; tys any type rows; D the rows of regions 0..2.  *)
(* ------------------------------------------------------------------------- *)

(* Names and rows canonical for a walk's claims. *)
let pl_canon_names = new_definition
 `pl_canon_names (nms:string list) <=>
    !a b. a < LENGTH nms /\ b < LENGTH nms /\ EL a nms = EL b nms ==> a = b`;;

let pl_canon_tys = new_definition
 `pl_canon_tys nms (tys:(num#num#num)list) <=>
    !i j ty. fdty nms tys i ty /\ fdty nms tys j ty ==> i = j`;;

(* ty_list: regions 0..2 the type table (rw), 3 the Y map (read), 4 the Y   *)
(* count, 5 the Y dropped marks, 6 the operand stack, 7 work; arg0 the first *)
(* operand, arg1 the number n of Y ids. REFUSED when a Y id is not live;    *)
(* FIRED with the type list row of the ids' type rows, in order.            *)
let pl_ty_list_spec = new_definition
 `pl_ty_list_spec prog <=>
    pl_leaf_ok prog [(2,16,8); (2,8,8); (2,8,8); (1,0,8); (1,8,8); (1,0,8); (1,0,8); (2,256,8)] /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
      ==> pl_table_kept t k u /\
          (intern_ok t /\
           8 * (val(tisa_fword t 22) + val(tisa_fword t 23)) <= val(tisa_len t 6) /\
           8 * val(pl_w t 4 0) <= val(tisa_len t 3) /\ 8 * val(pl_w t 4 0) <= val(tisa_len t 5)
           ==> let ys = pl_oplist t 6 (val(tisa_fword t 22)) (val(tisa_fword t 23)) in
               if ALL (\y. y < val(pl_w t 4 0) /\ pl_w t 5 y = word 0) ys
               then (k = 1 \/ k = 2) /\
                    (k = 1 ==> pl_tyids (pl_rows3 u 0 (val(intern_count u))) (val(tisa_fword u 19))
                                        (MAP (\y. val(pl_w t 3 y)) ys) /\
                               pl_cells_new 3 (val(intern_count t)) (pl_rows3 u 0 (val(intern_count u)))
                                            (\a. MEM a (MAP (\y. val(pl_w t 3 y)) ys)))
               else k = 0)`;;

(* ty_match: regions 0..2 the type table (read), 3 work; arg0 the generic   *)
(* type row g, arg1 the type row y. FIRED exactly when y's type is an       *)
(* instance of g's.                                                          *)
let pl_ty_match_spec = new_definition
 `pl_ty_match_spec prog <=>
    pl_leaf_ok prog [(1,16,8); (1,8,8); (1,8,8); (2,256,8)] /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u /\ intern_ok t
      ==> !nms ty0 ty. pl_canon_names nms /\ pl_canon_tys nms (pl_rows3 t 0 (val(intern_count t))) /\
                       fdty nms (pl_rows3 t 0 (val(intern_count t))) (val(tisa_fword t 22)) ty0 /\
                       fdty nms (pl_rows3 t 0 (val(intern_count t))) (val(tisa_fword t 23)) ty
                       ==> (k = 1 <=> ?tyin. ty = HTYPE_SUBST tyin ty0) /\ (k = 0 \/ k = 1)`;;

(* vfree_hyps: regions 0..2 the de Bruijn table (read), 3 work; arg0 a list *)
(* l, arg1 the name row x, v1 the type row y. FIRED exactly when dbVar(x,y)  *)
(* is free in no element of l.                                              *)
let pl_vfree_hyps_spec = new_definition
 `pl_vfree_hyps_spec prog <=>
    pl_leaf_ok prog [(1,16,8); (1,8,8); (1,8,8); (2,256,8)] /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u /\ intern_ok t
      ==> !nms tys ids ps TY.
            let D = pl_rows3 t 0 (val(intern_count t)) in
            pl_canon_names nms /\ pl_canon_tys nms tys /\
            pl_ids D (val(tisa_fword t 22)) ids /\ ALL2 (fddb nms tys D) ids ps /\
            val(tisa_fword t 23) < LENGTH nms /\ fdty nms tys (val(tregs t 1)) TY
            ==> (k = 1 <=> ALL (\p. ~hdbVFREE_IN (hdbVar (EL (val(tisa_fword t 23)) nms) TY) p) ps) /\
                (k = 0 \/ k = 1)`;;

(* db_closed: regions 0..2 the de Bruijn table (read), 3 work; arg0 a row.  *)
(* FIRED exactly when no dbVar occurs in it.                                 *)
let pl_db_closed_spec = new_definition
 `pl_db_closed_spec prog <=>
    pl_leaf_ok prog [(1,16,8); (1,8,8); (1,8,8); (2,256,8)] /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u /\ intern_ok t
      ==> !nms tys P. fddb nms tys (pl_rows3 t 0 (val(intern_count t))) (val(tisa_fword t 22)) P
                      ==> (k = 1 <=> !x ty. ~hdbVFREE_IN (hdbVar x ty) P) /\ (k = 0 \/ k = 1)`;;

(* ------------------------------------------------------------------------- *)
(* The reader's leaves (PLANS.txt, section 10). Region 0 is the input (read- *)
(* only, alignment 1); region 1 the reader's 16-byte state, word 0 the      *)
(* cursor, an offset into the input.                                         *)
(* ------------------------------------------------------------------------- *)

(* The cursor. *)
let pl_cursor = new_definition
 `pl_cursor t = val(pl_w t 1 0)`;;

(* cur: FIRED with the cursor; the state kept. *)
let pl_cur_spec = new_definition
 `pl_cur_spec prog <=>
    pl_leaf_ok prog [(1,0,1); (1,16,8)] /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
      ==> k = 1 /\ tisa_fword u 19 = pl_w t 1 0`;;

(* leb_next: the minimal LEB128 at the cursor, value below 2^62: FIRED with *)
(* the value and the cursor advanced by its length; otherwise REFUSED with  *)
(* the cursor kept.                                                          *)
let pl_leb_next_spec = new_definition
 `pl_leb_next_spec prog <=>
    pl_leaf_ok prog [(1,0,1); (2,16,8)] /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
      ==> (?v. leb_fires (region_from t 0 (pl_cursor t)) v /\ k = 1 /\ tisa_fword u 19 = word v /\
               pl_w u 1 0 = word(pl_cursor t + LENGTH(leb_enc v))) \/
          ((!v. ~leb_fires (region_from t 0 (pl_cursor t)) v) /\ k = 0 /\ pl_w u 1 0 = pl_w t 1 0)`;;

(* ids_next: region 2 the operand stack (rw). A count n and n values in the *)
(* format's list encoding (holr_ids) at the cursor: FIRED with n, the values *)
(* in stack words 0 .. n - 1, the cursor past the list; UNSUPPORTED when the *)
(* stack is too small; REFUSED when the bytes are no such list.              *)
let pl_ids_next_spec = new_definition
 `pl_ids_next_spec prog <=>
    pl_leaf_ok prog [(1,0,1); (2,16,8); (2,0,8)] /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
      ==> (?l rest. region_from t 0 (pl_cursor t) = APPEND (holr_ids l) rest /\
                    ALL (\x. x < 2 EXP 62) l /\ LENGTH l < 2 EXP 62 /\
                    (8 * LENGTH l <= val(tisa_len t 2)
                     ==> k = 1 /\ tisa_fword u 19 = word(LENGTH l) /\
                         (!j. j < LENGTH l ==> pl_w u 2 j = word(EL j l)) /\
                         pl_w u 1 0 = word(pl_cursor t + LENGTH(holr_ids l))) /\
                    (val(tisa_len t 2) < 8 * LENGTH l ==> k = 2)) \/
          ((!l rest. ALL (\x. x < 2 EXP 62) l /\ LENGTH l < 2 EXP 62
                     ==> ~(region_from t 0 (pl_cursor t) = APPEND (holr_ids l) rest)) /\ k = 0)`;;

(* skip: arg0 n; FIRED with the cursor advanced by n when that stays in the *)
(* input, else REFUSED.                                                      *)
let pl_skip_spec = new_definition
 `pl_skip_spec prog <=>
    pl_leaf_ok prog [(1,0,1); (2,16,8)] /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
      ==> if pl_cursor t + val(tisa_fword t 22) <= val(tisa_len t 0)
          then k = 1 /\ pl_w u 1 0 = word(pl_cursor t + val(tisa_fword t 22)) /\
               tisa_fword u 19 = pl_w u 1 0
          else k = 0`;;

(* le8_next: the 8 bytes at the cursor, little-endian: FIRED with the word  *)
(* they encode and the cursor advanced by 8; REFUSED past the input.        *)
let pl_le8_next_spec = new_definition
 `pl_le8_next_spec prog <=>
    pl_leaf_ok prog [(1,0,1); (2,16,8)] /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
      ==> if pl_cursor t + 8 <= val(tisa_len t 0)
          then k = 1 /\ le8 (tisa_fword u 19) = region_range t 0 (pl_cursor t) 8 /\
               pl_w u 1 0 = word(pl_cursor t + 8)
          else k = 0`;;

(* at_end: FIRED exactly when the cursor is the input's length. *)
let pl_at_end_spec = new_definition
 `pl_at_end_spec prog <=>
    pl_leaf_ok prog [(1,0,1); (1,16,8)] /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
      ==> if pl_cursor t = val(tisa_len t 0) then k = 1 else k = 0`;;

(* const_next: region 2 a constant (read-only); FIRED exactly when the input *)
(* at the cursor holds its bytes, the cursor advanced past them.            *)
let pl_const_next_spec = new_definition
 `pl_const_next_spec prog <=>
    pl_leaf_ok prog [(1,0,1); (2,16,8); (1,0,1)] /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
      ==> if pl_cursor t + val(tisa_len t 2) <= val(tisa_len t 0) /\
             region_range t 0 (pl_cursor t) (val(tisa_len t 2)) = region_range t 2 0 (val(tisa_len t 2))
          then k = 1 /\ pl_w u 1 0 = word(pl_cursor t + val(tisa_len t 2))
          else k = 0`;;

(* inc: arg0 a; FIRED with a + 1 below 2^62, else UNSUPPORTED. *)
let pl_inc_spec = new_definition
 `pl_inc_spec prog <=>
    pl_leaf_ok prog [] /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
      ==> if val(tisa_fword t 22) + 1 < 2 EXP 62
          then k = 1 /\ tisa_fword u 19 = word(val(tisa_fword t 22) + 1)
          else k = 2`;;

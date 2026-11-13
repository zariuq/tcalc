(* ========================================================================= *)
(* Interning of names (byte strings), as the standalone t-ISA p1 program     *)
(* intern_name (tcalc/native/names/intern_name.metta; its text is            *)
(* tcalc/native/names/intern_name_prog.txt, its image record                 *)
(* intern_name.hol).                                                         *)
(*                                                                           *)
(* Regions: 0 input (RO), 1 rows (RW, 16-byte rows (offset, length) into     *)
(* the arena), 2 arena (RW), 3 table (RW, 8-byte slots: 0 empty, id + 1      *)
(* used), 4 header (RW: word 0 the row count, word 1 the arena bytes used).  *)
(* The name is the arg1 bytes of the input from offset arg0 (name_key);     *)
(* entry register v1 is its hash, probing starts there.                      *)
(*                                                                           *)
(* NAME_RUN: every run from a state entry validation accepts ends with       *)
(* name_result: a FIRED run returns an id whose row's bytes, inside the used *)
(* arena, are the name, an earlier row or the row appended at the count,    *)
(* and keeps the rows and arena bytes below the old counts (name_post);     *)
(* every other outcome writes no memory but its status and return words;   *)
(* REFUSED is exactly a name outside the input. None of this depends on the *)
(* table or the hash. Further, when the hash is the name's FNV-1a 64        *)
(* (name_hash), every outcome keeps name_ok, the table's invariant: rows    *)
(* lie in their region and their bytes in the used arena, each row is found *)
(* by probing from its bytes' hash, and no two rows hold one name.          *)
(* NAME_APPEND_ABSENT: a run that appends found no row holding the name, so *)
(* equal names get equal ids (NAME_PRESENT_FOUND).                          *)
(*                                                                           *)
(* The probe loop, the byte comparison and the byte copy are proved with    *)
(* the weakest-precondition generator of tisa_wp.ml and their invariants;   *)
(* the table argument is NAME_OK_APPEND, independent of t-ISA.              *)
(* ========================================================================= *)

needs "native/hol/reader_common.ml";;
needs "native/hol/holr_bytes.ml";;

(* The region facts of five regions: decisions use focused arithmetic (see *)
(* tisa_wp.ml's header); the setting is restored at the end of this file.   *)
let name_saved_arith_focus = !tisa_arith_focus;;
tisa_arith_focus := true;;

(* ------------------------------------------------------------------------- *)
(* The program, as its text intern_name_prog.txt; INTERN_NAME_TERM is that  *)
(* text.                                                                     *)
(* ------------------------------------------------------------------------- *)

let name_copy_body = new_definition
 `name_copy_body = (TSeq (TInstr (TAddr 0 8 11 (SOME 4) 0 (&0:int))) (TSeq (TInstr (TLoad TyU64 1 0 9 8 (&0:int))) (TSeq (TInstr (TAddr 2 8 7 (SOME 4) 0 (&0:int))) (TInstr (TStore 1 2 8 (&0:int) 9)))))`;;

let name_cmp_body = new_definition
 `name_cmp_body = (TSeq (TInstr (TAddr 2 10 7 (SOME 6) 0 (&0:int))) (TSeq (TInstr (TLoad TyU64 1 2 10 10 (&0:int))) (TSeq (TInstr (TAddr 0 11 8 (SOME 6) 0 (&0:int))) (TSeq (TInstr (TLoad TyU64 1 0 11 11 (&0:int))) (TSeq (TInstr (TCmp CondEq TyU64 10 10 (OpReg 11))) (TInstr (TBin BinAnd TyBool 9 9 10)))))))`;;

let name_compare = new_definition
 `name_compare = (TSeq (TInstr (TLoad TyU64 8 1 10 11 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 4 9 8 (&8:int))) (TSeq (TInstr (TCmp CondUlt TyU64 7 9 (OpReg 10))) (TSeq (TIf 7 (TSeq (TInstr (TImm TyU64 7 (word 6))) (TReturn 2 7)) TSkip) (TSeq (TInstr (TBin BinSub TyU64 9 9 10)) (TSeq (TInstr (TCmp CondUlt TyU64 7 9 (OpReg 5))) (TSeq (TIf 7 (TSeq (TInstr (TImm TyU64 7 (word 6))) (TReturn 2 7)) TSkip) (TSeq (TInstr (TLoadFrame TyPtr 7 4)) (TSeq (TInstr (TAddr 2 7 7 (SOME 10) 0 (&0:int))) (TSeq (TInstr (TLoadFrame TyU64 8 22)) (TSeq (TInstr (TLoadFrame TyPtr 9 0)) (TSeq (TInstr (TAddr 0 8 9 (SOME 8) 0 (&0:int))) (TSeq (TInstr (TImm TyBool 9 (word 1))) (TSeq (TCountLoop 6 5 4294967295 name_cmp_body) (TIf 9 (TReturn 1 4) TSkip)))))))))))))))`;;

let name_prologue = new_definition
 `name_prologue = (TSeq (TInstr (TLoadFrame TyU64 4 22)) (TSeq (TInstr (TLoadFrame TyU64 5 23)) (TSeq (TInstr (TLoadFrame TyU64 6 1)) (TSeq (TInstr (TCmp CondUlt TyU64 7 6 (OpReg 4))) (TSeq (TIf 7 (TSeq (TInstr (TImm TyU64 8 (word 1))) (TReturn 0 8)) TSkip) (TSeq (TInstr (TBin BinSub TyU64 6 6 4)) (TSeq (TInstr (TCmp CondUlt TyU64 7 6 (OpReg 5))) (TSeq (TIf 7 (TSeq (TInstr (TImm TyU64 8 (word 1))) (TReturn 0 8)) TSkip) (TSeq (TInstr (TLoadFrame TyPtr 8 8)) (TSeq (TInstr (TLoad TyU64 8 4 9 8 (&0:int))) (TSeq (TInstr (TLoadFrame TyU64 10 3)) (TSeq (TInstr (TShift ShiftRightU TyU64 10 10 4)) (TSeq (TInstr (TCmp CondUlt TyU64 7 10 (OpReg 9))) (TSeq (TIf 7 (TSeq (TInstr (TImm TyU64 9 (word 5))) (TReturn 2 9)) TSkip) (TSeq (TInstr (TLoad TyU64 8 4 9 8 (&8:int))) (TSeq (TInstr (TLoadFrame TyU64 10 5)) (TSeq (TInstr (TCmp CondUlt TyU64 7 10 (OpReg 9))) (TSeq (TIf 7 (TSeq (TInstr (TImm TyU64 9 (word 5))) (TReturn 2 9)) TSkip) (TSeq (TInstr (TLoadFrame TyU64 3 7)) (TInstr (TShift ShiftRightU TyU64 3 3 3)))))))))))))))))))))`;;

let name_row = new_definition
 `name_row = (TSeq (TInstr (TShift ShiftLeft TyU64 10 4 1)) (TSeq (TInstr (TLoadFrame TyPtr 11 2)) (TSeq (TInstr (TAddr 1 11 11 (SOME 10) 3 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 1 10 11 (&8:int))) (TSeq (TInstr (TLoadFrame TyU64 5 23)) (TSeq (TInstr (TCmp CondEq TyU64 7 10 (OpReg 5))) (TIf 7 name_compare TSkip)))))))`;;

let name_append_room = new_definition
 `name_append_room = (TSeq (TInstr (TLoad TyU64 8 4 10 8 (&8:int))) (TSeq (TInstr (TLoadFrame TyU64 5 23)) (TSeq (TInstr (TLoadFrame TyU64 11 5)) (TSeq (TInstr (TBin BinSub TyU64 11 11 10)) (TSeq (TInstr (TCmp CondUlt TyU64 4 11 (OpReg 5))) (TSeq (TIf 4 (TSeq (TInstr (TImm TyU64 4 (word 4))) (TReturn 2 4)) TSkip) (TSeq (TInstr (TLoadFrame TyPtr 7 4)) (TSeq (TInstr (TAddr 2 7 7 (SOME 10) 0 (&0:int))) (TSeq (TInstr (TLoadFrame TyU64 4 22)) (TSeq (TInstr (TLoadFrame TyPtr 11 0)) (TSeq (TInstr (TAddr 0 11 11 (SOME 4) 0 (&0:int))) (TSeq (TCountLoop 4 5 4294967295 name_copy_body) (TSeq (TInstr (TLoadFrame TyPtr 8 8)) (TSeq (TInstr (TLoad TyU64 8 4 9 8 (&0:int))) (TSeq (TInstr (TShift ShiftLeft TyU64 4 9 1)) (TSeq (TInstr (TLoadFrame TyPtr 7 2)) (TSeq (TInstr (TAddr 1 7 7 (SOME 4) 3 (&0:int))) (TSeq (TInstr (TStore 8 1 7 (&0:int) 10)) (TSeq (TInstr (TStore 8 1 7 (&8:int) 5)) (TSeq (TInstr (TImm TyU64 4 (word 1))) (TSeq (TInstr (TBin BinAdd TyU64 4 9 4)) (TSeq (TInstr (TStore 8 3 6 (&0:int) 4)) (TSeq (TInstr (TStore 8 4 8 (&0:int) 4)) (TSeq (TInstr (TBin BinAdd TyU64 10 10 5)) (TSeq (TInstr (TStore 8 4 8 (&8:int) 10)) (TReturn 1 9))))))))))))))))))))))))))`;;

let name_occupied = new_definition
 `name_occupied = (TSeq (TInstr (TImm TyU64 4 (word 1))) (TSeq (TInstr (TBin BinSub TyU64 4 7 4)) (TSeq (TInstr (TLoadFrame TyPtr 8 8)) (TSeq (TInstr (TLoad TyU64 8 4 9 8 (&0:int))) (TSeq (TInstr (TCmp CondUlt TyU64 10 4 (OpReg 9))) (TIf 10 name_row TSkip))))))`;;

let name_append = new_definition
 `name_append = (TSeq (TInstr (TLoadFrame TyPtr 8 8)) (TSeq (TInstr (TLoad TyU64 8 4 9 8 (&0:int))) (TSeq (TInstr (TLoadFrame TyU64 10 3)) (TSeq (TInstr (TShift ShiftRightU TyU64 10 10 4)) (TSeq (TInstr (TCmp CondUlt TyU64 11 9 (OpReg 10))) (TIf 11 name_append_room (TSeq (TInstr (TImm TyU64 4 (word 1))) (TReturn 2 4))))))))`;;

let name_body = new_definition
 `name_body = (TSeq (TInstr (TImm TyU64 4 (word 1))) (TSeq (TInstr (TBin BinSub TyU64 4 3 4)) (TSeq (TInstr (TBin BinAdd TyU64 5 1 2)) (TSeq (TInstr (TBin BinAnd TyU64 5 5 4)) (TSeq (TInstr (TLoadFrame TyPtr 6 6)) (TSeq (TInstr (TAddr 3 6 6 (SOME 5) 3 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 3 7 6 (&0:int))) (TSeq (TInstr (TCmp CondEq TyU64 8 7 (OpImm (word 0)))) (TIf 8 name_append name_occupied)))))))))`;;

let intern_name = new_definition
 `intern_name = (TProg [(1,0,1); (2,16,8); (2,1,1); (2,8,8); (2,16,8)] [(1,TyU64,0)] (TSeq name_prologue (TSeq (TCountLoop 2 3 4294967295 name_body) (TSeq (TInstr (TImm TyU64 4 (word 3))) (TReturn 2 4)))))`;;

let INTERN_NAME_TERM = prove
 (`intern_name = (TProg [(1,0,1); (2,16,8); (2,1,1); (2,8,8); (2,16,8)] [(1,TyU64,0)] (TSeq (TSeq (TInstr (TLoadFrame TyU64 4 22)) (TSeq (TInstr (TLoadFrame TyU64 5 23)) (TSeq (TInstr (TLoadFrame TyU64 6 1)) (TSeq (TInstr (TCmp CondUlt TyU64 7 6 (OpReg 4))) (TSeq (TIf 7 (TSeq (TInstr (TImm TyU64 8 (word 1))) (TReturn 0 8)) TSkip) (TSeq (TInstr (TBin BinSub TyU64 6 6 4)) (TSeq (TInstr (TCmp CondUlt TyU64 7 6 (OpReg 5))) (TSeq (TIf 7 (TSeq (TInstr (TImm TyU64 8 (word 1))) (TReturn 0 8)) TSkip) (TSeq (TInstr (TLoadFrame TyPtr 8 8)) (TSeq (TInstr (TLoad TyU64 8 4 9 8 (&0:int))) (TSeq (TInstr (TLoadFrame TyU64 10 3)) (TSeq (TInstr (TShift ShiftRightU TyU64 10 10 4)) (TSeq (TInstr (TCmp CondUlt TyU64 7 10 (OpReg 9))) (TSeq (TIf 7 (TSeq (TInstr (TImm TyU64 9 (word 5))) (TReturn 2 9)) TSkip) (TSeq (TInstr (TLoad TyU64 8 4 9 8 (&8:int))) (TSeq (TInstr (TLoadFrame TyU64 10 5)) (TSeq (TInstr (TCmp CondUlt TyU64 7 10 (OpReg 9))) (TSeq (TIf 7 (TSeq (TInstr (TImm TyU64 9 (word 5))) (TReturn 2 9)) TSkip) (TSeq (TInstr (TLoadFrame TyU64 3 7)) (TInstr (TShift ShiftRightU TyU64 3 3 3))))))))))))))))))))) (TSeq (TCountLoop 2 3 4294967295 (TSeq (TInstr (TImm TyU64 4 (word 1))) (TSeq (TInstr (TBin BinSub TyU64 4 3 4)) (TSeq (TInstr (TBin BinAdd TyU64 5 1 2)) (TSeq (TInstr (TBin BinAnd TyU64 5 5 4)) (TSeq (TInstr (TLoadFrame TyPtr 6 6)) (TSeq (TInstr (TAddr 3 6 6 (SOME 5) 3 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 3 7 6 (&0:int))) (TSeq (TInstr (TCmp CondEq TyU64 8 7 (OpImm (word 0)))) (TIf 8 (TSeq (TInstr (TLoadFrame TyPtr 8 8)) (TSeq (TInstr (TLoad TyU64 8 4 9 8 (&0:int))) (TSeq (TInstr (TLoadFrame TyU64 10 3)) (TSeq (TInstr (TShift ShiftRightU TyU64 10 10 4)) (TSeq (TInstr (TCmp CondUlt TyU64 11 9 (OpReg 10))) (TIf 11 (TSeq (TInstr (TLoad TyU64 8 4 10 8 (&8:int))) (TSeq (TInstr (TLoadFrame TyU64 5 23)) (TSeq (TInstr (TLoadFrame TyU64 11 5)) (TSeq (TInstr (TBin BinSub TyU64 11 11 10)) (TSeq (TInstr (TCmp CondUlt TyU64 4 11 (OpReg 5))) (TSeq (TIf 4 (TSeq (TInstr (TImm TyU64 4 (word 4))) (TReturn 2 4)) TSkip) (TSeq (TInstr (TLoadFrame TyPtr 7 4)) (TSeq (TInstr (TAddr 2 7 7 (SOME 10) 0 (&0:int))) (TSeq (TInstr (TLoadFrame TyU64 4 22)) (TSeq (TInstr (TLoadFrame TyPtr 11 0)) (TSeq (TInstr (TAddr 0 11 11 (SOME 4) 0 (&0:int))) (TSeq (TCountLoop 4 5 4294967295 (TSeq (TInstr (TAddr 0 8 11 (SOME 4) 0 (&0:int))) (TSeq (TInstr (TLoad TyU64 1 0 9 8 (&0:int))) (TSeq (TInstr (TAddr 2 8 7 (SOME 4) 0 (&0:int))) (TInstr (TStore 1 2 8 (&0:int) 9)))))) (TSeq (TInstr (TLoadFrame TyPtr 8 8)) (TSeq (TInstr (TLoad TyU64 8 4 9 8 (&0:int))) (TSeq (TInstr (TShift ShiftLeft TyU64 4 9 1)) (TSeq (TInstr (TLoadFrame TyPtr 7 2)) (TSeq (TInstr (TAddr 1 7 7 (SOME 4) 3 (&0:int))) (TSeq (TInstr (TStore 8 1 7 (&0:int) 10)) (TSeq (TInstr (TStore 8 1 7 (&8:int) 5)) (TSeq (TInstr (TImm TyU64 4 (word 1))) (TSeq (TInstr (TBin BinAdd TyU64 4 9 4)) (TSeq (TInstr (TStore 8 3 6 (&0:int) 4)) (TSeq (TInstr (TStore 8 4 8 (&0:int) 4)) (TSeq (TInstr (TBin BinAdd TyU64 10 10 5)) (TSeq (TInstr (TStore 8 4 8 (&8:int) 10)) (TReturn 1 9)))))))))))))))))))))))))) (TSeq (TInstr (TImm TyU64 4 (word 1))) (TReturn 2 4)))))))) (TSeq (TInstr (TImm TyU64 4 (word 1))) (TSeq (TInstr (TBin BinSub TyU64 4 7 4)) (TSeq (TInstr (TLoadFrame TyPtr 8 8)) (TSeq (TInstr (TLoad TyU64 8 4 9 8 (&0:int))) (TSeq (TInstr (TCmp CondUlt TyU64 10 4 (OpReg 9))) (TIf 10 (TSeq (TInstr (TShift ShiftLeft TyU64 10 4 1)) (TSeq (TInstr (TLoadFrame TyPtr 11 2)) (TSeq (TInstr (TAddr 1 11 11 (SOME 10) 3 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 1 10 11 (&8:int))) (TSeq (TInstr (TLoadFrame TyU64 5 23)) (TSeq (TInstr (TCmp CondEq TyU64 7 10 (OpReg 5))) (TIf 7 (TSeq (TInstr (TLoad TyU64 8 1 10 11 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 4 9 8 (&8:int))) (TSeq (TInstr (TCmp CondUlt TyU64 7 9 (OpReg 10))) (TSeq (TIf 7 (TSeq (TInstr (TImm TyU64 7 (word 6))) (TReturn 2 7)) TSkip) (TSeq (TInstr (TBin BinSub TyU64 9 9 10)) (TSeq (TInstr (TCmp CondUlt TyU64 7 9 (OpReg 5))) (TSeq (TIf 7 (TSeq (TInstr (TImm TyU64 7 (word 6))) (TReturn 2 7)) TSkip) (TSeq (TInstr (TLoadFrame TyPtr 7 4)) (TSeq (TInstr (TAddr 2 7 7 (SOME 10) 0 (&0:int))) (TSeq (TInstr (TLoadFrame TyU64 8 22)) (TSeq (TInstr (TLoadFrame TyPtr 9 0)) (TSeq (TInstr (TAddr 0 8 9 (SOME 8) 0 (&0:int))) (TSeq (TInstr (TImm TyBool 9 (word 1))) (TSeq (TCountLoop 6 5 4294967295 (TSeq (TInstr (TAddr 2 10 7 (SOME 6) 0 (&0:int))) (TSeq (TInstr (TLoad TyU64 1 2 10 10 (&0:int))) (TSeq (TInstr (TAddr 0 11 8 (SOME 6) 0 (&0:int))) (TSeq (TInstr (TLoad TyU64 1 0 11 11 (&0:int))) (TSeq (TInstr (TCmp CondEq TyU64 10 10 (OpReg 11))) (TInstr (TBin BinAnd TyBool 9 9 10)))))))) (TIf 9 (TReturn 1 4) TSkip))))))))))))))) TSkip))))))) TSkip)))))))))))))))) (TSeq (TInstr (TImm TyU64 4 (word 3))) (TReturn 2 4)))))`,
  REWRITE_TAC[intern_name; name_body; name_append; name_occupied; name_append_room; name_row; name_prologue; name_compare; name_cmp_body; name_copy_body]);;

(* ------------------------------------------------------------------------- *)
(* The interner's view of a state: the header words, the rows, a row's      *)
(* bytes, the name, the table.                                               *)
(* ------------------------------------------------------------------------- *)

let name_count = new_definition
 `name_count st = tisa_read st (tisa_base st 4) 8`;;

let name_used = new_definition
 `name_used st = tisa_read st (word_add (tisa_base st 4) (word 8)) 8`;;

(* Word i of the rows region: row r is words 2r (offset) and 2r + 1 (length). *)
let name_word = new_definition
 `name_word st i = tisa_read st (word_add (tisa_base st 1) (word (8 * i))) 8`;;

let name_row_bytes = new_definition
 `name_row_bytes st i =
    list_of_seq (\k. region_byte st 2 (val(name_word st (2 * i)) + k))
                (val(name_word st (2 * i + 1)))`;;

(* The name: the arg1 bytes of the input from offset arg0. *)
let name_key = new_definition
 `name_key st = region_range st 0 (val(tisa_fword st 22)) (val(tisa_fword st 23))`;;

(* The hash completeness assumes: FNV-1a 64, as holr_spec.ml defines it. *)
let name_hash = new_definition
 `name_hash (l:num list) = fnv1a fnv_offset l`;;

let name_slots = new_definition
 `name_slots st = word_ushr (tisa_len st 3) 3`;;

let name_pos = new_definition
 `name_pos st (h:int64) x = word_and (word_add h (word x)) (word_sub (name_slots st) (word 1))`;;

let name_slot = new_definition
 `name_slot st (p:int64) = tisa_read st (word_add (tisa_base st 3) (word (8 * val p))) 8`;;

(* ------------------------------------------------------------------------- *)
(* The table's invariant.                                                    *)
(* ------------------------------------------------------------------------- *)

(* Every row below the count is reachable by probing from its bytes' hash   *)
(* through non-empty slots, and its slot holds its id plus one.              *)
let name_complete = new_definition
 `name_complete st <=>
    !i. i < val(name_count st)
        ==> ?d. d < val(name_slots st) /\
                name_slot st (name_pos st (name_hash (name_row_bytes st i)) d) = word(i + 1) /\
                !e. e < d
                    ==> ~(name_slot st (name_pos st (name_hash (name_row_bytes st i)) e) = word 0)`;;

(* No two rows below the count hold the same bytes. *)
let name_distinct = new_definition
 `name_distinct st <=>
    !i j. i < val(name_count st) /\ j < val(name_count st) /\
          name_row_bytes st i = name_row_bytes st j
          ==> i = j`;;

(* A well-formed interner. The capacity conjuncts are needed: rows past the  *)
(* rows region, or bytes past the arena, could lie in another region or in  *)
(* the frame, and the writes of a run (an append's stores, a stop's status  *)
(* and return words) would then change rows that the other conjuncts speak  *)
(* of. Row bytes lie below the bytes used, so an append, which writes the   *)
(* arena from the bytes used on, keeps every row's bytes.                    *)
let name_ok = new_definition
 `name_ok st <=>
    val(name_count st) <= val(tisa_len st 1) DIV 16 /\
    val(name_used st) <= val(tisa_len st 2) /\
    (!i. i < val(name_count st)
         ==> val(name_word st (2 * i)) + val(name_word st (2 * i + 1)) <= val(name_used st)) /\
    name_complete st /\ name_distinct st`;;

(* The hash completeness needs: v1 holds the name's FNV-1a 64. *)
let name_hash_ok = new_definition
 `name_hash_ok st <=> tregs st 1 = name_hash (name_key st)`;;

(* What one probe that continued established: the slot was not empty, and   *)
(* if it named a row below the count, that row does not hold the name.      *)
let name_probed = new_definition
 `name_probed st x <=>
    ~(name_slot st (name_pos st (tregs st 1) x) = word 0) /\
    (val(word_sub (name_slot st (name_pos st (tregs st 1) x)) (word 1)) < val(name_count st)
     ==> ~(name_row_bytes st (val(word_sub (name_slot st (name_pos st (tregs st 1) x)) (word 1))) =
           name_key st))`;;

(* ------------------------------------------------------------------------- *)
(* What a run guarantees.                                                    *)
(* ------------------------------------------------------------------------- *)

(* A FIRED run: the returned row holds the name inside the used arena; the  *)
(* run found it (counts unchanged) or appended it at the count; rows and    *)
(* arena bytes below the old counts are unchanged.                          *)
let name_post = new_definition
 `name_post st s <=>
    val(tisa_fword s 19) < val(name_count s) /\
    name_row_bytes s (val(tisa_fword s 19)) = name_key st /\
    val(name_word s (2 * val(tisa_fword s 19))) + val(name_word s (2 * val(tisa_fword s 19) + 1)) <=
    val(name_used s) /\
    (name_count s = name_count st /\ name_used s = name_used st \/
     val(name_count s) = val(name_count st) + 1 /\ val(tisa_fword s 19) = val(name_count st) /\
     val(name_used s) = val(name_used st) + val(tisa_fword st 23)) /\
    (!i. i < 2 * val(name_count st) ==> name_word s i = name_word st i) /\
    (!k. k < val(name_used st) ==> region_byte s 2 k = region_byte st 2 k)`;;

(* Every outcome: the invariant kept when the hash is right; FIRED as above; *)
(* any other outcome writes only its status and return words; REFUSED       *)
(* exactly when the name does not lie inside the input.                      *)
let name_result = new_definition
 `name_result st k s <=>
    (name_ok st /\ name_hash_ok st ==> name_ok s) /\
    (k = 1 ==> name_post st s) /\
    (~(k = 1) ==> tmem s = tmem (tisa_finst k (tisa_fword s 19) st)) /\
    (k = 0 <=> val(tisa_len st 0) < val(tisa_fword st 22) + val(tisa_fword st 23))`;;

(* ------------------------------------------------------------------------- *)
(* Rows, positions, words.                                                   *)
(* ------------------------------------------------------------------------- *)

let NAME_POS_LT = prove
 (`!st h x. 0 < val(name_slots st) ==> val(name_pos st h x) < val(name_slots st)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[name_pos] THEN
  MP_TAC(ISPECL [`word_add h (word x):int64`; `word_sub (name_slots st) (word 1):int64`]
         (CONJUNCT2 VAL_WORD_AND_LE)) THEN
  MP_TAC(ISPECL [`name_slots st`; `word 1:int64`] TISA_VAL_SUB_EXACT) THEN
  REWRITE_TAC[VAL_WORD_1] THEN ASM_ARITH_TAC);;

let NAME_WORD_SUC_NZ = prove
 (`!i. i + 1 < 2 EXP 64 ==> ~(word(i + 1):int64 = word 0)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int64->num`) THEN
  ASM_SIMP_TAC[TISA_VAL_WORD_EXACT; VAL_WORD_0] THEN ARITH_TAC);;

let NAME_WORD_SUC_PRED = prove
 (`!i. i + 1 < 2 EXP 64 ==> val(word_sub (word(i + 1):int64) (word 1)) = i`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word(i + 1):int64) = i + 1` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`word(i + 1):int64`; `word 1:int64`] TISA_VAL_SUB_EXACT) THEN
  ASM_REWRITE_TAC[VAL_WORD_1] THEN ARITH_TAC);;

let NAME_SLOTS_VAL = prove
 (`!st. val(name_slots st) = val(tisa_len st 3) DIV 8`,
  REWRITE_TAC[name_slots; VAL_WORD_USHR] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Two rows with the same words and the same arena bytes over their ranges *)
(* hold the same bytes.                                                      *)
let NAME_ROW_BYTES_TRANSFER = prove
 (`!s t i u.
     name_word t (2 * i) = name_word s (2 * i) /\
     name_word t (2 * i + 1) = name_word s (2 * i + 1) /\
     val(name_word s (2 * i)) + val(name_word s (2 * i + 1)) <= u /\
     (!k. k < u ==> region_byte t 2 k = region_byte s 2 k)
     ==> name_row_bytes t i = name_row_bytes s i`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[name_row_bytes] THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* Rows of different lengths hold different bytes; so do rows that differ   *)
(* in one byte.                                                              *)
let NAME_LIST_OF_SEQ_EQ = prove
 (`!(f:num->num) g m n.
     list_of_seq f m = list_of_seq g n <=> m = n /\ !k. k < n ==> f k = g k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A state that shows a well-formed interner's view is well formed.          *)
(* ------------------------------------------------------------------------- *)

let NAME_OK_TRANSFER = prove
 (`!s t. name_ok s /\
         name_count t = name_count s /\ name_used t = name_used s /\
         name_slots t = name_slots s /\
         tisa_len t 1 = tisa_len s 1 /\ tisa_len t 2 = tisa_len s 2 /\
         (!i. i < 2 * val(name_count s) ==> name_word t i = name_word s i) /\
         (!p. val p < val(name_slots s) ==> name_slot t p = name_slot s p) /\
         (!k. k < val(name_used s) ==> region_byte t 2 k = region_byte s 2 k)
         ==> name_ok t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[name_ok] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!h x. name_pos t h x = name_pos s h x` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[name_pos]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < val(name_count s)
                    ==> name_word t (2 * i) = name_word s (2 * i) /\
                        name_word t (2 * i + 1) = name_word s (2 * i + 1)`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < val(name_count s) ==> name_row_bytes t i = name_row_bytes s i`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC NAME_ROW_BYTES_TRANSFER THEN
    EXISTS_TAC `val(name_used s)` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!h d. d < val(name_slots s)
                      ==> name_slot t (name_pos s h d) = name_slot s (name_pos s h d)`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC NAME_POS_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `name_complete s`)) THEN
    REWRITE_TAC[name_complete] THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN X_GEN_TAC `e:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `e < val(name_slots s)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `name_distinct s`)) THEN
    REWRITE_TAC[name_distinct] THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Appending the name at the count, its bytes at the bytes used, through the *)
(* first empty slot of its probe sequence, keeps the interner well formed.   *)
(* ------------------------------------------------------------------------- *)

let name_appended = new_definition
 `name_appended s t j <=>
    name_slots t = name_slots s /\ tisa_len t 1 = tisa_len s 1 /\ tisa_len t 2 = tisa_len s 2 /\
    val(name_count t) = val(name_count s) + 1 /\
    val(name_used t) = val(name_used s) + val(tisa_fword s 23) /\
    (!i. i < 2 * val(name_count s) ==> name_word t i = name_word s i) /\
    name_word t (2 * val(name_count s)) = name_used s /\
    name_word t (2 * val(name_count s) + 1) = tisa_fword s 23 /\
    (!p. val p < val(name_slots s)
         ==> name_slot t p =
             if p = name_pos s (tregs s 1) j then word(val(name_count s) + 1) else name_slot s p) /\
    (!k. k < val(name_used s) ==> region_byte t 2 k = region_byte s 2 k) /\
    (!k. k < val(tisa_fword s 23)
         ==> region_byte t 2 (val(name_used s) + k) = region_byte s 0 (val(tisa_fword s 22) + k))`;;

(* The appended row's bytes are the name. *)
let NAME_APPENDED_ROW = prove
 (`!s t j. name_appended s t j
           ==> name_row_bytes t (val(name_count s)) = name_key s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[name_appended] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[name_row_bytes; name_key; region_range; NAME_LIST_OF_SEQ_EQ] THEN
  ASM_SIMP_TAC[]);;

let NAME_APPENDED_OLD_ROWS = prove
 (`!s t j. name_ok s /\ name_appended s t j
           ==> !i. i < val(name_count s) ==> name_row_bytes t i = name_row_bytes s i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[name_ok; name_appended] THEN STRIP_TAC THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NAME_ROW_BYTES_TRANSFER THEN
  EXISTS_TAC `val(name_used s)` THEN ASM_SIMP_TAC[] THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let NAME_OK_APPEND = prove
 (`!s t j.
     name_ok s /\ name_hash_ok s /\
     val(name_count s) < val(tisa_len s 1) DIV 16 /\
     val(name_used s) + val(tisa_fword s 23) <= val(tisa_len s 2) /\
     j < val(name_slots s) /\
     (!x. x < j ==> name_probed s x) /\
     name_slot s (name_pos s (tregs s 1) j) = word 0 /\
     name_appended s t j
     ==> name_ok t /\
         (!i. i < val(name_count s) ==> ~(name_row_bytes s i = name_key s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* The appended row's bytes: kept out of the assumptions, where the       *)
  (* arithmetic would meet an equation of lists.                            *)
  let ROW_TAC = MP_TAC(MATCH_MP NAME_APPENDED_ROW (ASSUME `name_appended s t j`)) in
  MP_TAC(SPECL [`s:tisa_state`; `t:tisa_state`; `j:num`] NAME_APPENDED_OLD_ROWS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[name_appended] o
              check (fun th -> concl th = `name_appended s t j`)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[name_ok] o
                check (fun th -> concl th = `name_ok s`)) THEN
  SUBGOAL_THEN `val(name_count s) + 1 < 2 EXP 64 /\ 0 < val(name_slots s)`
   STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `tisa_len s 1` VAL_BOUND_64) THEN TISA_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!h x. name_pos t h x = name_pos s h x` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[name_pos]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!h d. d < val(name_slots s)
          ==> name_slot t (name_pos s h d) =
              if name_pos s h d = name_pos s (tregs s 1) j
              then word(val(name_count s) + 1) else name_slot s (name_pos s h d)`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC NAME_POS_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(word(val(name_count s) + 1):int64 = word 0)` ASSUME_TAC THENL
   [MATCH_MP_TAC NAME_WORD_SUC_NZ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* No row below the count holds the name: its probe chain from the name's *)
  (* hash would have passed probe j, met the empty slot, or been seen.      *)
  SUBGOAL_THEN `!i. i < val(name_count s) ==> ~(name_row_bytes s i = name_key s)`
   ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `i + 1 < 2 EXP 64` ASSUME_TAC THENL [TISA_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o REWRITE_RULE[name_complete] o
                check (fun th -> concl th = `name_complete s`)) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> if concl th = `name_hash_ok s`
                          then REWRITE_TAC[GSYM(REWRITE_RULE[name_hash_ok] th)] else NO_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num` STRIP_ASSUME_TAC) THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (ARITH_RULE `d < j \/ d = j \/ j < d`) THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `d:num` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `name_probed`)) (concl th))) THEN
      ASM_SIMP_TAC[name_probed; NAME_WORD_SUC_PRED];
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `d:num = j`)) THEN
      SUBGOAL_THEN `word(i + 1):int64 = word 0` MP_TAC THENL
       [ASM_MESON_TAC[]; ASM_SIMP_TAC[NAME_WORD_SUC_NZ]];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[name_ok; name_complete; name_distinct] THEN REPEAT CONJ_TAC THENL
   [TISA_ARITH_TAC;
    (* every row's bytes lie in the used arena *)
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `i < val(name_count s) \/ i = val(name_count s)` STRIP_ASSUME_TAC THENL
     [TISA_ARITH_TAC;
      SUBGOAL_THEN `name_word t (2 * i) = name_word s (2 * i) /\
                    name_word t (2 * i + 1) = name_word s (2 * i + 1)`
       (fun th -> REWRITE_TAC[th]) THENL
       [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN TISA_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `val(name_used s)`)) (concl th) &&
        can (find_term ((=) `name_word s`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN TISA_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN TISA_ARITH_TAC];
    (* every row is found by probing: old rows at their old distance, the  *)
    (* new row at the name's probe j                                         *)
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `i < val(name_count s) \/ i = val(name_count s)` STRIP_ASSUME_TAC THENL
     [TISA_ARITH_TAC;
      ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN `i + 1 < 2 EXP 64` ASSUME_TAC THENL [TISA_ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPEC `i:num` o REWRITE_RULE[name_complete] o
                  check (fun th -> concl th = `name_complete s`)) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `d:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
       [COND_CASES_TAC THEN REWRITE_TAC[] THEN
        SUBGOAL_THEN `word(i + 1):int64 = word 0` MP_TAC THENL
         [FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
                                     can (find_term ((=) `d:num`)) (lhand(concl th)) &&
                                     not(is_forall(concl th)) &&
                                     type_of(lhand(concl th)) = `:int64`
                                  then SUBST_ALL_TAC th else NO_TAC) THEN
          ASM_MESON_TAC[];
          ASM_SIMP_TAC[NAME_WORD_SUC_NZ]];
        X_GEN_TAC `e:num` THEN DISCH_TAC THEN
        SUBGOAL_THEN `e < val(name_slots s)` ASSUME_TAC THENL
         [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `d:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]];
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `i = val(name_count s)`)) THEN
      ROW_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(fun th -> if concl th = `name_hash_ok s`
                            then REWRITE_TAC[GSYM(REWRITE_RULE[name_hash_ok] th)] else NO_TAC) THEN
      EXISTS_TAC `j:num` THEN ASM_SIMP_TAC[] THEN
      X_GEN_TAC `e:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `e < val(name_slots s)` ASSUME_TAC THENL
       [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e:num` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `name_probed`)) (concl th))) THEN
      ASM_SIMP_TAC[name_probed]];
    (* no two rows hold one name *)
    MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(a < val(name_count s) \/ a = val(name_count s)) /\
                  (b < val(name_count s) \/ b = val(name_count s))`
     MP_TAC THENL [CONJ_TAC THEN TISA_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC DISJ_CASES_TAC) THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      is_var(lhand(concl th)) && rand(concl th) = `val(name_count s)`))) THEN
    REWRITE_TAC[] THEN ROW_TAC THEN DISCH_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[name_distinct] o
                    check (fun th -> concl th = `name_distinct s`)) THEN
      ASM_MESON_TAC[];
      ASM_MESON_TAC[];
      ASM_MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Entry validation: each region's bounds and minimum length, its distance  *)
(* from the frame, and the separation of the read-write regions from each   *)
(* other and from a non-empty input. Stated pair by pair, as the arithmetic *)
(* uses them.                                                                *)
(* ------------------------------------------------------------------------- *)

let name_regions = new_definition
 `name_regions st <=>
    val(tregs st 0) + 192 <= 2 EXP 64 /\
    val(tisa_base st 0) + val(tisa_len st 0) < 2 EXP 64 /\
    val(tisa_base st 1) + val(tisa_len st 1) < 2 EXP 64 /\
    val(tisa_base st 2) + val(tisa_len st 2) < 2 EXP 64 /\
    val(tisa_base st 3) + val(tisa_len st 3) < 2 EXP 64 /\
    val(tisa_base st 4) + val(tisa_len st 4) < 2 EXP 64 /\
    (val(tisa_len st 0) = 0 \/
     val(tisa_base st 0) + val(tisa_len st 0) <= val(tregs st 0) + 144 \/
     val(tregs st 0) + 192 <= val(tisa_base st 0)) /\
    (val(tisa_base st 1) + val(tisa_len st 1) <= val(tregs st 0) \/
     val(tregs st 0) + 192 <= val(tisa_base st 1)) /\
    (val(tisa_base st 2) + val(tisa_len st 2) <= val(tregs st 0) \/
     val(tregs st 0) + 192 <= val(tisa_base st 2)) /\
    (val(tisa_base st 3) + val(tisa_len st 3) <= val(tregs st 0) \/
     val(tregs st 0) + 192 <= val(tisa_base st 3)) /\
    (val(tisa_base st 4) + val(tisa_len st 4) <= val(tregs st 0) \/
     val(tregs st 0) + 192 <= val(tisa_base st 4)) /\
    16 <= val(tisa_len st 1) /\ 1 <= val(tisa_len st 2) /\
    8 <= val(tisa_len st 3) /\ 16 <= val(tisa_len st 4) /\
    (val(tisa_len st 0) = 0 \/
     val(tisa_base st 0) + val(tisa_len st 0) <= val(tisa_base st 1) \/
     val(tisa_base st 1) + val(tisa_len st 1) <= val(tisa_base st 0)) /\
    (val(tisa_len st 0) = 0 \/
     val(tisa_base st 0) + val(tisa_len st 0) <= val(tisa_base st 2) \/
     val(tisa_base st 2) + val(tisa_len st 2) <= val(tisa_base st 0)) /\
    (val(tisa_len st 0) = 0 \/
     val(tisa_base st 0) + val(tisa_len st 0) <= val(tisa_base st 3) \/
     val(tisa_base st 3) + val(tisa_len st 3) <= val(tisa_base st 0)) /\
    (val(tisa_len st 0) = 0 \/
     val(tisa_base st 0) + val(tisa_len st 0) <= val(tisa_base st 4) \/
     val(tisa_base st 4) + val(tisa_len st 4) <= val(tisa_base st 0)) /\
    (val(tisa_base st 1) + val(tisa_len st 1) <= val(tisa_base st 2) \/
     val(tisa_base st 2) + val(tisa_len st 2) <= val(tisa_base st 1)) /\
    (val(tisa_base st 1) + val(tisa_len st 1) <= val(tisa_base st 3) \/
     val(tisa_base st 3) + val(tisa_len st 3) <= val(tisa_base st 1)) /\
    (val(tisa_base st 1) + val(tisa_len st 1) <= val(tisa_base st 4) \/
     val(tisa_base st 4) + val(tisa_len st 4) <= val(tisa_base st 1)) /\
    (val(tisa_base st 2) + val(tisa_len st 2) <= val(tisa_base st 3) \/
     val(tisa_base st 3) + val(tisa_len st 3) <= val(tisa_base st 2)) /\
    (val(tisa_base st 2) + val(tisa_len st 2) <= val(tisa_base st 4) \/
     val(tisa_base st 4) + val(tisa_len st 4) <= val(tisa_base st 2)) /\
    (val(tisa_base st 3) + val(tisa_len st 3) <= val(tisa_base st 4) \/
     val(tisa_base st 4) + val(tisa_len st 4) <= val(tisa_base st 3))`;;

(* A goal among the assumptions, or arithmetic over them. *)
let NAME_CLOSE_TAC =
  FIRST_ASSUM ACCEPT_TAC ORELSE (ASM_REWRITE_TAC[] THEN NO_TAC) ORELSE TISA_WP_ARITH_TAC;;

let NAME_ENTRY = prove
 (`!st. tisa_entry_ok intern_name st ==> name_regions st`,
  GEN_TAC THEN
  REWRITE_TAC[intern_name; tisa_entry_ok; tisa_decls_ok; tisa_pairs_ok; tisa_init_ok;
              tisa_region_ok; tisa_pair_ok; tisa_frame; tisa_base; tisa_len; name_regions] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `~(val(tisa_fword st 3) = 0) /\ ~(val(tisa_fword st 5) = 0) /\
                ~(val(tisa_fword st 7) = 0) /\ ~(val(tisa_fword st 9) = 0)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TISA_WP_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(val(tisa_fword st 3) = 0)`;
                              ASSUME `~(val(tisa_fword st 5) = 0)`;
                              ASSUME `~(val(tisa_fword st 7) = 0)`;
                              ASSUME `~(val(tisa_fword st 9) = 0)`]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  ASM_CASES_TAC `val(tisa_fword st 1) = 0` THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN NAME_CLOSE_TAC;
    FIRST_X_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
    REPEAT CONJ_TAC THEN NAME_CLOSE_TAC]);;

(* The entry facts as assumptions, one per conjunct (never split on their  *)
(* disjunctions), and the slot count as arithmetic.                         *)
let NAME_REGIONS_TAC =
  FIRST_ASSUM((REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o GEN_REWRITE_RULE I [name_regions] o
              check (fun th -> concl th = `name_regions st`)) THEN
  ASSUME_TAC(SPEC `st:tisa_state` NAME_SLOTS_VAL);;

(* The view of state s as the entry state's. *)
let NAME_SAME_VIEW_TAC s =
  MP_TAC(ISPECL [s; `st:tisa_state`] TISA_SAME_VIEW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC];;

(* ------------------------------------------------------------------------- *)
(* The finish (status and return words) keeps the interner's view of a       *)
(* state with the entry state's frame register and memory.                   *)
(* ------------------------------------------------------------------------- *)

let NAME_REGION_WORD_VAL = prove
 (`!(b:int64) l k. val b + l < 2 EXP 64 /\ k <= l ==> val(word_add b (word k)) = val b + k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC);;

(* A read away from the status and return words, through the finish of a  *)
(* state with the entry state's frame register and memory.                 *)
let NAME_FINST_READ = prove
 (`!st X out (v:int64) (a:int64) w.
     val(tregs st 0) + 192 <= 2 EXP 64 /\ tregs X 0 = tregs st 0 /\ tmem X = tmem st /\
     val a + w <= 2 EXP 64 /\
     (val a + w <= val(tregs st 0) + 144 \/ val(tregs st 0) + 160 <= val a)
     ==> tisa_read (tisa_finst out v X) a w = tisa_read st a w`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`out:num`; `v:int64`; `X:tisa_state`; `a:int64`; `w:num`] TISA_READ_FINST_W) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[tisa_read]);;

let NAME_FINST_VIEW = prove
 (`!st X out (v:int64).
     name_regions st /\ tregs X 0 = tregs st 0 /\ tmem X = tmem st
     ==> tisa_fword (tisa_finst out v X) 19 = v /\
         tisa_fword (tisa_finst out v X) 22 = tisa_fword st 22 /\
         tisa_fword (tisa_finst out v X) 23 = tisa_fword st 23 /\
         (!r. r < 5 ==> tisa_base (tisa_finst out v X) r = tisa_base st r /\
                        tisa_len (tisa_finst out v X) r = tisa_len st r) /\
         name_count (tisa_finst out v X) = name_count st /\
         name_used (tisa_finst out v X) = name_used st /\
         name_slots (tisa_finst out v X) = name_slots st /\
         (!i. i < 2 * (val(tisa_len st 1) DIV 16)
              ==> name_word (tisa_finst out v X) i = name_word st i) /\
         (!p. val p < val(name_slots st) ==> name_slot (tisa_finst out v X) p = name_slot st p) /\
         (!k. k < val(tisa_len st 2) ==> region_byte (tisa_finst out v X) 2 k = region_byte st 2 k) /\
         (!k. k < val(tisa_len st 0) ==> region_byte (tisa_finst out v X) 0 k = region_byte st 0 k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN NAME_REGIONS_TAC THEN
  NAME_SAME_VIEW_TAC `X:tisa_state` THEN
  MP_TAC(ISPECL [`out:num`; `v:int64`; `X:tisa_state`] TISA_FINST_VIEW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)] THEN
  SUBGOAL_THEN `!r. r < 5 ==> tisa_base (tisa_finst out v X) r = tisa_base st r /\
                              tisa_len (tisa_finst out v X) r = tisa_len st r`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ARITH_RULE `r < 5 ==> r < 9`]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[name_count; name_used; name_slots; name_word; name_slot; region_byte] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < 5 /\ 1 < 5 /\ 2 < 5 /\ 3 < 5 /\ 4 < 5 /\
                           19 < 24 /\ 22 < 24 /\ 23 < 24`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN RULE_ASSUM_TAC(REWRITE_RULE[NAME_SLOTS_VAL]) THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN TRY AP_TERM_TAC THEN
  MATCH_MP_TAC NAME_FINST_READ THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[NAME_SLOTS_VAL] THEN TISA_ARITH_DECIDE_TAC);;

let NAME_OK_FINST = prove
 (`!st X out (v:int64).
     name_regions st /\ tregs X 0 = tregs st 0 /\ tmem X = tmem st /\ name_ok st
     ==> name_ok (tisa_finst out v X)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NAME_OK_TRANSFER THEN EXISTS_TAC `st:tisa_state` THEN
  MP_TAC(SPECL [`st:tisa_state`; `X:tisa_state`; `out:num`; `v:int64`] NAME_FINST_VIEW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[name_ok] o check (fun th -> concl th = `name_ok st`)) THEN
  ASM_SIMP_TAC[ARITH_RULE `1 < 5 /\ 2 < 5`] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN TISA_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* States are equal when their registers and memories are.                   *)
(* ------------------------------------------------------------------------- *)

let TISA_STATE_CASES = prove_cases_thm tisa_state_INDUCT;;

let TISA_STATE_EQ = prove
 (`!s t. s = t <=> tregs s = tregs t /\ tmem s = tmem t`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `s:tisa_state` TISA_STATE_CASES) THEN
  STRUCT_CASES_TAC(ISPEC `t:tisa_state` TISA_STATE_CASES) THEN
  REWRITE_TAC[tregs; tmem; injectivity "tisa_state"]);;

(* ------------------------------------------------------------------------- *)
(* The comparison loop (COUNT_LOOP 6 5, body name_cmp_body): from state sq, *)
(* with v7 pointing n = val v5 bytes into the arena and v8 n bytes into the *)
(* input, it leaves v9 = 1 exactly when the two ranges hold the same bytes; *)
(* it writes only v6, v9, v10 and v11, and no memory.                        *)
(* ------------------------------------------------------------------------- *)

let name_cmp_inv = new_definition
 `name_cmp_inv st sq N i s <=>
    tregs s 0 = tregs st 0 /\ tmem s = tmem st /\ N = val(tregs sq 5) /\
    (!r. ~(r = 6) /\ ~(r = 9) /\ ~(r = 10) /\ ~(r = 11) ==> tregs s r = tregs sq r) /\
    tregs s 9 = (if !k. k < i ==> tisa_read st (word_add (tregs sq 7) (word k)) 1 =
                                 tisa_read st (word_add (tregs sq 8) (word k)) 1
                 then word 1 else word 0)`;;

let NAME_CMP_BODY_WP = prove
 (`!st sq N j s0 R.
     name_regions st /\
     val(tisa_base st 2) <= val(tregs sq 7) /\
     val(tregs sq 7) + val(tregs sq 5) <= val(tisa_base st 2) + val(tisa_len st 2) /\
     val(tisa_base st 0) <= val(tregs sq 8) /\
     val(tregs sq 8) + val(tregs sq 5) <= val(tisa_base st 0) + val(tisa_len st 0) /\
     j < N /\ name_cmp_inv st sq N j s0
     ==> tisa_wp name_cmp_body (name_cmp_inv st sq N (j + 1)) R (tisa_setreg 6 (word j) s0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN NAME_REGIONS_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [name_cmp_inv] o
                check (fun th -> tisa_has_tm `name_cmp_inv` th)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N = val(tregs sq 5)`)) THEN
  NAME_SAME_VIEW_TAC `s0:tisa_state` THEN
  MAP_EVERY (fun r -> FIRST_ASSUM(ASSUME_TAC o C MP (EQT_ELIM(NUM_REDUCE_CONV
      (list_mk_conj (map (fun q -> mk_neg(mk_eq(mk_small_numeral r, mk_small_numeral q))) [6;9;10;11])))) o
      SPEC (mk_small_numeral r) o check (fun th -> is_forall(concl th) && tisa_has_tm `tregs sq` th)))
    [5; 7; 8] THEN
  ASSUME_TAC(ISPEC `tregs sq 5` VAL_BOUND_64) THEN
  SUBGOAL_THEN `val(word j:int64) = j` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN TISA_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[name_cmp_body] THEN TISA_VCG_TAC THEN
  REWRITE_TAC[name_cmp_inv] THEN TISA_STATE_NORM_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES] THEN REPEAT CONJ_TAC THEN
  TRY(GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `k < j + 1 <=> k < j \/ k = j`] THEN MESON_TAC[]);;

let NAME_CMP_LOOP = prove
 (`!st sq Q R.
     name_regions st /\ tregs sq 0 = tregs st 0 /\ tmem sq = tmem st /\
     val(tisa_base st 2) <= val(tregs sq 7) /\
     val(tregs sq 7) + val(tregs sq 5) <= val(tisa_base st 2) + val(tisa_len st 2) /\
     val(tisa_base st 0) <= val(tregs sq 8) /\
     val(tregs sq 8) + val(tregs sq 5) <= val(tisa_base st 0) + val(tisa_len st 0) /\
     tregs sq 9 = word 1 /\
     (4294967295 < val(tregs sq 5) ==> R 2 (tisa_failst 2 sq)) /\
     (!s. tregs s 0 = tregs st 0 /\ tmem s = tmem st /\
          (!r. ~(r = 6) /\ ~(r = 9) /\ ~(r = 10) /\ ~(r = 11) ==> tregs s r = tregs sq r) /\
          tregs s 9 =
          (if !k. k < val(tregs sq 5) ==> tisa_read st (word_add (tregs sq 7) (word k)) 1 =
                                         tisa_read st (word_add (tregs sq 8) (word k)) 1
           then word 1 else word 0)
          ==> Q s)
     ==> tisa_wp (TCountLoop 6 5 4294967295 name_cmp_body) Q R sq`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC TISA_WP_COUNT_LOOP THEN EXISTS_TAC `name_cmp_inv st sq` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN ASM_REWRITE_TAC[name_cmp_inv; LT] THEN MESON_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NAME_CMP_BODY_WP THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[name_cmp_inv] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[TISA_TREGS_SETREG; TISA_TMEM_SETREG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The copy loop (COUNT_LOOP 4 5, body name_copy_body): from state sq, with  *)
(* v11 pointing n = val v5 bytes into the input and v7 n bytes into the      *)
(* arena, it leaves the input's n bytes written at v7, as one byte-range     *)
(* write, and writes only v4, v8 and v9 otherwise.                           *)
(* ------------------------------------------------------------------------- *)

(* Copying byte i after bytes 0 .. i - 1. *)
let NAME_WRITE_COPY_STEP = prove
 (`!(d:int64) (src:int64) i (m:int64->byte).
     i < 2 EXP 64
     ==> write (bytes(word_add d (word i),1)) (read (bytes(word_add src (word i),1)) m)
               (write (bytes(d,i)) (read (bytes(src,i)) m) m) =
         write (bytes(d,i + 1)) (read (bytes(src,i + 1)) m) m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; WRITE_BYTES] THEN
  X_GEN_TAC `c:int64` THEN BETA_TAC THEN REWRITE_TAC[LIMB_READ_BYTES] THEN
  REWRITE_TAC[WORD_RULE `word_sub c (word_add d (word i)):int64 = word_sub (word_sub c d) (word i)`] THEN
  ABBREV_TAC `u = word_sub c d:int64` THEN
  SUBGOAL_THEN `c = word_add d u:int64` SUBST1_TAC THENL
   [EXPAND_TAC "u" THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub u (word i):int64) < 1 <=> val(u:int64) = i` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `n < 1 <=> n = 0`; VAL_EQ_0; WORD_SUB_EQ_0] THEN
    REWRITE_TAC[GSYM VAL_EQ] THEN ASM_SIMP_TAC[TISA_VAL_WORD_EXACT];
    ALL_TAC] THEN
  ASM_CASES_TAC `val(u:int64) = i` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `word_sub u (word i):int64 = word 0` SUBST1_TAC THENL
     [REWRITE_TAC[WORD_SUB_EQ_0; GSYM VAL_EQ] THEN ASM_SIMP_TAC[TISA_VAL_WORD_EXACT]; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD_0; ARITH_RULE `0 < 1 /\ i < i + 1`; WORD_ADD_0] THEN
    SUBGOAL_THEN `u:int64 = word i` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ] THEN ASM_SIMP_TAC[TISA_VAL_WORD_EXACT]; REWRITE_TAC[]];
    ASM_CASES_TAC `val(u:int64) < i` THEN
    ASM_SIMP_TAC[ARITH_RULE `x < i ==> x < i + 1`] THEN
    SUBGOAL_THEN `~(val(u:int64) < i + 1)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC]);;

let name_copy_inv = new_definition
 `name_copy_inv st sq N i s <=>
    tregs s 0 = tregs st 0 /\ N = val(tregs sq 5) /\
    (!r. ~(r = 4) /\ ~(r = 8) /\ ~(r = 9) ==> tregs s r = tregs sq r) /\
    tmem s = write (bytes(tregs sq 7,i)) (read (bytes(tregs sq 11,i)) (tmem st)) (tmem st)`;;

let NAME_COPY_BODY_WP = prove
 (`!st sq N j s0 R.
     name_regions st /\
     val(tisa_base st 2) <= val(tregs sq 7) /\
     val(tregs sq 7) + val(tregs sq 5) <= val(tisa_base st 2) + val(tisa_len st 2) /\
     val(tisa_base st 0) <= val(tregs sq 11) /\
     val(tregs sq 11) + val(tregs sq 5) <= val(tisa_base st 0) + val(tisa_len st 0) /\
     j < N /\ name_copy_inv st sq N j s0
     ==> tisa_wp name_copy_body (name_copy_inv st sq N (j + 1)) R (tisa_setreg 4 (word j) s0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN NAME_REGIONS_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [name_copy_inv] o
                check (fun th -> tisa_has_tm `name_copy_inv` th)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N = val(tregs sq 5)`)) THEN
  MAP_EVERY (fun r -> FIRST_ASSUM(ASSUME_TAC o C MP (EQT_ELIM(NUM_REDUCE_CONV
      (list_mk_conj (map (fun q -> mk_neg(mk_eq(mk_small_numeral r, mk_small_numeral q))) [4;8;9])))) o
      SPEC (mk_small_numeral r) o check (fun th -> is_forall(concl th) && tisa_has_tm `tregs sq` th)))
    [5; 7; 11] THEN
  ASSUME_TAC(ISPEC `tregs sq 5` VAL_BOUND_64) THEN
  SUBGOAL_THEN `val(word j:int64) = j` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN TISA_ARITH_TAC; ALL_TAC] THEN
  (* s0 as a byte-range write over a state with the entry state's memory *)
  ABBREV_TAC `X = TState (tregs s0) (tmem st)` THEN
  SUBGOAL_THEN `tregs X = tregs s0 /\ tmem X = tmem st` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[tregs; tmem]; ALL_TAC] THEN
  SUBGOAL_THEN `s0 = tisa_bwrite (tregs sq 7) j (read (bytes(tregs sq 11,j)) (tmem st)) X`
   SUBST1_TAC THENL
   [ASM_REWRITE_TAC[TISA_STATE_EQ; TISA_TREGS_BWRITE; TISA_TMEM_BWRITE]; ALL_TAC] THEN
  SUBGOAL_THEN `tregs X 0 = tregs st 0` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  NAME_SAME_VIEW_TAC `X:tisa_state` THEN
  SUBGOAL_THEN `tregs X 5 = tregs sq 5 /\ tregs X 7 = tregs sq 7 /\ tregs X 11 = tregs sq 11`
   STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(val(tregs sq 5) = 0)` ASSUME_TAC THENL [TISA_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[name_copy_body] THEN TISA_VCG_TAC THEN
  REWRITE_TAC[name_copy_inv] THEN TISA_STATE_NORM_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES] THEN REPEAT CONJ_TAC THEN
  TRY(GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) && tisa_has_tm `tregs sq` th)) THEN
      ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  (REWRITE_TAC[TISA_TMEM_STORE; TISA_TMEM_SETREG; TISA_TMEM_BWRITE; tisa_read; tisa_norm] THEN
    ASM_REWRITE_TAC[] THEN
    W(fun (asl,w) -> MP_TAC(ISPECL [`tregs sq 7`; `tregs sq 11`; `j:num`; `tmem st`]
                              NAME_WRITE_COPY_STEP)) THEN
    ANTS_TAC THENL [TISA_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    SUBGOAL_THEN `read (bytes (word_add (tregs sq 11) (word j),1)) (tmem st) MOD 2 EXP 64 =
                  read (bytes (word_add (tregs sq 11) (word j),1)) (tmem st)`
     SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN
      MP_TAC(ISPECL [`word_add (tregs sq 11) (word j):int64`; `1`; `tmem st`] READ_BYTES_BOUND) THEN
      ARITH_TAC;
      REWRITE_TAC[]]));;

let NAME_COPY_LOOP = prove
 (`!st sq Q R.
     name_regions st /\ tregs sq 0 = tregs st 0 /\ tmem sq = tmem st /\
     val(tisa_base st 2) <= val(tregs sq 7) /\
     val(tregs sq 7) + val(tregs sq 5) <= val(tisa_base st 2) + val(tisa_len st 2) /\
     val(tisa_base st 0) <= val(tregs sq 11) /\
     val(tregs sq 11) + val(tregs sq 5) <= val(tisa_base st 0) + val(tisa_len st 0) /\
     (4294967295 < val(tregs sq 5) ==> R 2 (tisa_failst 2 sq)) /\
     (!s. tregs s 0 = tregs st 0 /\ tmem s = tmem st /\
          (!r. ~(r = 4) /\ ~(r = 8) /\ ~(r = 9) ==> tregs s r = tregs sq r)
          ==> Q (tisa_bwrite (tregs sq 7) (val(tregs sq 5))
                             (read (bytes(tregs sq 11,val(tregs sq 5))) (tmem st)) s))
     ==> tisa_wp (TCountLoop 4 5 4294967295 name_copy_body) Q R sq`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC TISA_WP_COUNT_LOOP THEN EXISTS_TAC `name_copy_inv st sq` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN ASM_REWRITE_TAC[name_copy_inv] THEN
    REWRITE_TAC[READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[FUN_EQ_THM; WRITE_BYTES; LT] THEN MESON_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NAME_COPY_BODY_WP THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[name_copy_inv] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N = val(tregs sq 5)`)) THEN
    SUBGOAL_THEN
     `tisa_setreg 4 (word (val(tregs sq 5))) s =
      tisa_bwrite (tregs sq 7) (val(tregs sq 5)) (read (bytes(tregs sq 11,val(tregs sq 5))) (tmem st))
                  (TState (tregs (tisa_setreg 4 (word (val(tregs sq 5))) s)) (tmem st))`
     SUBST1_TAC THENL
     [ASM_REWRITE_TAC[TISA_STATE_EQ; TISA_TREGS_BWRITE; TISA_TMEM_BWRITE; tregs; tmem;
                      TISA_TMEM_SETREG];
      ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[tregs; tmem; TISA_TREGS_SETREG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The loop invariant, and what the prologue establishes.                    *)
(* ------------------------------------------------------------------------- *)

(* The prologue's checks: the name lies inside the input, the header words  *)
(* inside their regions.                                                     *)
let name_entered = new_definition
 `name_entered st <=>
    val(tisa_fword st 22) + val(tisa_fword st 23) <= val(tisa_len st 0) /\
    val(name_count st) <= val(tisa_len st 1) DIV 16 /\
    val(name_used st) <= val(tisa_len st 2)`;;

(* Before probe j: the frame, memory, hash and slot count of the entry      *)
(* state, the prologue's checks, and probes 0 .. j - 1 made.                 *)
let name_inv = new_definition
 `name_inv st N j s <=>
    tregs s 0 = tregs st 0 /\ tmem s = tmem st /\
    tregs s 1 = tregs st 1 /\ tregs s 3 = name_slots st /\
    N = val(name_slots st) /\ name_entered st /\
    (!x. x < j ==> name_probed st x)`;;

(* ------------------------------------------------------------------------- *)
(* The results of the stops.                                                 *)
(* ------------------------------------------------------------------------- *)

let NAME_FINST_MEM = prove
 (`!st X out (v:int64).
     tregs X 0 = tregs st 0 /\ tmem X = tmem st
     ==> tmem (tisa_finst out v X) = tmem (tisa_finst out v st)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[tisa_finst; tisa_setfword; tisa_frame; TISA_TMEM_STORE; TISA_TREGS_STORE] THEN
  ASM_REWRITE_TAC[]);;

(* A stop after the prologue that wrote only its status and return words.   *)
let NAME_STOP_RESULT = prove
 (`!st X k (v:int64).
     name_regions st /\ name_entered st /\ tregs X 0 = tregs st 0 /\ tmem X = tmem st /\
     ~(k = 0) /\ ~(k = 1)
     ==> name_result st k (tisa_finst k v X)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[name_result] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`st:tisa_state`; `X:tisa_state`; `k:num`; `v:int64`] NAME_FINST_VIEW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [STRIP_TAC THEN MATCH_MP_TAC NAME_OK_FINST THEN EXISTS_TAC `st:tisa_state` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC NAME_FINST_MEM THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[name_entered] o
                  check (fun th -> concl th = `name_entered st`)) THEN ARITH_TAC]);;

(* A stop in the prologue, before any check is known to have passed.        *)
let NAME_EARLY_STOP_RESULT = prove
 (`!st X k (v:int64).
     name_regions st /\ tregs X 0 = tregs st 0 /\ tmem X = tmem st /\ ~(k = 1) /\
     (k = 0 <=> val(tisa_len st 0) < val(tisa_fword st 22) + val(tisa_fword st 23))
     ==> name_result st k (tisa_finst k v X)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[name_result] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`st:tisa_state`; `X:tisa_state`; `k:num`; `v:int64`] NAME_FINST_VIEW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [STRIP_TAC THEN MATCH_MP_TAC NAME_OK_FINST THEN EXISTS_TAC `st:tisa_state` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC NAME_FINST_MEM THEN ASM_REWRITE_TAC[]]);;

(* A FIRED stop that found the name in row val w. *)
let NAME_FOUND_RESULT = prove
 (`!st X (w:int64).
     name_regions st /\ name_entered st /\ tregs X 0 = tregs st 0 /\ tmem X = tmem st /\
     val w < val(name_count st) /\
     val(name_word st (2 * val w)) + val(name_word st (2 * val w + 1)) <= val(name_used st) /\
     name_row_bytes st (val w) = name_key st
     ==> name_result st 1 (tisa_finst 1 w X)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[name_result] THEN
  MP_TAC(SPECL [`st:tisa_state`; `X:tisa_state`; `1`; `w:int64`] NAME_FINST_VIEW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[name_entered] o
              check (fun th -> concl th = `name_entered st`)) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN REPEAT CONJ_TAC THENL
   [STRIP_TAC THEN MATCH_MP_TAC NAME_OK_FINST THEN EXISTS_TAC `st:tisa_state` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[name_post] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!i. i < 2 * val(name_count st) ==> i < 2 * (val(tisa_len st 1) DIV 16)`
     ASSUME_TAC THENL [REPEAT STRIP_TAC THEN TISA_WP_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `!k. k < val(name_used st) ==> k < val(tisa_len st 2)`
     ASSUME_TAC THENL [REPEAT STRIP_TAC THEN TISA_WP_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `name_word (tisa_finst 1 w X) (2 * val w) = name_word st (2 * val w) /\
                  name_word (tisa_finst 1 w X) (2 * val w + 1) = name_word st (2 * val w + 1)`
     STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN TISA_WP_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `name_row_bytes st (val(w:int64)) = name_key st`)) THEN
      MATCH_MP_TAC NAME_ROW_BYTES_TRANSFER THEN EXISTS_TAC `val(name_used st)` THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]];
    TISA_WP_ARITH_TAC]);;

(* A FIRED stop that appended the name: a state with the appended view.     *)
let NAME_APPEND_RESULT = prove
 (`!st t j.
     name_regions st /\ name_entered st /\
     val(name_count st) < val(tisa_len st 1) DIV 16 /\
     val(name_used st) + val(tisa_fword st 23) <= val(tisa_len st 2) /\
     j < val(name_slots st) /\ (!x. x < j ==> name_probed st x) /\
     name_slot st (name_pos st (tregs st 1) j) = word 0 /\
     name_appended st t j /\ tisa_fword t 19 = name_count st
     ==> name_result st 1 t /\
         (name_ok st /\ name_hash_ok st
          ==> !i. i < val(name_count st) ==> ~(name_row_bytes st i = name_key st))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[name_entered] o
              check (fun th -> concl th = `name_entered st`)) THEN
  REWRITE_TAC[name_result; ARITH_EQ] THEN REPEAT CONJ_TAC THENL
   [STRIP_TAC THEN MP_TAC(SPECL [`st:tisa_state`; `t:tisa_state`; `j:num`] NAME_OK_APPEND) THEN
    ASM_SIMP_TAC[];
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP NAME_APPENDED_ROW) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[name_appended] o
                  check (fun th -> concl th = `name_appended st t j`)) THEN
    ASM_REWRITE_TAC[name_post] THEN
    SUBGOAL_THEN `val(name_count st) + 1 < 2 EXP 64` ASSUME_TAC THENL
     [MP_TAC(ISPEC `tisa_len st 1` VAL_BOUND_64) THEN TISA_WP_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[ARITH_RULE `x < x + 1`] THEN TISA_WP_ARITH_TAC;
    TISA_WP_ARITH_TAC;
    STRIP_TAC THEN MP_TAC(SPECL [`st:tisa_state`; `t:tisa_state`; `j:num`] NAME_OK_APPEND) THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The blocks of one probe. Each starts from a state with the entry state's *)
(* frame register and memory; its facts are the entry facts, the prologue's *)
(* checks and the registers the probe set.                                   *)
(* ------------------------------------------------------------------------- *)

(* The entry facts and the prologue's checks as arithmetic on the terms the *)
(* generator writes (header words as reads), and the view of state s as the *)
(* entry state's.                                                            *)
let NAME_BLOCK_SETUP_TAC s =
  NAME_REGIONS_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[name_entered; name_count; name_used] o
              check (fun th -> concl th = `name_entered st`)) THEN
  NAME_SAME_VIEW_TAC s THEN
  ASSUME_TAC(ISPEC `tisa_fword st 23` VAL_BOUND_64) THEN
  ASSUME_TAC(ISPEC `tisa_fword st 22` VAL_BOUND_64);;

(* Row words as the generator reads them: base + 8 * val(word_shl id 1). *)
let NAME_WORD_SHL = prove
 (`!st (id:int64).
     val id < 2 EXP 62
     ==> name_word st (2 * val id) =
         tisa_read st (word_add (tisa_base st 1) (word (8 * val(word_shl id 1)))) 8 /\
         name_word st (2 * val id + 1) =
         tisa_read st (word_add (tisa_base st 1) (word (8 * val(word_shl id 1) + 8))) 8`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word_shl (id:int64) 1) = 2 * val id` SUBST1_TAC THENL
   [MATCH_MP_TAC TISA_VAL_SHL1 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[name_word; ARITH_RULE `8 * (2 * x + 1) = 8 * (2 * x) + 8`]);;

(* The bytes of a row of the name's length against the name's bytes. *)
let NAME_ROW_KEY = prove
 (`!st i a.
     name_word st (2 * i) = a /\ name_word st (2 * i + 1) = tisa_fword st 23
     ==> (name_row_bytes st i = name_key st <=>
          !k. k < val(tisa_fword st 23)
              ==> tisa_read st (word_add (tisa_base st 2) (word (val a + k))) 1 =
                  tisa_read st (word_add (tisa_base st 0) (word (val(tisa_fword st 22) + k))) 1)`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[name_row_bytes; name_key; region_range; NAME_LIST_OF_SEQ_EQ; region_byte] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN SIMP_TAC[]);;

(* The slot's id, and its row's words as the generator reads them. *)
let name_id_tm = `word_sub (name_slot st (name_pos st (tregs st 1) j)) (word 1):int64`;;

let NAME_ROW_WORDS_TAC =
  let lt = mk_comb(mk_comb(`(<):num->num->bool`, mk_comb(`val:int64->num`, name_id_tm)), `2 EXP 62`) in
  SUBGOAL_THEN lt ASSUME_TAC THENL [TISA_WP_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(MP (ISPECL [`st:tisa_state`; name_id_tm] NAME_WORD_SHL) (ASSUME lt)) THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC);;

let TISA_FAILST_FINST = prove
 (`!k st. tisa_failst k st = tisa_finst k (word k) st`,
  REWRITE_TAC[tisa_failst; tisa_finst]);;

let NAME_PROBED_STEP = prove
 (`!st j. (!x. x < j ==> name_probed st x) /\ name_probed st j
          ==> !x. x < j + 1 ==> name_probed st x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:num = j` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* A side condition: state facts by normalization, arithmetic by decision. *)
let NAME_SIDE_TAC =
  TISA_STATE_NORM_TAC THEN
  ((ASM_REWRITE_TAC[] THEN NO_TAC) ORELSE TISA_ARITH_DECIDE_TAC);;

(* A stop that wrote only its status and return words. *)
let NAME_STOP_LEAF_TAC =
  REWRITE_TAC[TISA_FAILST_FINST] THEN
  MATCH_MP_TAC NAME_STOP_RESULT THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  CONJ_TAC THEN TISA_STATE_NORM_TAC;;

(* Instantiate a loop's register-preservation fact at registers rs. *)
let NAME_REGS_TAC rs =
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && tisa_has_tm `tregs` th && is_imp(snd(strip_forall(concl th))) &&
       length(fst(strip_forall(concl th))) = 1
    then MAP_EVERY (fun r ->
           let thr = SPEC (mk_small_numeral r) th in
           let ante = lhand(concl thr) in
           ASSUME_TAC(MP thr (EQT_ELIM(NUM_REDUCE_CONV ante)))) rs
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* A used slot: its id below the count names a row; a row of the name's    *)
(* length whose bytes lie in the used arena is compared byte for byte.      *)
(* ------------------------------------------------------------------------- *)

(* The row's offset word as the generator reads it. *)
let name_roff_tm =
  subst [name_id_tm, `id:int64`]
    `tisa_read st (word_add (tisa_base st 1) (word (8 * val(word_shl (id:int64) 1)))) 8`;;

(* The comparison's verdict against the row's bytes and the name's. *)
let NAME_ROW_KEY_TAC =
  MP_TAC(ISPECL [`st:tisa_state`; mk_comb(`val:int64->num`, name_id_tm); name_roff_tm] NAME_ROW_KEY) THEN
  ASM_REWRITE_TAC[];;

(* A row that does not hold the name: another length, or another byte. *)
let NAME_ROW_DIFF_TAC =
  NAME_ROW_WORDS_TAC THEN
  ((REWRITE_TAC[name_row_bytes; name_key; region_range; NAME_LIST_OF_SEQ_EQ] THEN
    ASM_REWRITE_TAC[VAL_EQ] THEN NO_TAC) ORELSE
   (NAME_ROW_KEY_TAC THEN NO_TAC));;

(* Path conditions and loop facts in the generator's normal form. *)
let NAME_ASM_NORM_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE (TISA_COND01_EQ_0 :: ARITH_EQ :: MULT_CLAUSES ::
                               TISA_WORD_ADD_OFFSETS :: TISA_INSTR_REWRS));;

(* A probe that continues: the invariant one probe further; the slot was not *)
(* empty, and the row it names, if below the count, does not hold the name. *)
let NAME_CONT_LEAF_TAC =
  NAME_ASM_NORM_TAC THEN
  REWRITE_TAC[name_inv; GSYM NAME_SLOTS_VAL] THEN TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NAME_PROBED_STEP THEN ASM_REWRITE_TAC[name_probed; name_count] THEN
  NAME_ROW_DIFF_TAC;;

(* The row holds the name: FIRED with its id. *)
let NAME_FOUND_LEAF_TAC =
  NAME_ASM_NORM_TAC THEN TISA_STATE_NORM_TAC THEN NAME_ROW_WORDS_TAC THEN
  MATCH_MP_TAC NAME_FOUND_RESULT THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST [REWRITE_TAC[name_count] THEN TISA_WP_ARITH_TAC THEN NO_TAC;
         ASM_REWRITE_TAC[name_used] THEN TISA_ARITH_DECIDE_TAC THEN NO_TAC;
         NAME_ROW_KEY_TAC THEN NO_TAC];;

(* After the comparison loop: v9 says whether the bytes are the name's. *)
let NAME_CMP_DONE_TAC =
  X_GEN_TAC `s1:tisa_state` THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  NAME_REGS_TAC [1;3;4] THEN NAME_SAME_VIEW_TAC `s1:tisa_state` THEN
  BETA_TAC THEN TISA_VCG_TAC THEN
  (fun (asl,w) -> if fst(strip_comb w) = `name_inv` then NAME_CONT_LEAF_TAC (asl,w)
                  else NAME_FOUND_LEAF_TAC (asl,w));;

(* The comparison loop, by NAME_CMP_LOOP. *)
let NAME_CMP_LOOP_TAC =
  MATCH_MP_TAC NAME_CMP_LOOP THEN EXISTS_TAC `st:tisa_state` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  (fun (asl,w) -> if is_forall w then NAME_CMP_DONE_TAC (asl,w)
                  else if is_imp w then (DISCH_TAC THEN NAME_STOP_LEAF_TAC) (asl,w)
                  else NAME_SIDE_TAC (asl,w));;

let NAME_OCCUPIED_LEAF_TAC : tactic = fun (asl,w) ->
  let h,args = strip_comb w in
  if h = `name_inv` then NAME_CONT_LEAF_TAC (asl,w)
  else if h = `tisa_wp` then NAME_CMP_LOOP_TAC (asl,w)
  else NAME_STOP_LEAF_TAC (asl,w);;

let NAME_OCCUPIED_WP = prove
 (`!st N j s.
     name_regions st /\ name_entered st /\ j < N /\ N = val(name_slots st) /\
     tregs s 0 = tregs st 0 /\ tmem s = tmem st /\
     tregs s 1 = tregs st 1 /\ tregs s 3 = name_slots st /\
     tregs s 7 = name_slot st (name_pos st (tregs st 1) j) /\
     ~(name_slot st (name_pos st (tregs st 1) j) = word 0) /\
     (!x. x < j ==> name_probed st x)
     ==> tisa_wp name_occupied (name_inv st N (j + 1)) (name_result st) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N = val(name_slots st)`)) THEN
  NAME_BLOCK_SETUP_TAC `s:tisa_state` THEN
  REWRITE_TAC[name_occupied; name_row; name_compare] THEN TISA_VCG_TAC THEN
  NAME_OCCUPIED_LEAF_TAC);;

(* ------------------------------------------------------------------------- *)
(* An empty slot: room for a row and the bytes, the copy, the row, the slot, *)
(* and the publication. Its FIRED stop has the appended view: each part is  *)
(* read through the finish, the stores and the copy (NAME_APPEND_RESULT).    *)
(* ------------------------------------------------------------------------- *)

let NAME_VIEWS = [name_count; name_used; name_slots; name_word; name_slot; region_byte];;

(* A view of the appended state against the entry state's. *)
let NAME_APP_VIEW_TAC =
  REWRITE_TAC NAME_VIEWS THEN REPEAT STRIP_TAC THEN TISA_STATE_NORM_TAC THEN
  TRY TISA_ARITH_DECIDE_TAC;;

(* The slots: the name's probe holds count + 1, the others are unchanged. *)
let NAME_APP_SLOT_TAC =
  REWRITE_TAC NAME_VIEWS THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `p = name_pos st (tregs st 1) j`)) THEN
    TISA_STATE_NORM_TAC THEN REWRITE_TAC[TISA_WORD_ADD_VAL];
    FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[GSYM VAL_EQ] o
                  check (fun th -> concl th = `~(p = name_pos st (tregs st 1) j)`)) THEN
    TISA_STATE_NORM_TAC];;

(* A byte inside the copy: the name's byte. *)
let NAME_BWRITE_BYTE_TAC =
  W(fun (asl,w) ->
    let t = find_term (fun t -> let h,args = strip_comb t in
                         h = `tisa_read:tisa_state->int64->num->int64` && length args = 3 &&
                         fst(strip_comb (hd args)) = `tisa_bwrite`) w in
    let _,targs = strip_comb t in
    let _,sargs = strip_comb (hd targs) in
    let a = hd sargs and b = el 1 targs in
    MP_TAC(ISPECL (sargs @ [b]) TISA_READ_BWRITE_BYTE) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN TISA_ARITH_DECIDE_TAC; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN (mk_eq(mk_binop `(-):num->num->num` (mk_comb(`val:int64->num`, b))
                                 (mk_comb(`val:int64->num`, a)), `k:num`))
      SUBST1_TAC THENL [TISA_ARITH_DECIDE_TAC; ALL_TAC]) THEN
  ASM_REWRITE_TAC[LIMB_READ_BYTES; tisa_read; READ_BYTES_1; MULT_CLAUSES; TISA_WORD_ADD_OFFSETS];;

let NAME_APP_BYTES_TAC =
  REWRITE_TAC NAME_VIEWS THEN REPEAT STRIP_TAC THEN TISA_STATE_NORM_TAC THEN
  NAME_BWRITE_BYTE_TAC;;

let NAME_APP_OBLIGATION_TAC : tactic = fun (asl,w) ->
  if is_forall w && can (find_term ((=) `name_slot`)) w then NAME_APP_SLOT_TAC (asl,w)
  else if is_forall w && can (find_term ((=) `region_byte st 0`)) w then NAME_APP_BYTES_TAC (asl,w)
  else NAME_APP_VIEW_TAC (asl,w);;

(* The FIRED stop after the copy. *)
let NAME_APP_FIRED_TAC =
  W(fun (asl,w) -> MP_TAC(SPECL [`st:tisa_state`; rand w; `j:num`] NAME_APPEND_RESULT)) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[name_appended] THEN REPEAT CONJ_TAC THEN NAME_APP_OBLIGATION_TAC;;

(* After the copy loop: a byte-range write over a state with the entry     *)
(* state's memory; the row, the slot and the header words follow.          *)
let NAME_COPY_DONE_TAC =
  X_GEN_TAC `s1:tisa_state` THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  NAME_REGS_TAC [5;6;10] THEN NAME_SAME_VIEW_TAC `s1:tisa_state` THEN
  BETA_TAC THEN TISA_VCG_TAC THEN NAME_APP_FIRED_TAC;;

(* The copy loop, by NAME_COPY_LOOP. *)
let NAME_COPY_LOOP_TAC =
  MATCH_MP_TAC NAME_COPY_LOOP THEN EXISTS_TAC `st:tisa_state` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  (fun (asl,w) -> if is_forall w then NAME_COPY_DONE_TAC (asl,w)
                  else if is_imp w then (DISCH_TAC THEN NAME_STOP_LEAF_TAC) (asl,w)
                  else NAME_SIDE_TAC (asl,w));;

let NAME_APPEND_LEAF_TAC : tactic = fun (asl,w) ->
  if fst(strip_comb w) = `tisa_wp` then NAME_COPY_LOOP_TAC (asl,w) else NAME_STOP_LEAF_TAC (asl,w);;

let NAME_APPEND_WP = prove
 (`!st N j s Q.
     name_regions st /\ name_entered st /\ j < N /\ N = val(name_slots st) /\
     tregs s 0 = tregs st 0 /\ tmem s = tmem st /\ tregs s 1 = tregs st 1 /\
     tregs s 6 = word_add (tisa_base st 3) (word (8 * val(name_pos st (tregs st 1) j))) /\
     name_slot st (name_pos st (tregs st 1) j) = word 0 /\
     (!x. x < j ==> name_probed st x)
     ==> tisa_wp name_append Q (name_result st) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N = val(name_slots st)`)) THEN
  NAME_BLOCK_SETUP_TAC `s:tisa_state` THEN
  MP_TAC(SPECL [`st:tisa_state`; `tregs st 1`; `j:num`] NAME_POS_LT) THEN
  ANTS_TAC THENL [TISA_WP_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[name_append; name_append_room] THEN TISA_VCG_TAC THEN
  NAME_APPEND_LEAF_TAC);;

(* ------------------------------------------------------------------------- *)
(* One probe: the slot at (hash + j) and (slots - 1); an empty slot appends, *)
(* a used one is checked.                                                    *)
(* ------------------------------------------------------------------------- *)

let NAME_BLOCK_HYPS_TAC =
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[name_slot; name_pos] THEN NO_TAC);;

let NAME_BODY_WP = prove
 (`!st N j s0.
     name_regions st /\ j < N /\ name_inv st N j s0
     ==> tisa_wp name_body (name_inv st N (j + 1)) (name_result st) (tisa_setreg 2 (word j) s0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [name_inv] o
              check (fun th -> tisa_has_tm `name_inv` th)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N = val(name_slots st)`)) THEN
  NAME_BLOCK_SETUP_TAC `s0:tisa_state` THEN
  SUBGOAL_THEN `val(word j:int64) = j` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN MP_TAC(ISPEC `name_slots st` VAL_BOUND_64) THEN
    TISA_WP_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[name_body] THEN TISA_VCG_TAC THEN
  (fun (asl,w) ->
     if can (find_term ((=) `name_append`)) w then
       (MATCH_MP_TAC NAME_APPEND_WP THEN MAP_EVERY EXISTS_TAC [`val(name_slots st)`; `j:num`] THEN
        NAME_BLOCK_HYPS_TAC) (asl,w)
     else (MATCH_MP_TAC NAME_OCCUPIED_WP THEN NAME_BLOCK_HYPS_TAC) (asl,w)));;

(* ------------------------------------------------------------------------- *)
(* The prologue: a name outside the input is refused, a header word above  *)
(* its region is UNSUPPORTED; otherwise the invariant before probe 0.        *)
(* ------------------------------------------------------------------------- *)

let NAME_PROLOGUE_WP = prove
 (`!st. name_regions st
        ==> tisa_wp name_prologue (\s. name_inv st (val(name_slots st)) 0 s)
                    (name_result st) st`,
  GEN_TAC THEN DISCH_TAC THEN NAME_REGIONS_TAC THEN
  REWRITE_TAC[name_prologue] THEN TISA_VCG_TAC THEN
  (fun (asl,w) ->
     if fst(strip_comb w) = `name_inv` then
       (REWRITE_TAC[name_inv; name_entered; name_count; name_used; name_slots; LT] THEN
        TISA_STATE_NORM_TAC THEN REPEAT CONJ_TAC THEN TISA_ARITH_DECIDE_TAC) (asl,w)
     else
       (MATCH_MP_TAC NAME_EARLY_STOP_RESULT THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
        REPEAT CONJ_TAC THEN TRY(TISA_STATE_NORM_TAC THEN NO_TAC) THEN
        TISA_ARITH_DECIDE_TAC) (asl,w)));;

(* ------------------------------------------------------------------------- *)
(* The whole program: every run that stops ends with name_result; no run    *)
(* continues past the final RETURN.                                          *)
(* ------------------------------------------------------------------------- *)

let NAME_ROOT_WP = prove
 (`!st. tisa_entry_ok intern_name st
        ==> tisa_wp (tisa_root intern_name) (\s. F) (name_result st) st`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NAME_ENTRY) THEN
  REWRITE_TAC[intern_name; tisa_root; TISA_WP_SEQ] THEN
  MATCH_MP_TAC TISA_WP_MONO THEN
  EXISTS_TAC `\s. name_inv st (val(name_slots st)) 0 s` THEN
  EXISTS_TAC `name_result st` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC NAME_PROLOGUE_WP THEN ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `s:tisa_state` THEN DISCH_TAC THEN
  MATCH_MP_TAC TISA_WP_COUNT_LOOP THEN EXISTS_TAC `name_inv st` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [name_inv]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* more slots than the loop's cap *)
    DISCH_TAC THEN NAME_STOP_LEAF_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NAME_BODY_WP THEN ASM_REWRITE_TAC[];
    (* every slot probed: UNSUPPORTED *)
    MAP_EVERY X_GEN_TAC [`N:num`; `s1:tisa_state`] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [name_inv]) THEN
    TISA_VCG_TAC THEN NAME_STOP_LEAF_TAC]);;

let NAME_RUN = prove
 (`!st k st'. tisa_entry_ok intern_name st /\ tisa_run intern_name st = TStop k st'
              ==> name_result st k st'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `st:tisa_state` NAME_ROOT_WP) THEN ASM_REWRITE_TAC[tisa_wp] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> tisa_has_tm `tisa_run` th)) THEN
  ASM_REWRITE_TAC[tisa_run] THEN
  MP_TAC(ISPEC `tisa_exec (tisa_root intern_name) st` TISA_RESULT_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:tisa_state` SUBST1_TAC)
     (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `a:tisa_state` SUBST1_TAC))) THEN
  REWRITE_TAC[tisa_then; TISA_RWP_CONT; TISA_RWP_STOP; TISA_RESULT_INJ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Soundness, completeness, canonicity.                                      *)
(* ------------------------------------------------------------------------- *)

(* Soundness, whatever the table and the hash: a FIRED run's row holds the   *)
(* name inside the used arena; rows and arena bytes below the old counts are *)
(* unchanged.                                                                *)
let NAME_SOUND = prove
 (`!st st'. tisa_entry_ok intern_name st /\ tisa_run intern_name st = TStop 1 st'
            ==> name_post st st'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `1`; `st':tisa_state`] NAME_RUN) THEN
  ASM_SIMP_TAC[name_result]);;

(* The invariant is kept by every outcome when the hash is the name's. *)
let NAME_RUN_COMPLETE = prove
 (`!st k st'. tisa_entry_ok intern_name st /\ name_ok st /\ name_hash_ok st /\
              tisa_run intern_name st = TStop k st'
              ==> name_ok st' /\ (k = 1 ==> name_post st st')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `k:num`; `st':tisa_state`] NAME_RUN) THEN
  ASM_SIMP_TAC[name_result]);;

(* A run that appended found no row holding the name. *)
let NAME_APPEND_ABSENT = prove
 (`!st st'. tisa_entry_ok intern_name st /\ name_ok st /\ name_hash_ok st /\
            tisa_run intern_name st = TStop 1 st' /\
            val(tisa_fword st' 19) = val(name_count st)
            ==> !i. i < val(name_count st) ==> ~(name_row_bytes st i = name_key st)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `1`; `st':tisa_state`] NAME_RUN_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[name_ok; name_distinct; name_post] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  X_GEN_TAC `i:num` THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `val(name_count st)`] o
    check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN
  TRY(FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `val(tisa_fword st' 19) < val(name_count st')`)) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `name_row_bytes st' i = name_row_bytes st i` SUBST1_TAC THENL
   [MATCH_MP_TAC NAME_ROW_BYTES_TRANSFER THEN EXISTS_TAC `val(name_used st)` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[name_ok]) THEN ASM_SIMP_TAC[] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `val(tisa_fword st' 19) = val(name_count st)`)) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* Equal names get equal ids: a name held by a row is answered with that row. *)
let NAME_PRESENT_FOUND = prove
 (`!st st' i. tisa_entry_ok intern_name st /\ name_ok st /\ name_hash_ok st /\
              i < val(name_count st) /\ name_row_bytes st i = name_key st /\
              tisa_run intern_name st = TStop 1 st'
              ==> val(tisa_fword st' 19) = i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `1`; `st':tisa_state`] NAME_RUN_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[name_post] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [(* found: its row in st holds the name, so it is row i *)
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[name_ok] o check (fun th -> concl th = `name_ok st`)) THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[name_distinct] o check (fun th -> concl th = `name_distinct st`)) THEN
    DISCH_THEN(MP_TAC o SPECL [`val(tisa_fword st' 19)`; `i:num`]) THEN
    SUBGOAL_THEN `val(tisa_fword st' 19) < val(name_count st)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN `name_row_bytes st' (val(tisa_fword st' 19)) = name_row_bytes st (val(tisa_fword st' 19))`
     (fun th -> ASM_MESON_TAC[th]) THEN
    MATCH_MP_TAC NAME_ROW_BYTES_TRANSFER THEN EXISTS_TAC `val(name_used st)` THEN
    ASM_SIMP_TAC[] THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    (* appended: then no row held the name, but row i does *)
    MP_TAC(SPECL [`st:tisa_state`; `st':tisa_state`] NAME_APPEND_ABSENT) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

tisa_arith_focus := name_saved_arith_focus;;

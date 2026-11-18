(* ========================================================================= *)
(* Plans over tables given by an interface, for any abstract state. The     *)
(* interface names, by the slots a step binds:                               *)
(*   trow j s i        row i of the rows at slot j, a list of words;        *)
(*   tn c s            the count held at slot c;                             *)
(*   twd j             the width of the rows at slot j;                      *)
(*   tdrop jm s i      row i dropped, by the marks at slot jm;               *)
(*   tapp j c s r s'   s' is s with row r appended to the rows at slot j,   *)
(*                     whose count is at slot c;                             *)
(*   tput j c s i w v s'  s' is s with word w of row i of the table at slot *)
(*                     j (its rows counted at c) set to v.                   *)
(* A fixed table's rows have its width; a names table's rows are byte       *)
(* strings of any length. A leaf's meaning (tab_leaf) reads and writes     *)
(* every table through the interface, and the run's input inp (the bytes   *)
(* the input region holds, constant through a run), so one meaning serves *)
(* every table of every rule table; a run (tab_run) is pl_run's.           *)
(* Interning finds the row equal to the key and otherwise appends it:     *)
(* intern16's key is its two words, intern_name's the input's bytes it     *)
(* names. Appending checks the width.                                       *)
(*                                                                           *)
(* A leaf's meaning may have a domain: append_row writes rows of v1 words,   *)
(* and put_word words of rows of v1 words, so their meanings hold only when *)
(* v1 is the table's width; intern_name                                      *)
(* keeps its hash table's invariant only when v1 is the name's FNV-1a, so   *)
(* inside the input its meaning holds only then. A plan is safe from a     *)
(* state (tab_safe) when every leaf a run of it reaches is enabled there;   *)
(* the other leaves' meanings are total, so they are always enabled.       *)
(*                                                                           *)
(* Loaded after plans_abs.ml.                                                *)
(* ========================================================================= *)

let tab_intern = new_definition
 `tab_intern (trow:num->S->num->num list) (tn:num->S->num)
             (tapp:num->num->S->num list->S->bool) j c (s:S) (key:num list) k pay (s':S) <=>
    (k = 1 /\ pay < 2 EXP 60 /\
     (pay < tn c s /\ trow j s pay = key /\ s' = s \/
      pay = tn c s /\ (!i. i < tn c s ==> ~(trow j s i = key)) /\
      tn c s + 1 < 2 EXP 60 /\ tapp j c s key s')) \/
    (~(k = 0) /\ ~(k = 1) /\ s' = s)`;;

(* Appending writes a row of w words: its domain is the table's width. *)
let tab_append = new_definition
 `tab_append (tn:num->S->num) (twd:num->num) (tapp:num->num->S->num list->S->bool)
             j c (s:S) w (r:num list) k pay (s':S) <=>
    w = twd j /\
    ((k = 1 /\ tn c s + 1 < 2 EXP 60 /\ pay = tn c s /\ tapp j c s r s') \/
     (k = 2 /\ s' = s))`;;

let tab_live = new_definition
 `tab_live (tn:num->S->num) (tdrop:num->S->num->bool) c jm (s:S) i k (pay:num) <=>
    if i < tn c s /\ ~tdrop jm s i then k = 1 /\ pay = i else k = 0`;;

(* The row an append step writes: its first w of arg0, arg1, v2, v3, v4. *)
let tab_row = new_definition
 `tab_row (cw:num->num) (st:int64 list) w =
    list_of_seq (\i. EL i [cw(val(EL 10 st)); cw(val(EL 11 st)); cw(val(EL 13 st));
                          cw(val(EL 14 st)); cw(val(EL 15 st))]) w`;;

(* The input's bytes from a0, a1 of them. *)
let tab_key = new_definition
 `tab_key (inp:num list) a0 a1 = list_of_seq (\i. EL (a0 + i) inp) a1`;;

(* fnv: FIRED with the FNV-1a of the input's bytes from a0, a1 of them, from *)
(* the state v1, when they lie in the input; REFUSED when they do not;       *)
(* UNSUPPORTED past the loop's cap (pl_fnv_spec).                            *)
let tab_fnv = new_definition
 `tab_fnv (inp:num list) a0 a1 v1 k (pay:num) <=>
    if a0 + a1 <= LENGTH inp
    then k = 1 /\ pay = val(fnv1a (word v1) (tab_key inp a0 a1)) \/ k = 2 /\ 4294967295 < a1
    else k = 0`;;

(* intern_name: the input's bytes from a0, a1 of them, interned in the       *)
(* names table at slot j counted at c, given v1 their FNV-1a; REFUSED       *)
(* exactly when they lie outside the input.                                  *)
let tab_name = new_definition
 `tab_name (trow:num->S->num->num list) (tn:num->S->num) (tapp:num->num->S->num list->S->bool)
           j c (inp:num list) a0 a1 v1 (s:S) k pay (s':S) <=>
    if a0 + a1 <= LENGTH inp
    then v1 = val(fnv1a fnv_offset (tab_key inp a0 a1)) /\
         tab_intern trow tn tapp j c s (tab_key inp a0 a1) k pay s'
    else k = 0 /\ s' = s`;;

(* put_word: word w of row i := v, the rows of v1 words at slot j counted at *)
(* c; FIRED with payload v inside the table, UNSUPPORTED (the state kept)  *)
(* exactly when the row or word lies outside the represented table.          *)
let tab_putw = new_definition
 `tab_putw (tn:num->S->num) (twd:num->num) (tput:num->num->S->num->num->num->S->bool)
           j c (s:S) v1 i w v k pay (s':S) <=>
    v1 = twd j /\
    (i < tn c s /\ w < v1 /\ k = 1 /\ pay = v /\ tput j c s i w v s' \/
     ~(i < tn c s /\ w < v1) /\ k = 2 /\ s' = s)`;;

let tab_put_mark_ok = new_definition
 `tab_put_mark_ok ((trow,tn,twd,tdrop,tapp,tput):(num->S->num->num list)#(num->S->num)#(num->num)#
                                                 (num->S->num->bool)#(num->num->S->num list->S->bool)#
                                                 (num->num->S->num->num->num->S->bool)) jm c <=>
    (!s i v. i < tn c s ==> ?s'. tput jm c s i 0 v s') /\
    (!s i v s'. tput jm c s i 0 v s'
                ==> (!i'. tdrop jm s' i' <=> if i' = i then ~(v = 0) else tdrop jm s i') /\
                    (!j'. trow j' s' = trow j' s) /\ (!c'. tn c' s' = tn c' s) /\
                    (!jm'. ~(jm' = jm) ==> tdrop jm' s' = tdrop jm' s))`;;

(* pol_max: REFUSED unless p <= 2; payload MAX pol p. *)
let tab_polmax = new_definition
 `tab_polmax pol p k (pay:num) <=> if p <= 2 then k = 1 /\ pay = MAX pol p else k = 0`;;

(* The leaves: 0 intern16 (rows, slots, count), 1 pack, 2 unpack, 3 eqw,     *)
(* 4 row_word (rows, count), 5 live (count, marks), 6 append_row (rows,      *)
(* count), 9 put_word (table, count), 20 pol_max, 22 fnv (input),           *)
(* 23 intern_name (input, rows, arena, table, header: the count).            *)
let tab_leaf = new_definition
 `tab_leaf ((trow,tn,twd,tdrop,tapp,tput):(num->S->num->num list)#(num->S->num)#(num->num)#
                                      (num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool))
           (inp:num list) (st:int64 list) ((cw,s,stk):(num->num)#S#num list) k (pay:num) (s':S) <=>
    let a0 = cw(val(EL 10 st)) and a1 = cw(val(EL 11 st)) and v1 = cw(val(EL 12 st)) in
    (val(EL 0 st) = 0 /\ tab_intern trow tn tapp (val(EL 1 st)) (val(EL 3 st)) s [a0; a1] k pay s') \/
    (val(EL 0 st) = 1 /\ pl_pack a0 a1 k pay /\ s' = s) \/
    (val(EL 0 st) = 2 /\ pl_unpack a0 a1 k pay /\ s' = s) \/
    (val(EL 0 st) = 3 /\ pl_eqw a0 a1 k pay /\ s' = s) \/
    (val(EL 0 st) = 4 /\
     pl_roww (\i w. EL w (trow (val(EL 1 st)) s i)) (tn (val(EL 2 st)) s) (twd (val(EL 1 st)))
             a0 a1 v1 k pay /\ s' = s) \/
    (val(EL 0 st) = 5 /\ tab_live tn tdrop (val(EL 1 st)) (val(EL 2 st)) s a0 k pay /\ s' = s) \/
    (val(EL 0 st) = 6 /\
     tab_append tn twd tapp (val(EL 1 st)) (val(EL 2 st)) s v1 (tab_row cw st v1) k pay s') \/
    (val(EL 0 st) = 9 /\
     tab_putw tn twd tput (val(EL 1 st)) (val(EL 2 st)) s v1 a0 (cw(val(EL 13 st))) a1 k pay s') \/
    (val(EL 0 st) = 20 /\ tab_polmax a0 a1 k pay /\ s' = s) \/
    (val(EL 0 st) = 22 /\ tab_fnv inp a0 a1 v1 k pay /\ s' = s) \/
    (val(EL 0 st) = 23 /\ tab_name trow tn tapp (val(EL 2 st)) (val(EL 5 st)) inp a0 a1 v1 s k pay s')`;;

(* A run of the steps from index i: (outcome, index of the step that ended  *)
(* the plan, final state), as pl_run.                                        *)
let tab_run = define
 `(tab_run (tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
              (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)) (inp:num list) [] i (s:(num->num)#S#num list) r <=>
     r = (1,i,s)) /\
  (tab_run tb inp (CONS st sts) i s r <=>
     ?k pay s'. tab_leaf tb inp st s k pay s' /\
                (if k = 1 then tab_run tb inp sts (i + 1) (pl_set (FST s) (val(EL 17 st)) pay,s',SND(SND s)) r
                 else r = (k,i,(pl_set (FST s) (val(EL 17 st)) pay,s',SND(SND s)))))`;;

(* Every leaf a run of the steps reaches is enabled there. *)
let tab_safe = define
 `(tab_safe (tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
               (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)) (inp:num list) [] (s:(num->num)#S#num list) <=> T) /\
  (tab_safe tb inp (CONS st sts) s <=>
     (?k pay s'. tab_leaf tb inp st s k pay s') /\
     !k pay s'. tab_leaf tb inp st s k pay s' /\ k = 1
                ==> tab_safe tb inp sts (pl_set (FST s) (val(EL 17 st)) pay,s',SND(SND s)))`;;
